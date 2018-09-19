/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

trait ExtractionPipeline { self =>
  val s: extraction.Trees
  val t: ast.Trees

  implicit val context: inox.Context
  protected implicit def printerOpts: s.PrinterOptions = s.PrinterOptions.fromContext(context)

  def extract(symbols: s.Symbols): t.Symbols

  def invalidate(id: Identifier): Unit

  def andThen(that: ExtractionPipeline { val s: self.t.type }): ExtractionPipeline {
    val s: self.s.type
    val t: that.t.type
  } = new ExtractionPipeline {
    override val s: self.s.type = self.s
    override val t: that.t.type = that.t
    override val context = self.context

    override def extract(symbols: s.Symbols): t.Symbols = {
      that.extract(self.extract(symbols))
    }

    override def invalidate(id: Identifier): Unit = {
      self.invalidate(id)
      that.invalidate(id)
    }
  }
}

object ExtractionPipeline {
  def apply(transformer: ast.TreeTransformer { val s: Trees; val t: ast.Trees })
           (implicit ctx: inox.Context): ExtractionPipeline {
    val s: transformer.s.type
    val t: transformer.t.type
  } = new ExtractionPipeline { self =>
    override val s: transformer.s.type = transformer.s
    override val t: transformer.t.type = transformer.t
    override val context = ctx

    override def extract(symbols: s.Symbols): t.Symbols =
      symbols.transform(transformer.asInstanceOf[ast.TreeTransformer {
        val s: self.s.type
        val t: self.t.type
      }])

    override def invalidate(id: Identifier): Unit = ()
  }

  def apply(transformer: inox.ast.SymbolTransformer { val s: Trees; val t: ast.Trees })
           (implicit ctx: inox.Context): ExtractionPipeline {
    val s: transformer.s.type
    val t: transformer.t.type
  } = new ExtractionPipeline {
    override val s: transformer.s.type = transformer.s
    override val t: transformer.t.type = transformer.t
    override val context = ctx

    override def extract(symbols: s.Symbols): t.Symbols = transformer.transform(symbols)
    override def invalidate(id: Identifier): Unit = ()
  }
}

trait ExtractionCaches { self: ExtractionPipeline =>
  /** Represents a definition dependency with some identifier `id`.
    * Such a dependency can be either a
    * - function definition
    * - class definition
    * - sort definition
    * These dependencies represent transformation results that can't be cached based
    * solely on their identifier (e.g. subtyping functions). Such functions are marked
    * as `Uncached` and MUST be part of the dependencies of all functions that rely on
    * them in order for caching to be sound.
    */
  private final class Dependency(val id: Identifier, val key: AnyRef) {
    override val hashCode: Int = key.hashCode
    override def equals(that: Any): Boolean = that match {
      case dep: Dependency => key == dep.key
      case _ => false
    }
  }

  /** Represents a cache key with all it's `Uncached` dependencies. */
  protected class CacheKey private(
    private[ExtractionCaches] val id: Identifier,
    private[ExtractionCaches] val keys: Set[Dependency],
    private[ExtractionCaches] val dependencies: Set[Identifier]) {

    override val hashCode: Int = (id, keys).hashCode
    override def equals(that: Any): Boolean = that match {
      case ck: CacheKey => id == ck.id && keys == ck.keys
      case _ => false
    }
  }

  protected object CacheKey {
    def apply(id: Identifier)(implicit symbols: s.Symbols): CacheKey = {
      new CacheKey(id, symbols.dependencies(id).flatMap { did =>
        val optKey = symbols.lookupFunction(id).map { fd =>
          if (fd.flags contains s.Uncached) {
            Some((fd.id, fd.typeArgs, fd.params.map(_.toVariable), fd.returnType, fd.fullBody, fd.flags))
          } else {
            None
          }
        } orElse symbols.lookupSort(id).map { sort =>
          if (sort.flags contains s.Uncached) {
            Some((sort.id, sort.typeArgs, sort.constructors.map { cons =>
              (cons.id, cons.sort, cons.fields.map(_.toVariable))
            }, sort.flags))
          } else {
            None
          }
        } orElse {
          if (s.isInstanceOf[oo.Trees]) {
            val oos = s.asInstanceOf[oo.Trees]
            symbols.asInstanceOf[oos.Symbols].lookupClass(id).map { cd =>
              if (cd.flags contains oos.Uncached) {
                Some((cd.id, cd.typeArgs, cd.parents, cd.fields.map(_.toVariable), cd.flags))
              } else {
                None
              }
            }
          } else {
            None
          }
        } getOrElse (throw inox.FatalError(s"Unexpected dependency in ${id.asString}: ${did.asString}"))

        optKey.map(new Dependency(did, _))
      }, symbols.dependencies(id))
    }

    def apply(d: s.Definition)(implicit symbols: s.Symbols): CacheKey = apply(d.id)
  }

  private[this] val caches = new scala.collection.mutable.ListBuffer[ExtractionCache[_, _, _]]

  protected class ExtractionCache[Key, X <: s.Definition, Y](keyOf: (X, s.Symbols) => Key) {
    private[this] final val cache = new utils.ConcurrentCache[(X, Key), Y]

    def cached(id: X, symbols: s.Symbols)(builder: => Y): Y = cache.cached(id -> keyOf(id, symbols))(builder)

    def contains(id: X, symbols: s.Symbols): Boolean = cache contains (id -> keyOf(id, symbols))
    def update(id: X, symbols: s.Symbols, value: Y) = cache.update(id -> keyOf(id, symbols), value)
    def get(id: X, symbols: s.Symbols): Option[Y] = cache.get(id -> keyOf(id, symbols))
    def apply(id: X, symbols: s.Symbols): Y = cache(id -> keyOf(id, symbols))

    private[ExtractionCaches] def invalidate(id: Identifier): Unit =
      cache.retain(key => key._1.id != id)
      // FIXME: key._1.dependencies is not accepted by the compiler
      // cache.retain(key => key._1.id != id && !(key._1.dependencies contains id)) 

    self.synchronized(caches += this)
  }

  object ExtractionCache {
    def apply[X <: s.Definition, Y]() = {
      new ExtractionCache[CacheKey, X, Y]((x, sym) => CacheKey(x)(sym))
    }
  }

  override def invalidate(id: Identifier): Unit = {
    for (cache <- caches) cache.invalidate(id)
  }
}

trait CachingPhase extends ExtractionPipeline with ExtractionCaches { self =>
  protected type FunctionResult
  private[this] final val funCache = ExtractionCache[s.FunDef, FunctionResult]()

  protected type SortResult
  private[this] final val sortCache = ExtractionCache[s.ADTSort, SortResult]()

  protected type TransformerContext
  protected def getContext(symbols: s.Symbols): TransformerContext

  protected def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult
  protected def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols

  protected def extractSort(context: TransformerContext, sort: s.ADTSort): SortResult
  protected def registerSorts(symbols: t.Symbols, sorts: Seq[SortResult]): t.Symbols

  override final def extract(symbols: s.Symbols): t.Symbols = {
    val context = getContext(symbols)
    extractSymbols(context, symbols)
  }

  protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val functions = symbols.functions.values.map { fd =>
      funCache.cached(fd, symbols)(extractFunction(context, fd))
    }.toSeq

    val sorts = symbols.sorts.values.map { sort =>
      sortCache.cached(sort, symbols)(extractSort(context, sort))
    }.toSeq

    registerSorts(registerFunctions(t.NoSymbols, functions), sorts)
  }
}

trait SimpleSorts extends CachingPhase {
  override protected type SortResult = t.ADTSort
  override protected def registerSorts(symbols: t.Symbols, sorts: Seq[t.ADTSort]): t.Symbols = symbols.withSorts(sorts)
}

trait IdentitySorts extends SimpleSorts { self =>
  private[this] final object identity extends ast.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = identity.transform(sort)
}

trait SimpleFunctions extends CachingPhase {
  override protected type FunctionResult = t.FunDef
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[t.FunDef]): t.Symbols = symbols.withFunctions(functions)
}

trait IdentityFunctions extends SimpleFunctions { self =>
  private[this] final object identity extends ast.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = identity.transform(fd)
}

trait SimplePhase extends ExtractionPipeline with SimpleSorts with SimpleFunctions { self =>
  override protected type TransformerContext <: ast.TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)
}
