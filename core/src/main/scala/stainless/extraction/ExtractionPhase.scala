/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.collection.mutable.{Map => MutableMap}

trait ExtractionPhase extends inox.ast.SymbolTransformer { self =>
  val s: extraction.Trees
  val t: ast.Trees

  implicit val context: inox.Context
  protected implicit def printerOpts: s.PrinterOptions = s.PrinterOptions.fromContext(context)


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
  protected class CacheKey private(private val id: Identifier, private val dependencies: Set[Dependency]) {
    override val hashCode: Int = (id, dependencies).hashCode
    override def equals(that: Any): Boolean = that match {
      case ck: CacheKey => id == ck.id && dependencies == ck.dependencies
      case _ => false
    }
  }

  protected object CacheKey {
    private def apply(id: Identifier)(implicit symbols: s.Symbols): CacheKey = {
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
      })
    }

    def apply(d: s.Definition)(implicit symbols: s.Symbols): CacheKey = apply(d.id)
  }

  protected class ExtractionCache[+Key <: s.Definition, T] {
    private[this] final val cache: MutableMap[CacheKey, T] = MutableMap.empty

    def cached(key: Key, symbols: s.Symbols)(builder: => T): T = {
      cache.getOrElseUpdate(CacheKey(key)(symbols), builder)
    }

    def contains(key: Key, symbols: s.Symbols): Boolean = cache contains CacheKey(key)(symbols)
    def update(key: Key, symbols: s.Symbols, value: T) = cache.update(CacheKey(key)(symbols), value)
    def get(key: Key, symbols: s.Symbols): Option[T] = cache.get(CacheKey(key)(symbols))
    def apply(key: Key, symbols: s.Symbols): T = cache(CacheKey(key)(symbols))
  }
}

trait CachingPhase extends ExtractionPhase { self =>
  protected type FunctionResult
  private[this] final val funCache = new ExtractionCache[s.FunDef, FunctionResult]

  protected type SortResult
  private[this] final val sortCache = new ExtractionCache[s.ADTSort, SortResult]

  protected type TransformerContext
  protected def getContext(symbols: s.Symbols): TransformerContext

  protected def transformFunction(context: TransformerContext, fd: s.FunDef): FunctionResult
  protected def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols

  protected def transformSort(context: TransformerContext, sort: s.ADTSort): SortResult
  protected def registerSorts(symbols: t.Symbols, sorts: Seq[SortResult]): t.Symbols

  override final def transform(symbols: s.Symbols): t.Symbols = {
    val context = getContext(symbols)
    transformSymbols(context, symbols)
  }

  protected def transformSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val functions = symbols.functions.values.map { fd =>
      funCache.cached(fd, symbols)(transformFunction(context, fd))
    }.toSeq

    val sorts = symbols.sorts.values.map { sort =>
      sortCache.cached(sort, symbols)(transformSort(context, sort))
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

  override protected def transformSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = identity.transform(sort)
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

  override protected def transformFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = identity.transform(fd)
}

trait SimplePhase extends ExtractionPhase with SimpleSorts with SimpleFunctions { self =>
  override protected type TransformerContext <: ast.TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def transformFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def transformSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)
}
