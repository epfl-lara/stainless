/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction

import transformers._

trait ExtractionPipeline { self =>
  val s: ast.Trees
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
  def apply(transformer: DefinitionTransformer { val s: Trees; val t: ast.Trees })
           (implicit ctx: inox.Context): ExtractionPipeline {
    val s: transformer.s.type
    val t: transformer.t.type
  } = new ExtractionPipeline { self =>
    override val s: transformer.s.type = transformer.s
    override val t: transformer.t.type = transformer.t
    override val context = ctx

    override def extract(symbols: s.Symbols): t.Symbols =
      symbols.transform(transformer.asInstanceOf[DefinitionTransformer {
        val s: self.s.type
        val t: self.t.type
      }])

    override def invalidate(id: Identifier): Unit = ()
  }

  def apply(transformer: inox.transformers.SymbolTransformer { val s: Trees; val t: ast.Trees })
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

trait ExtractionContext extends ExtractionPipeline {
  protected type TransformerContext
  protected def getContext(symbols: s.Symbols): TransformerContext
}

trait CachingPhase extends ExtractionContext with ExtractionCaches { self =>
  protected type FunctionResult
  protected val funCache: ExtractionCache[s.FunDef, FunctionResult]

  protected type SortResult
  protected val sortCache: ExtractionCache[s.ADTSort, SortResult]

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
      funCache.cached(fd, context)(extractFunction(context, fd))
    }.toSeq

    val sorts = symbols.sorts.values.map { sort =>
      sortCache.cached(sort, context)(extractSort(context, sort))
    }.toSeq

    registerSorts(registerFunctions(t.NoSymbols, functions), sorts)
  }
}

trait SimpleSorts extends CachingPhase {
  override protected type SortResult = t.ADTSort
  override protected def registerSorts(symbols: t.Symbols, sorts: Seq[t.ADTSort]): t.Symbols = symbols.withSorts(sorts)
}

trait SimplyCachedSorts extends CachingPhase {
  override protected final val sortCache: ExtractionCache[s.ADTSort, SortResult] = new SimpleCache[s.ADTSort, SortResult]
}

trait IdentitySorts extends SimpleSorts with SimplyCachedSorts { self =>
  private[this] final object identity extends TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = identity.transform(sort)
}

trait SimpleFunctions extends CachingPhase {
  override protected type FunctionResult = t.FunDef
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[t.FunDef]): t.Symbols = symbols.withFunctions(functions)
}

trait SimplyCachedFunctions extends CachingPhase {
  override protected final val funCache: ExtractionCache[s.FunDef, FunctionResult] = new SimpleCache[s.FunDef, FunctionResult]
}

trait IdentityFunctions extends SimpleFunctions with SimplyCachedFunctions { self =>
  private[this] final object identity extends TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = identity.transform(fd)
}

trait SimplePhase extends ExtractionPipeline with SimpleSorts with SimpleFunctions { self =>
  override protected type TransformerContext <: TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)
}
