/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

import transformers._

trait ExtractionPipeline { self =>
  val s: ast.Trees
  val t: ast.Trees
  val context: inox.Context

  import context.given

  protected val printerOpts: s.PrinterOptions = s.PrinterOptions.fromContext(context)
  given givenPipelinePrinterOpts: printerOpts.type = printerOpts

  def extract(symbols: s.Symbols): t.Symbols

  def invalidate(id: Identifier): Unit

  def andThen(that: ExtractionPipeline { val s: self.t.type }): ExtractionPipeline {
    val s: self.s.type
    val t: that.t.type
  } = {
    class AndThenImpl(override val s: self.s.type,
                      override val t: that.t.type)
                     (using override val context: inox.Context) extends ExtractionPipeline {
      override def extract(symbols: s.Symbols): t.Symbols = {
        that.extract(self.extract(symbols))
      }

      override def invalidate(id: Identifier): Unit = {
        self.invalidate(id)
        that.invalidate(id)
      }
    }
    new AndThenImpl(self.s, that.t)
  }
}

object ExtractionPipeline {
  def apply(transformer: DefinitionTransformer { val s: Trees; val t: ast.Trees })
           (using inox.Context): ExtractionPipeline {
    val s: transformer.s.type
    val t: transformer.t.type
  } = {
    class Impl(override val s: transformer.s.type,
               override val t: transformer.t.type)
              (using override val context: inox.Context) extends ExtractionPipeline { self =>
      override def extract(symbols: s.Symbols): t.Symbols =
        symbols.transform(transformer.asInstanceOf[DefinitionTransformer {
          val s: self.s.type
          val t: self.t.type
        }])

      override def invalidate(id: Identifier): Unit = ()
    }
    new Impl(transformer.s, transformer.t)
  }

  def apply(transformer: inox.transformers.SymbolTransformer { val s: Trees; val t: ast.Trees })
           (using inox.Context): ExtractionPipeline {
    val s: transformer.s.type
    val t: transformer.t.type
  } = {
    class Impl(override val s: transformer.s.type,
               override val t: transformer.t.type)
              (using override val context: inox.Context) extends ExtractionPipeline {
      override def extract(symbols: s.Symbols): t.Symbols = transformer.transform(symbols)
      override def invalidate(id: Identifier): Unit = ()
    }
    new Impl(transformer.s, transformer.t)
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
  private[this] class IdentitySortsImpl(override val s: self.s.type, override val t: self.t.type)
    extends ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentitySortsImpl(self.s, self.t)

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
  private[this] class IdentityFunctionsImpl(override val s: self.s.type, override val t: self.t.type)
    extends ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentityFunctionsImpl(self.s, self.t)

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
