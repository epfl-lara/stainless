/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

import transformers._

enum ExtractionSummary {
  case Node(lhs: ExtractionSummary, rhs: ExtractionSummary)
  case Leaf[T <: ExtractionPipelineCreator](pipelineCreator: T)(val summary: pipelineCreator.SummaryData)
  case NoSummary

  def leafs: Seq[Leaf[?]] = this match {
    case Node(lhs, rhs) => lhs.leafs ++ rhs.leafs
    case l@Leaf(_) => Seq(l)
    case NoSummary => Seq()
  }
}

trait ExtractionPipelineCreator {
  type SummaryData
  val name: String
}

trait ExtractionPipeline { self =>
  val s: ast.Trees
  val t: ast.Trees
  val context: inox.Context

  import context.given

  protected val printerOpts: s.PrinterOptions = s.PrinterOptions.fromContext(context)
  given givenPipelinePrinterOpts: printerOpts.type = printerOpts

  def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary)

  def invalidate(id: Identifier): Unit

  def andThen(that: ExtractionPipeline { val s: self.t.type }): ExtractionPipeline {
    val s: self.s.type
    val t: that.t.type
  } = {
    class AndThenImpl(override val s: self.s.type,
                      override val t: that.t.type)
                     (using override val context: inox.Context) extends ExtractionPipeline {
      override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
        val (slfSym, slfSum) = self.extract(symbols)
        val (thatSym, thatSum) = that.extract(slfSym)
        (thatSym, ExtractionSummary.Node(slfSum, thatSum))
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
      override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) =
        (
          symbols.transform(transformer.asInstanceOf[DefinitionTransformer {
            val s: self.s.type
            val t: self.t.type
          }]),
          ExtractionSummary.NoSummary
        )

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
      override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) =
        (transformer.transform(symbols), ExtractionSummary.NoSummary)
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
  protected type FunctionSummary
  protected val funCache: ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)]

  protected type SortResult
  protected type SortSummary
  protected val sortCache: ExtractionCache[s.ADTSort, (SortResult, SortSummary)]

  protected def extractFunction(context: TransformerContext, fd: s.FunDef): (FunctionResult, FunctionSummary)
  protected def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols

  protected def extractSort(context: TransformerContext, sort: s.ADTSort): (SortResult, SortSummary)
  protected def registerSorts(symbols: t.Symbols, sorts: Seq[SortResult]): t.Symbols

  class AllSummaries(val fnsSummary: Seq[FunctionSummary] = Seq.empty, val sortsSummary: Seq[SortSummary] = Seq.empty)

  protected def combineSummaries(summaries: AllSummaries): ExtractionSummary

  override final def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    val context = getContext(symbols)
    val (exSyms, allSummaries) = extractSymbols(context, symbols)
    val exSummary = combineSummaries(allSummaries)
    (exSyms, exSummary)
  }

  protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): (t.Symbols, AllSummaries) = {
    val (functions, fnsSummary) = symbols.functions.values.map { fd =>
      funCache.cached(fd, context)(extractFunction(context, fd))
    }.toSeq.unzip

    val (sorts, sortsSummary) = symbols.sorts.values.map { sort =>
      sortCache.cached(sort, context)(extractSort(context, sort))
    }.toSeq.unzip

    (registerSorts(registerFunctions(t.NoSymbols, functions), sorts), AllSummaries(fnsSummary, sortsSummary))
  }
}

trait SimpleSorts extends CachingPhase {
  override protected type SortResult = t.ADTSort
  override protected def registerSorts(symbols: t.Symbols, sorts: Seq[t.ADTSort]): t.Symbols = symbols.withSorts(sorts)
}

trait SimplyCachedSorts extends CachingPhase {
  override protected final val sortCache: ExtractionCache[s.ADTSort, (SortResult, SortSummary)] = new SimpleCache[s.ADTSort, (SortResult, SortSummary)]
}

trait IdentitySorts extends SimpleSorts with SimplyCachedSorts { self =>
  override protected type SortSummary = Unit

  private[this] class IdentitySortsImpl(override val s: self.s.type, override val t: self.t.type)
    extends ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentitySortsImpl(self.s, self.t)

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): (t.ADTSort, Unit) = (identity.transform(sort), ())
}

trait SimpleFunctions extends CachingPhase {
  override protected type FunctionResult = t.FunDef
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[t.FunDef]): t.Symbols = symbols.withFunctions(functions)
}

trait SimplyCachedFunctions extends CachingPhase {
  override protected final val funCache: ExtractionCache[s.FunDef, (FunctionResult, FunctionSummary)] = new SimpleCache[s.FunDef, (FunctionResult, FunctionSummary)]
}

trait IdentityFunctions extends SimpleFunctions with SimplyCachedFunctions { self =>
  override protected type FunctionSummary = Unit

  private[this] class IdentityFunctionsImpl(override val s: self.s.type, override val t: self.t.type)
    extends ConcreteTreeTransformer(s, t)
  private[this] val identity = new IdentityFunctionsImpl(self.s, self.t)

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = (identity.transform(fd), ())
}

trait NoSummaryPhase extends CachingPhase {
  override protected type FunctionSummary = Unit
  override protected type SortSummary = Unit

  override protected def combineSummaries(summaries: AllSummaries): ExtractionSummary = ExtractionSummary.NoSummary
}

trait SimplePhase extends ExtractionPipeline with SimpleSorts with SimpleFunctions with NoSummaryPhase { self =>
  override protected type TransformerContext <: TreeTransformer {
    val s: self.s.type
    val t: self.t.type
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) = (context.transform(fd), ())
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): (t.ADTSort, Unit) = (context.transform(sort), ())
}
