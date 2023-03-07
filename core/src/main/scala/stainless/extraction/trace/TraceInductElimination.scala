package stainless
package extraction
package trace

import stainless.equivchk.Utils

class TraceInductElimination(override val s: Trees, override val t: termination.Trees)
                            (using override val context: inox.Context)
  extends CachingPhase
    with NoSummaryPhase
    with SimplyCachedFunctions
    with IdentitySorts
    with Utils { self =>
  import s._
  override val trees: self.s.type = s

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def extractFunction(symbols: TransformerContext, fd: FunDef): (FunctionResult, Unit) = {
    val fns = elimTraceInduct(symbols, fd)
      .map(res => res.updatedFd +: res.helper.toSeq)
      .getOrElse(Seq(fd))
      .map(identity.transform)
    (fns, ())
  }

  private[this] class Identity(override val s: self.s.type, override val t: self.t.type) extends transformers.ConcreteTreeTransformer(s, t)
  private[this] val identity = new Identity(self.s, self.t)
}

object TraceInductElimination {
  def apply(ts: Trees, tt: termination.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends TraceInductElimination(s, t)
    new Impl(ts, tt)
  }
}