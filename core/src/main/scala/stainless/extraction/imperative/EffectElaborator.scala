/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

trait EffectElaborator
  extends oo.CachingPhase
     with SimpleSorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with AliasAnalyzer { self =>
  import s._

  // Function rewriting depends on the effects analysis which relies on all dependencies
  // of the function, so we use a dependency cache here.
  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult](
    (fd, context) => getDependencyKey(fd.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult](
    (sort, context) => getDependencyKey(sort.id)(context.symbols)
  )

  // Function types are rewritten by the transformer depending on the result of the
  // effects analysis, so we again use a dependency cache here.
  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult](
    (cd, context) => getDependencyKey(cd.id)(context.symbols)
  )

  override protected type FunctionResult = Option[FunDef]
  override protected def registerFunctions(symbols: t.Symbols,
      functions: Seq[Option[t.FunDef]]): t.Symbols =
    symbols.withFunctions(functions.flatten)

  protected case class EffectTransformerContext(symbols: Symbols) extends AliasAnalysis

  override protected type TransformerContext = EffectTransformerContext
  override protected def getContext(symbols: Symbols) = EffectTransformerContext(symbols)

  override protected def extractFunction(tctx: EffectTransformerContext,
      fd: FunDef): Option[FunDef] =
  {
    import tctx._
    import symbols._

    // Just run and dump the analysis for now
    if (fd.params.nonEmpty) {
      val (graph, resultOpt) = computeGraph(Summaries.empty, fd.params, fd.fullBody)
      dumpGraph(graph, resultOpt, s"heapgraph_${fd.id}.dot")
    }

    Some(fd)
  }

  override protected def extractSort(tctx: EffectTransformerContext, sort: ADTSort): ADTSort =
    sort

  override protected def extractClass(tctx: EffectTransformerContext, cd: ClassDef): ClassDef =
    cd
}

object EffectElaborator {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new EffectElaborator {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
