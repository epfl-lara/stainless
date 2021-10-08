/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object termination {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
        functions: Map[Identifier, FunDef],
        sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with StainlessAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols = {
      Symbols(functions, sorts)
    }

    object printer extends Printer { val trees: termination.trees.type = termination.trees }
  }

  def extractor(using inox.Context) = {
    class LoweringImpl(override val s: trees.type, override val t: extraction.trees.type) extends CheckingTransformer {
      // We remove `Induct` flags that may appear in let bindings and in variables after FunctionInlining
      override def transform(vd: s.ValDef): t.ValDef = {
        t.ValDef(vd.id, transform(vd.tpe), vd.flags.filter(_ != s.Induct).map(transform)).copiedFrom(vd)
      }

      override def transform(e: s.Expr): t.Expr = e match {
        case s.Variable(id, tpe, flags) =>
          t.Variable(id, transform(tpe), flags.filter(_ != s.Induct).map(transform)).copiedFrom(e)
        case _ => super.transform(e)
      }
    }
    val lowering = ExtractionPipeline(new LoweringImpl(trees, extraction.trees))

    utils.DebugPipeline("SizedADTExtraction", SizedADTExtraction(trees)) andThen
    utils.DebugPipeline("InductElimination", InductElimination(trees)) andThen
    lowering
  }

  def fullExtractor(using inox.Context) = extractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: termination.trees.type } = {
    extraction.phaseSemantics(termination.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: extraction.trees.type } = {
    extraction.extractionSemantics
  }
}
