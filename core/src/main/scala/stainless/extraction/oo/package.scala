/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object oo {

  object trees extends oo.Trees with ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with OOAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ): Symbols = {
      Symbols(functions, sorts, classes, typeDefs)
    }

    object printer extends Printer { val trees: oo.trees.type = oo.trees }
  }

  def extractor(using inox.Context) = {
    class LoweringImpl(override val s: trees.type, override val t: innerfuns.trees.type) extends CheckingTransformer {
      override def transform(fd: s.FunDef): t.FunDef = {
        super.transform(fd.copy(flags = fd.flags.filterNot(_ == s.IsInvariant)))
      }
    }
    val lowering = ExtractionPipeline(new LoweringImpl(trees, innerfuns.trees))

    utils.NamedPipeline("AdtSpecialization", AdtSpecialization(trees, trees)) `andThen`
    //utils.NamedPipeline("RefinementLifting", RefinementLifting(trees, trees)) `andThen`
    utils.NamedPipeline("TypeEncoding",      TypeEncoding(trees, trees))      `andThen`
    utils.NamedPipeline("InvariantInitialization", InvariantInitialization(trees, trees)) `andThen`
    lowering
  }

  def fullExtractor(using inox.Context) = extractor `andThen` nextExtractor
  def nextExtractor(using inox.Context) = innerfuns.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: oo.trees.type } = {
    extraction.phaseSemantics(oo.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: innerfuns.trees.type } = {
    innerfuns.phaseSemantics
  }
}
