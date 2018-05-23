/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object xlang {

  object trees extends xlang.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: xlang.trees.type = xlang.trees }
  }

  /** As `xlang.Trees` don't extend the supported ASTs, the transformation from
    * these trees to `oo.Trees` simply consists in an identity mapping. */
  val extractor = PipelineBuilder(trees, methods.trees)(prev => new PipelinePhase with oo.SimplePhase {
    override val s: trees.type = trees
    override val t: methods.trees.type = methods.trees
    override protected val previous: prev.type = prev

    override protected def transformFunction(transformer: TransformerContext, fd: s.FunDef): t.FunDef =
      transformer.transform(fd.copy(flags = fd.flags.filter { case s.Ignore => false case _ => true }))

    override protected def transformSort(transformer: TransformerContext, sort: s.ADTSort): t.ADTSort =
      transformer.transform(sort.copy(flags = sort.flags filterNot (_ == s.Ignore)))

    override protected def transformClass(transformer: TransformerContext, cd: s.ClassDef): t.ClassDef =
      transformer.transform(cd.copy(flags = cd.flags filterNot (_ == s.Ignore)))
  })
}
