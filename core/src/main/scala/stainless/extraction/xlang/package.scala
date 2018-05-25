/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

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
  def extractor(implicit ctx: inox.Context) = {
    val lowering: ExtractionPhase {
      val s: trees.type
      val t: methods.trees.type
    } = new oo.SimplePhase {
      override val s: trees.type = trees
      override val t: methods.trees.type = methods.trees
      override val context = ctx

      override protected def transformFunction(transformer: TransformerContext, fd: s.FunDef): t.FunDef =
        transformer.transform(fd.copy(flags = fd.flags.filter { case s.Ignore => false case _ => true }))

      override protected def transformSort(transformer: TransformerContext, sort: s.ADTSort): t.ADTSort =
        transformer.transform(sort.copy(flags = sort.flags filterNot (_ == s.Ignore)))

      override protected def transformClass(transformer: TransformerContext, cd: s.ClassDef): t.ClassDef =
        transformer.transform(cd.copy(flags = cd.flags filterNot (_ == s.Ignore)))
    }

    TreeSanitizer(trees) andThen
    PartialFunctions(trees) andThen
    lowering
  }
}
