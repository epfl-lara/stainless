/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object xlang {

  object trees extends xlang.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: xlang.trees.type = xlang.trees }
  }

  /** As `xlang.Trees` don't extend the supported ASTs, the transformation from
    * these trees to `oo.Trees` simply consists in an identity mapping. */
  def extractor(implicit ctx: inox.Context) = {
    val lowering: ExtractionPipeline {
      val s: trees.type
      val t: innerclasses.trees.type
    } = new oo.SimplePhase
          with SimplyCachedFunctions
          with SimplyCachedSorts
          with oo.IdentityTypeDefs
          with oo.SimplyCachedClasses { self =>

      override val s: trees.type = trees
      override val t: innerclasses.trees.type = innerclasses.trees
      override val context = ctx

      override protected type TransformerContext = identity.type
      override protected def getContext(symbols: s.Symbols) = identity

      protected final object identity extends oo.TreeTransformer {
        override val s: self.s.type = self.s
        override val t: self.t.type = self.t

        override def transform(vd: s.ValDef): t.ValDef = {
          super.transform(vd.copy(flags = vd.flags filterNot (_ == s.Ignore)))
        }
      }

      override protected def extractFunction(transformer: TransformerContext, fd: s.FunDef): t.FunDef =
        transformer.transform(fd.copy(flags = fd.flags.filter { case s.Ignore => false case _ => true }))

      override protected def extractSort(transformer: TransformerContext, sort: s.ADTSort): t.ADTSort =
        transformer.transform(sort.copy(flags = sort.flags filterNot (_ == s.Ignore)))

      override protected def extractClass(transformer: TransformerContext, cd: s.ClassDef): t.ClassDef =
        transformer.transform(cd.copy(flags = cd.flags filterNot (_ == s.Ignore)))
    }

    utils.DebugPipeline("PartialFunctions", PartialFunctions(trees)) andThen lowering
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = innerclasses.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: xlang.trees.type } = {
    extraction.phaseSemantics(xlang.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: innerclasses.trees.type } = {
    innerclasses.phaseSemantics
  }
}
