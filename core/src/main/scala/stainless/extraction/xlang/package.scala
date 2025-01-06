/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object xlang {

  object trees extends xlang.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with InnerClassesAbstractSymbols {
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

    object printer extends Printer { val trees: xlang.trees.type = xlang.trees }
  }

  /** As `xlang.Trees` don't extend the supported ASTs, the transformation from
    * these trees to `oo.Trees` simply consists in an identity mapping. */
  def extractor(using ctx: inox.Context) = {
    class Lowering(override val s: trees.type, override val t: innerclasses.trees.type)(using override val context: inox.Context)
      extends oo.SimplePhase
         with oo.NoSummaryPhase
         with SimplyCachedFunctions
         with SimplyCachedSorts
         with oo.IdentityTypeDefs
         with oo.SimplyCachedClasses { self =>

      override protected type TransformerContext = identity.type
      override protected def getContext(symbols: s.Symbols) = identity

      private def keepFlag(flag: s.Flag): Boolean = flag != s.Ignore && flag != s.StrictBV

      protected val identity = new Identity(self.s, self.t)

      protected class Identity(override val s: self.s.type, override val t: self.t.type) extends oo.ConcreteTreeTransformer(self.s, self.t) {
        override def transform(tpe: s.Type): t.Type = tpe match {
          case s.AnnotatedType(tpe, flags) if flags.exists(keepFlag) =>
            t.AnnotatedType(super.transform(tpe), flags.filter(keepFlag).map(super.transform))
          case s.AnnotatedType(tpe, _) => super.transform(tpe)
          case _ => super.transform(tpe)
        }

        override def transform(vd: s.ValDef): t.ValDef = {
          super.transform(vd.copy(flags = vd.flags.filter(keepFlag)))
        }
      }

      override protected def extractFunction(transformer: TransformerContext, fd: s.FunDef): (t.FunDef, Unit) =
        (transformer.transform(fd.copy(flags = fd.flags.filter(keepFlag))), ())

      override protected def extractSort(transformer: TransformerContext, sort: s.ADTSort): (t.ADTSort, Unit) =
        (transformer.transform(sort.copy(flags = sort.flags.filter(keepFlag))), ())

      override protected def extractClass(transformer: TransformerContext, cd: s.ClassDef): (t.ClassDef, Unit) =
        (transformer.transform(cd.copy(flags = cd.flags.filter(keepFlag))), ())
    }

    val lowering = new Lowering(trees, innerclasses.trees)
    utils.NamedPipeline("ConstructsUsage", ConstructsUsage(trees)) `andThen`
    utils.NamedPipeline("PartialFunctions", PartialFunctions(trees)) `andThen`
    utils.NamedPipeline("XlangLowering", lowering)
  }

  def fullExtractor(using inox.Context) = extractor `andThen` nextExtractor
  def nextExtractor(using inox.Context) = innerclasses.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: xlang.trees.type } = {
    extraction.phaseSemantics(xlang.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: innerclasses.trees.type } = {
    innerclasses.phaseSemantics
  }
}
