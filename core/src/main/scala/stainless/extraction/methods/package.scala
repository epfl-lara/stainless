/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object methods {

  object trees extends methods.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: methods.trees.type = methods.trees }
  }

  def extractor(implicit ctx: inox.Context) = {
    val lowering = ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: throwing.trees.type = throwing.trees

      private def keepFlag(f: s.Flag): Boolean = f match {
        case s.IsMethodOf(_) | s.IsInvariant | s.IsAbstract => false
        case _ => true
      }

      override def transform(fd: s.FunDef): t.FunDef =
        super.transform(fd.copy(flags = fd.flags filter keepFlag))
    })

    utils.DebugPipeline("methods.MethodLifting", MethodLifting(trees, trees)) andThen
    utils.DebugPipeline("methods.FieldAccessors", FieldAccessors(trees, trees)) andThen
    lowering
  }
}
