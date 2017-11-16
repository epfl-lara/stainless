/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import scala.language.existentials

/** Provides definitions for a hierarchy of languages above stainless,
  * topped by xlang, which is the extended input language of stainless.
  *
  * The traits [[extraction.Trees]], [[extraction.TreeDeconstructor]]
  * and [[extraction.ExprOps]] (defined in the [[extraction]] package
  * object) provide the unification point of all different stainless tree
  * types that can appear once extraction and pre-processing has finished.
  *
  * The hierarhcy is
  *   extraction < inlining < innerfuns < imperative < holes < oo < xlang
  *
  * Inlining adds support for function inlining.
  * Innerfuns adds inner functions.
  * Imperative adds imperative features.
  * Holes adds the hole (???) synthesis construct.
  * OO adds object-oriented features.
  * xlang adds imports and module structure.
  */
package object extraction {

  /** Unifies all stainless tree definitions */
  trait Trees extends ast.Trees with termination.Trees { self =>
    override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
      case tree: Trees => new TreeDeconstructor {
        protected val s: self.type = self
        protected val t: tree.type = tree
      }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

      case _ => super.getDeconstructor(that)
    }

    override val exprOps: ExprOps { val trees: self.type } = new {
      protected val trees: self.type = self
    } with ExprOps
  }

  /** Unifies all stainless tree printers */
  trait Printer extends ast.Printer with termination.Printer

  /** Unifies all stainless tree extractors */
  trait TreeDeconstructor extends ast.TreeDeconstructor with termination.TreeDeconstructor

  /** Unifies all stainless expression operations */
  trait ExprOps extends ast.ExprOps with termination.ExprOps

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: extraction.trees.type = extraction.trees }
  }

  case class MissformedStainlessCode(tree: inox.ast.Trees#Tree, msg: String)
    extends Exception(msg)

  def extract(
    program: Program { val trees: xlang.trees.type },
    ctx: inox.Context
  ): Program { val trees: extraction.trees.type } = {
    val pipeline =
      xlang.extractor      andThen
      oo.extractor         andThen
      holes.extractor      andThen
      imperative.extractor andThen
      innerfuns.extractor  andThen
      inlining.extractor

    TreeSanitizer.check(program) // Might throw some MissformedStainlessCode
    program.transform(pipeline)
  }
}
