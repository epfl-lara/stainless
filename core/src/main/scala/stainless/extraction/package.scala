/* Copyright 2009-2018 EPFL, Lausanne */

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
  *   extraction < inlining < innerfuns < imperative < oo < throwing < methods < xlang
  *
  * Inlining adds support for function inlining.
  * Innerfuns adds inner functions.
  * Imperative adds imperative features.
  * OO adds object-oriented features.
  * Throwing handles exception lifting.
  * Methods takes care of method lifting.
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

    object Uncached extends Flag("uncached", Seq())

    override val exprOps: ExprOps { val trees: self.type } = new {
      protected val trees: self.type = self
    } with ExprOps
  }

  /** Unifies all stainless tree printers */
  trait Printer extends ast.Printer with termination.Printer

  /** Unifies all stainless tree extractors */
  trait TreeDeconstructor extends ast.TreeDeconstructor with termination.TreeDeconstructor {
    protected val s: Trees
    protected val t: Trees

    override def deconstruct(flag: s.Flag): DeconstructedFlag = flag match {
      case s.Uncached => (Seq(), Seq(), Seq(), (_, _, _) => t.Uncached)
      case _ => super.deconstruct(flag)
    }
  }

  /** Unifies all stainless expression operations */
  trait ExprOps extends ast.ExprOps with termination.ExprOps

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: extraction.trees.type = extraction.trees }
  }

  case class MissformedStainlessCode(tree: inox.ast.Trees#Tree, msg: String)
    extends Exception(msg)

  val partials = PipelineBuilder(xlang.trees, xlang.trees)(PartialFunctions(xlang.trees))

  def extract(
    program: Program { val trees: xlang.trees.type },
    ctx: inox.Context
  ): Program { val trees: extraction.trees.type } = {
    val pipeline =
      partials             andThen
      xlang.extractor      andThen
      methods.extractor    andThen
      throwing.extractor   andThen
      oo.extractor         andThen
      imperative.extractor andThen
      innerfuns.extractor  andThen
      inlining.extractor

    TreeSanitizer.check(program) // Might throw some MissformedStainlessCode
    program.transform(pipeline)
  }
}
