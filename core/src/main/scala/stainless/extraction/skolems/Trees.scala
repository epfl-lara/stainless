/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package skolems

import inox.transformers.Transformer
import stainless.transformers.TreeTransformer
import stainless.transformers.TreeTraverser

trait Trees extends xlang.Trees { self =>

  case class Skolem(id: Identifier, tpe: Type) extends Expr with CachingTyped {
    def computeTpe(stripRefinements: Boolean)(using Symbols) = tpe.getTpe(stripRefinements)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

    case _ => super.getDeconstructor(that)
  }
}

trait TreeDeconstructor extends xlang.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.Skolem(id, tpe) =>
      (Seq(id), Seq(), Seq(), Seq(tpe), Seq(), (ids, _, _, tpes, _) => t.Skolem(ids(0), tpes(0)))


    case _ => super.deconstruct(e)
  }
}

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor

trait Printer extends xlang.Printer {
  val trees: Trees
  import trees._

  override def ppBody(tree: Tree)(using PrinterContext): Unit = tree match {
    case Skolem(id, tpe) => p"$id"
    case _ => super.ppBody(tree)
  }

}