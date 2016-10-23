/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package holes

trait Trees extends imperative.Trees { self =>
  case class Hole(tp: Type) extends Expr {
    override def getType(implicit s: Symbols): Type = tp
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Hole(tp) => p"???[$tp]"
    case _ => super.ppBody(tree)
  }

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[inox.ast.TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait TreeDeconstructor extends imperative.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.Hole(tp) =>
      (Seq(), Seq(), Seq(tp), (_, _, tps) => t.Hole(tps.head))
    case other =>
      super.deconstruct(other)
  }

}
