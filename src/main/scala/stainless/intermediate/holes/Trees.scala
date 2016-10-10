package stainless
package intermediate
package holes

trait Trees extends imperative.Trees { self =>
  case class Hole(tp: Type) extends Expr {
    override def getType(implicit s: Symbols): Type = tp
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Hole(tp) => p"???[$tp]"
    case _ => super.pp(tree)
  }

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
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