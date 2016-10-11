/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate
package innerfuns

trait Trees extends stainless.ast.Trees { self =>

  case class LetRec(defs: Seq[(ValDef, Expr)], in: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      // FIXME
      in.getType
    }
  }

  case class ApplyLetRec(fun: Variable, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      // FIXME
      Untyped
    }
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    // FIXME
    case LetRec(defs, body) =>
      defs foreach { case (name, Lambda(args, body)) =>
        p"def $name "
      }

    case _ => super.ppBody(tree)
  }
  // FIXME requiresBraces

  override val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  } = new TreeDeconstructor {
    protected val s: self.type = self
    protected val t: self.type = self
  }
}

trait TreeDeconstructor extends ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.LetRec(defs, body) =>
      (
        defs map (_._1.toVariable),
        defs.map(_._2) :+ body,
        Seq(),
        (vs, es, _) => t.LetRec(vs.zip(es.init).map{case (v, e) => (v.toVal, e)}, es.last)
      )
    case s.ApplyLetRec(fun, args) =>
      (
        Seq(fun),
        args,
        Seq(),
        (vs, es, _) => t.ApplyLetRec(vs.head, es)
      )
    case other =>
      super.deconstruct(other)
  }

}

