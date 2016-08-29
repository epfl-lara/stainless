/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

import inox.ast.Identifier

trait TreeDeconstructor extends ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(vd: s.Definition): (Identifier, Seq[s.Expr], Seq[s.Type], (Identifier, Seq[t.Expr], Seq[t.Type]) => t.Definition) = vd match {
    case s.VarDef(id, tpe) => (id, Seq.empty, Seq(tpe), (id, _, tps) => t.VarDef(id, tps.head))
    case _ => super.deconstruct(vd)
  }

  override def deconstruct(e: s.Expr): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.MethodInvocation(rec, id, tps, args) =>
      (rec +: args, tps, (es, tps) => t.MethodInvocation(es(0), id, tps, es.tail))

    case s.ClassConstructor(ct, args) =>
      (args, Seq(ct), (es, tps) => t.ClassConstructor(tps.head.asInstanceOf[t.ClassType], es))

    case s.ClassSelector(expr, selector) =>
      (Seq(expr), Seq.empty, (es, tps) => t.ClassSelector(es.head, selector))

    case s.This(ct) =>
      (Seq.empty, Seq(ct), (es, tps) => t.This(tps.head.asInstanceOf[t.ClassType]))

    case s.Block(exprs, last) =>
      (exprs :+ last, Seq.empty, (es, tps) => t.Block(es.init, es.last))

    case s.Assignment(v, value) =>
      (Seq(v, value), Seq.empty, (es, tps) => t.Assignment(es(0).asInstanceOf[t.Variable], es(1)))

    case s.FieldAssignment(obj, selector, value) =>
      (Seq(obj, value), Seq.empty, (es, tps) => t.FieldAssignment(es(0), selector, es(1)))

    case s.While(cond, body, pred) =>
      (Seq(cond, body) ++ pred, Seq.empty, (es, tps) => t.While(es(0), es(1), es.drop(2).headOption))

    case s.ArrayUpdate(array, index, value) =>
      (Seq(array, index, value), Seq.empty, (es, tps) => t.ArrayUpdate(es(0), es(1), es(2)))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(tpe: s.Type): (Seq[s.Type], Seq[t.Type] => t.Type) = tpe match {
    case s.ClassType(id, tps) =>
      (tps, tps => t.ClassType(id, tps))

    case _ => super.deconstruct(tpe)
  }
}

trait Extractors extends ast.Extractors { self: Trees =>

  val deconstructor: TreeDeconstructor {
    val s: self.type
    val t: self.type
  }
}
