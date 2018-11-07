/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package imperative

// FIXME: @romac
trait TransformerWithType extends oo.TransformerWithType {
  val s: Trees
  val t: Trees
  val symbols: s.Symbols
  import symbols._

  override def transform(expr: s.Expr, tpe: s.Type): t.Expr = expr match {
    case s.Block(es, last) =>
      t.Block(es map (e => transform(e)), transform(last, tpe)).copiedFrom(expr)

    case s.LetVar(vd, e, b) =>
      t.LetVar(transform(vd), transform(e, vd.getType), transform(b, tpe)).copiedFrom(expr)

    case s.Assignment(v, value) =>
      t.Assignment(transform(v).asInstanceOf[t.Variable], transform(value, v.getType)).copiedFrom(expr)

    case fa @ s.FieldAssignment(obj, sel, value) =>
      t.FieldAssignment(
        transform(obj),
        sel,
        transform(value, fa.getField.get.getType)
      ).copiedFrom(expr)

    case s.While(cond, body, pred) =>
      t.While(
        transform(cond, s.BooleanType()),
        transform(body),
        pred map (transform(_, s.BooleanType()))
      ).copiedFrom(expr)

    case s.ArrayUpdate(array, index, value) =>
      val at @ s.ArrayType(base) = widen(array.getType)
      t.ArrayUpdate(
        transform(array, at),
        transform(index, s.Int32Type()),
        transform(value, base)
      ).copiedFrom(expr)

    case s.Old(e) =>
      t.Old(transform(e, tpe)).copiedFrom(expr)

    case s.BoolBitwiseAnd(lhs, rhs) =>
      t.BoolBitwiseAnd(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)

    case s.BoolBitwiseOr(lhs, rhs) =>
      t.BoolBitwiseOr(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)

    case s.BoolBitwiseXor(lhs, rhs) =>
      t.BoolBitwiseXor(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)

    case _ => super.transform(expr, tpe)
  }
}
