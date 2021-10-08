/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait TransformerWithType extends oo.TransformerWithType {
  val s: Trees
  val t: Trees
  val symbols: s.Symbols
  import symbols.{given, _}

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

    case s.While(cond, body, pred, weakInv, flags) =>
      t.While(
        transform(cond, s.BooleanType()),
        transform(body),
        pred map (transform(_, s.BooleanType())),
        weakInv map (transform(_, s.BooleanType())),
        flags map (transform)
      ).copiedFrom(expr)

    case s.ArrayUpdate(array, index, value) =>
      val at @ s.ArrayType(base) = widen(array.getType)
      t.ArrayUpdate(
        transform(array, at),
        transform(index, s.Int32Type()),
        transform(value, base)
      ).copiedFrom(expr)

    case s.Swap(array1, index1, array2, index2) =>
      val at @ s.ArrayType(base) = widen(array1.getType)
      t.Swap(
        transform(array1, at),
        transform(index1, s.Int32Type()),
        transform(array2, at),
        transform(index2, s.Int32Type()),
      ).copiedFrom(expr)

    case s.MutableMapWithDefault(from, to, default) =>
      t.MutableMapWithDefault(transform(from), transform(to),
        transform(default, s.FunctionType(Seq(), to))
      )

    case s.MutableMapApply(map, index) =>
      val mmt @ s.MutableMapType(from, to) = widen(map.getType)
      t.MutableMapApply(transform(map, mmt), transform(index, from)).copiedFrom(expr)

    case s.MutableMapUpdate(map, key, value) =>
      val mmt @ s.MutableMapType(from, to) = widen(map.getType)
      t.MutableMapUpdate(transform(map, mmt), transform(key, from), transform(value, to)).copiedFrom(expr)

    case s.MutableMapUpdated(map, key, value) =>
      val mmt @ s.MutableMapType(from, to) = widen(map.getType)
      t.MutableMapUpdated(transform(map, mmt), transform(key, from), transform(value, to)).copiedFrom(expr)

    case s.MutableMapDuplicate(map) =>
      val mmt @ s.MutableMapType(from, to) = widen(map.getType)
      t.MutableMapDuplicate(transform(map, mmt)).copiedFrom(expr)

    case s.Old(e) =>
      t.Old(transform(e, tpe)).copiedFrom(expr)

    case s.Snapshot(e) =>
      t.Snapshot(transform(e, tpe)).copiedFrom(expr)

    case s.FreshCopy(e) =>
      t.FreshCopy(transform(e, tpe)).copiedFrom(expr)

    case s.Return(e) =>
      t.Return(transform(e)).copiedFrom(expr)

    case s.BoolBitwiseAnd(lhs, rhs) =>
      t.BoolBitwiseAnd(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)

    case s.BoolBitwiseOr(lhs, rhs) =>
      t.BoolBitwiseOr(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)

    case s.BoolBitwiseXor(lhs, rhs) =>
      t.BoolBitwiseXor(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)

    case _ => super.transform(expr, tpe)
  }
}
