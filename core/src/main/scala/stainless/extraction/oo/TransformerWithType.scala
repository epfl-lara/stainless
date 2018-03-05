/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction.oo

trait TransformerWithType extends TreeTransformer {
  val s: Trees
  val t: Trees
  val symbols: s.Symbols
  import symbols._

  private def getArithmeticType(lhs: s.Expr, expectedType: s.Type): s.Type = expectedType match {
    case s.AnyType() => lhs.getType
    case _ => expectedType
  }

  def transform(pat: s.Pattern, tpe: s.Type): t.Pattern = pat match {
    case s.WildcardPattern(ob) =>
      t.WildcardPattern(ob map transform).copiedFrom(pat)

    case s.InstanceOfPattern(ob, tpe) =>
      t.InstanceOfPattern(ob map transform, transform(tpe)).copiedFrom(pat)

    case s.ClassPattern(ob, ct, subs) =>
      t.ClassPattern(
        ob map transform,
        transform(ct).asInstanceOf[t.ClassType],
        (subs zip ct.tcd.fields.map(_.tpe)) map (p => transform(p._1, p._2))
      ).copiedFrom(pat)

    case s.ADTPattern(ob, id, tps, subs) =>
      t.ADTPattern(
        ob map transform, id, tps map transform,
        (subs zip getConstructor(id, tps).fields.map(_.tpe)) map (p => transform(p._1, p._2))
      ).copiedFrom(pat)

    case s.TuplePattern(ob, subs) => tpe match {
      case s.TupleType(tps) =>
        t.TuplePattern(ob map transform, (subs zip tps) map (p => transform(p._1, p._2))).copiedFrom(pat)
      case _ =>
        t.TuplePattern(ob map transform, subs map (transform(_, s.AnyType()))).copiedFrom(pat)
    }

    case up @ s.UnapplyPattern(ob, id, tps, subs) =>
      val subTps = up.getGet.returnType match {
        case tpe if subs.size == 1 => Seq(tpe)
        case s.TupleType(tps2) => tps2
        case _ => subs.map(_ => s.AnyType())
      }

      t.UnapplyPattern(ob map transform, id, tps map transform,
        (subs zip subTps) map (p => transform(p._1, p._2))).copiedFrom(pat)

    case s.LiteralPattern(ob, lit) =>
      t.LiteralPattern(ob map transform, transform(lit).asInstanceOf[t.Literal[_]])
  }

  def transform(expr: s.Expr, tpe: s.Type): t.Expr = expr match {
    case s.Assume(pred, body) =>
      t.Assume(transform(pred, s.BooleanType()), transform(body, tpe)).copiedFrom(expr)
    case s.Let(vd, e, b) =>
      t.Let(transform(vd), transform(e, vd.tpe), transform(b, tpe)).copiedFrom(expr)
    case s.Application(caller, args) =>
      val s.FunctionType(from, to) = caller.getType
      t.Application(
        transform(caller, s.FunctionType(from, tpe)),
        (args zip from) map (p => transform(p._1, p._2))
      ).copiedFrom(expr)
    case s.Lambda(args, body) => tpe match {
      case s.FunctionType(from, to) => t.Lambda(args map transform, transform(body, to)).copiedFrom(expr)
      case _ => t.Lambda(args map transform, transform(body, s.AnyType())).copiedFrom(expr)
    }
    case s.Forall(args, body) =>
      t.Forall(args map transform, transform(body, s.BooleanType())).copiedFrom(expr)
    case s.Choose(res, pred) =>
      t.Choose(transform(res), transform(pred, s.BooleanType())).copiedFrom(expr)
    case fi @ s.FunctionInvocation(id, tps, args) =>
      t.FunctionInvocation(id, tps map transform,
        (args zip fi.tfd.params.map(_.tpe)) map (p => transform(p._1, p._2))).copiedFrom(expr)
    case s.IfExpr(cond, thenn, elze) =>
      t.IfExpr(transform(cond, s.BooleanType()), transform(thenn, tpe), transform(elze, tpe)).copiedFrom(expr)
    case s.ADT(id, tps, args) =>
      t.ADT(id, tps map transform,
        (args zip getConstructor(id, tps).fieldsTypes) map (p => transform(p._1, p._2))).copiedFrom(expr)
    case s.IsConstructor(e, id) =>
      t.IsConstructor(transform(e, e.getType), id).copiedFrom(expr)
    case s.ADTSelector(e, sel) =>
      t.ADTSelector(transform(e, e.getType), sel).copiedFrom(expr)
    case s.Equals(lhs, rhs) =>
      t.Equals(transform(lhs, s.AnyType()), transform(rhs, s.AnyType())).copiedFrom(expr)
    case s.And(es) =>
      t.And(es map (transform(_, s.BooleanType()))).copiedFrom(expr)
    case s.Or(es) =>
      t.Or(es map (transform(_, s.BooleanType()))).copiedFrom(expr)
    case s.Implies(lhs, rhs) =>
      t.Implies(transform(lhs, s.BooleanType()), transform(rhs, s.BooleanType())).copiedFrom(expr)
    case s.Not(e) =>
      t.Not(transform(e, s.BooleanType())).copiedFrom(expr)
    case s.StringConcat(lhs, rhs) =>
      t.StringConcat(transform(lhs, s.StringType()), transform(rhs, s.StringType())).copiedFrom(expr)
    case s.SubString(str, start, end) =>
      t.SubString(
        transform(str, s.StringType()),
        transform(start, s.IntegerType()),
        transform(end, s.IntegerType())
      ).copiedFrom(expr)
    case s.StringLength(str) =>
      t.StringLength(transform(str, s.StringType())).copiedFrom(expr)
    case s.Plus(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.Plus(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.Minus(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.Minus(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.UMinus(e) =>
      val atpe = getArithmeticType(e, tpe)
      t.UMinus(transform(e, atpe)).copiedFrom(expr)
    case s.Times(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.Times(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.Division(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.Division(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.Remainder(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.Remainder(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.Modulo(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.Modulo(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.LessThan(lhs, rhs) =>
      t.LessThan(transform(lhs, lhs.getType), transform(rhs, lhs.getType)).copiedFrom(expr)
    case s.GreaterThan(lhs, rhs) =>
      t.GreaterThan(transform(lhs, lhs.getType), transform(rhs, lhs.getType)).copiedFrom(expr)
    case s.LessEquals(lhs, rhs) =>
      t.LessEquals(transform(lhs, lhs.getType), transform(rhs, lhs.getType)).copiedFrom(expr)
    case s.GreaterEquals(lhs, rhs) =>
      t.GreaterEquals(transform(lhs, lhs.getType), transform(rhs, lhs.getType)).copiedFrom(expr)
    case s.BVNot(e) =>
      val atpe = getArithmeticType(e, tpe)
      t.BVNot(transform(e, atpe)).copiedFrom(expr)
    case s.BVOr(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.BVOr(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.BVAnd(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.BVAnd(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.BVXor(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.BVXor(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.BVShiftLeft(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.BVShiftLeft(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.BVAShiftRight(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.BVAShiftRight(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.BVLShiftRight(lhs, rhs) =>
      val atpe = getArithmeticType(lhs, tpe)
      t.BVLShiftRight(transform(lhs, atpe), transform(rhs, atpe)).copiedFrom(expr)
    case s.BVNarrowingCast(expr, tpe) =>
      t.BVNarrowingCast(transform(expr, expr.getType), transform(tpe).asInstanceOf[t.BVType]).copiedFrom(expr)
    case s.BVWideningCast(expr, tpe) =>
      t.BVWideningCast(transform(expr, expr.getType), transform(tpe).asInstanceOf[t.BVType]).copiedFrom(expr)
    case s.Tuple(es) => tpe match {
      case s.TupleType(tps) => t.Tuple((es zip tps) map (p => transform(p._1, p._2))).copiedFrom(expr)
      case _ => t.Tuple(es map (transform(_, s.AnyType()))).copiedFrom(expr)
    }
    case s.TupleSelect(tuple, index) =>
      val s.TupleType(tps) = tuple.getType
      val tt = s.TupleType(tps.zipWithIndex.map { case (tp, i) => if (i == index - 1) tpe else tp })
      t.TupleSelect(transform(tuple, tt), index).copiedFrom(expr)
    case s.FiniteSet(elems, base) =>
      t.FiniteSet(elems map (transform(_, base)), transform(base)).copiedFrom(expr)
    case s.SetAdd(set, elem) =>
      val st @ s.SetType(base) = set.getType
      t.SetAdd(transform(set, st), transform(elem, base)).copiedFrom(expr)
    case s.ElementOfSet(elem, set) =>
      val st @ s.SetType(base) = set.getType
      t.ElementOfSet(transform(elem, base), transform(set, st)).copiedFrom(expr)
    case s.SubsetOf(s1, s2) =>
      t.SubsetOf(transform(s1, s1.getType), transform(s2, s1.getType)).copiedFrom(expr)
    case s.SetIntersection(s1, s2) =>
      t.SetIntersection(transform(s1, s1.getType), transform(s2, s1.getType)).copiedFrom(expr)
    case s.SetUnion(s1, s2) =>
      t.SetUnion(transform(s1, s1.getType), transform(s2, s1.getType)).copiedFrom(expr)
    case s.SetDifference(s1, s2) =>
      t.SetDifference(transform(s1, s1.getType), transform(s2, s1.getType)).copiedFrom(expr)
    case s.FiniteBag(elems, base) =>
      t.FiniteBag(
        elems.map(p => (transform(p._1, base), transform(p._2, s.IntegerType()))),
        transform(base)
      ).copiedFrom(expr)
    case s.BagAdd(bag, elem) =>
      val bt @ s.BagType(base) = bag.getType
      t.BagAdd(transform(bag, bt), transform(elem, base)).copiedFrom(expr)
    case s.MultiplicityInBag(elem, bag) =>
      val bt @ s.BagType(base) = bag.getType
      t.MultiplicityInBag(transform(elem, base), transform(bag, bt)).copiedFrom(expr)
    case s.BagIntersection(b1, b2) =>
      t.BagIntersection(transform(b1, b1.getType), transform(b2, b1.getType)).copiedFrom(expr)
    case s.BagUnion(b1, b2) =>
      t.BagUnion(transform(b1, b1.getType), transform(b2, b1.getType)).copiedFrom(expr)
    case s.BagDifference(b1, b2) =>
      t.BagDifference(transform(b1, b1.getType), transform(b2, b1.getType)).copiedFrom(expr)
    case s.FiniteMap(pairs, dflt, kt, vt) =>
      t.FiniteMap(
        pairs map (p => (transform(p._1, kt), transform(p._2, vt))),
        transform(dflt, vt),
        transform(kt),
        transform(vt)
      ).copiedFrom(expr)
    case s.MapApply(map, key) =>
      val mt @ s.MapType(from, _) = map.getType
      t.MapApply(transform(map, mt), transform(key, from)).copiedFrom(expr)
    case s.MapUpdated(map, key, value) =>
      val mt @ s.MapType(from, to) = map.getType
      t.MapUpdated(transform(map, mt), transform(key, from), transform(value, to)).copiedFrom(expr)

    // Stainless expressions
    case s.Require(pred, body) =>
      t.Require(transform(pred, s.BooleanType()), transform(body, tpe)).copiedFrom(expr)
    case s.Annotated(body, flags) =>
      t.Annotated(transform(body, tpe), flags map transform).copiedFrom(expr)
    case s.Ensuring(body, pred) =>
      t.Ensuring(
        transform(body, tpe),
        transform(pred, s.FunctionType(Seq(tpe), s.BooleanType())).asInstanceOf[t.Lambda]
      ).copiedFrom(expr)
    case s.Assert(pred, err, body) =>
      t.Assert(transform(pred, s.BooleanType()), err, transform(body, tpe)).copiedFrom(expr)
    case s.MatchExpr(scrut, cses) =>
      t.MatchExpr(
        transform(scrut, scrut.getType),
        cses map { case cse @ s.MatchCase(pat, guard, rhs) =>
          t.MatchCase(
            transform(pat, scrut.getType),
            guard map (transform(_, s.BooleanType())),
            transform(rhs, tpe)
          ).copiedFrom(cse)
        }).copiedFrom(expr)
    case s.FiniteArray(elems, base) =>
      t.FiniteArray(elems map (transform(_, base)), transform(base)).copiedFrom(expr)
    case s.LargeArray(elems, dflt, size, base) =>
      t.LargeArray(
        elems mapValues (transform(_, base)),
        transform(dflt, base),
        transform(size, s.Int32Type()),
        transform(base)
      ).copiedFrom(expr)
    case s.ArraySelect(array, index) =>
      t.ArraySelect(transform(array, array.getType), transform(index, s.Int32Type())).copiedFrom(expr)
    case s.ArrayUpdated(array, index, value) =>
      val at @ s.ArrayType(base) = array.getType
      t.ArrayUpdated(
        transform(array, at),
        transform(index, s.Int32Type()),
        transform(value, base)
      ).copiedFrom(expr)
    case s.ArrayLength(array) =>
      t.ArrayLength(transform(array, array.getType)).copiedFrom(expr)

    // Inner function expressions
    case s.LetRec(fds, body) =>
      t.LetRec(
        fds.map { case lfd @ s.LocalFunDef(name, tparams, body) =>
          t.LocalFunDef(
            transform(name),
            tparams map transform,
            transform(body, name.tpe).asInstanceOf[t.Lambda]
          ).copiedFrom(lfd)
        },
        transform(body, tpe)
      ).copiedFrom(expr)
    case s.ApplyLetRec(fun, tparams, tps, args) =>
      val s.FunctionType(from, _) = s.typeOps.instantiateType(fun.tpe, (tparams zip tps).toMap)
      t.ApplyLetRec(
        transform(fun.toVal).toVariable,
        tparams map (tp => transform(tp).asInstanceOf[t.TypeParameter]),
        tps map transform,
        (args zip from) map (p => transform(p._1, p._2))
      ).copiedFrom(expr)

    // Imperative expressions
    case s.Block(es, last) =>
      t.Block(es map (e => transform(e, e.getType)), transform(last, tpe)).copiedFrom(expr)
    case s.LetVar(vd, e, b) =>
      t.LetVar(transform(vd), transform(e, vd.tpe), transform(b, tpe)).copiedFrom(expr)
    case s.Assignment(v, value) =>
      t.Assignment(transform(v).asInstanceOf[t.Variable], transform(value, v.tpe)).copiedFrom(expr)
    case fa @ s.FieldAssignment(obj, sel, value) =>
      t.FieldAssignment(
        transform(obj, obj.getType),
        sel,
        transform(value, fa.getField.get.tpe)
      ).copiedFrom(expr)
    case s.While(cond, body, pred) =>
      t.While(
        transform(cond, s.BooleanType()),
        transform(body, body.getType),
        pred map (transform(_, s.BooleanType()))
      ).copiedFrom(expr)
    case s.ArrayUpdate(array, index, value) =>
      val at @ s.ArrayType(base) = array.getType
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

    // OO expressions
    case s.MethodInvocation(rec, id, tps, args) =>
      val (recTpe +: argTps) = getFunction(id, tps).params.map(_.tpe)
      t.MethodInvocation(
        transform(rec, recTpe),
        id,
        tps map transform,
        (args zip argTps) map (p => transform(p._1, p._2))
      ).copiedFrom(expr)
    case s.ClassConstructor(ct, args) =>
      t.ClassConstructor(
        transform(ct).asInstanceOf[t.ClassType],
        (args zip ct.tcd.fields.map(_.tpe)) map (p => transform(p._1, p._2))
      ).copiedFrom(expr)
    case s.ClassSelector(e, sel) =>
      t.ClassSelector(transform(e, e.getType), sel).copiedFrom(expr)
    case s.This(ct) =>
      t.This(transform(ct).asInstanceOf[t.ClassType]).copiedFrom(expr)
    case s.Super(ct) =>
      t.Super(transform(ct).asInstanceOf[t.ClassType]).copiedFrom(expr)
    case s.IsInstanceOf(e, tp) =>
      t.IsInstanceOf(transform(e, s.AnyType()), transform(tp)).copiedFrom(expr)
    case s.AsInstanceOf(e, tp) =>
      t.AsInstanceOf(transform(e, s.AnyType()), transform(tp)).copiedFrom(expr)

    case term: t.Terminal => super.transform(term)
  }

  override def transform(e: s.Expr): t.Expr = transform(e, e.getType)
}
