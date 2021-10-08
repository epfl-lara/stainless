/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait TransformerWithType extends TreeTransformer {
  val s: Trees
  val t: Trees
  val symbols: s.Symbols
  import symbols.{given, _}

  private def getArithmeticType(lhs: s.Expr, expectedType: s.Type): s.Type = expectedType match {
    case s.AnyType() => lhs.getType
    case _ => expectedType
  }

  protected def widen(tpe: s.Type): s.Type = tpe match {
    case tp: s.TypeParameter =>
      import s._
      widen(tp.upperBound)
    case ta: s.TypeApply =>
      widen(ta.upperBound)
    case _ => tpe
  }

  def transform(pat: s.Pattern, tpe: s.Type): t.Pattern = pat match {
    case s.WildcardPattern(ob) => t.WildcardPattern(ob map transform).copiedFrom(pat)

    case s.InstanceOfPattern(ob, tpe) => t.InstanceOfPattern(ob map transform, transform(tpe)).copiedFrom(pat)

    case s.ClassPattern(ob, ct, subs) =>
      val rsubs = (subs zip ct.tcd.fields).map(p => transform(p._1, p._2.getType))
      t.ClassPattern(ob map transform, transform(ct).asInstanceOf[t.ClassType], rsubs).copiedFrom(pat)

    case s.ADTPattern(ob, id, tps, subs) =>
      val rsubs = (subs zip getConstructor(id, tps).fields).map(p => transform(p._1, p._2.getType))
      t.ADTPattern(ob map transform, id, tps map transform, rsubs).copiedFrom(pat)

    case s.TuplePattern(ob, subs) =>
      val tps = widen(tpe) match {
        case s.TupleType(tps) => tps
        case _ => subs map (_ => s.AnyType())
      }
      val rsubs = (subs zip tps).map(p => transform(p._1, p._2))
      t.TuplePattern(ob map transform, rsubs).copiedFrom(pat)

    case up @ s.UnapplyPattern(ob, recs, id, tps, subs) =>
      val rsubs = (subs zip up.subTypes(tpe)).map(p => transform(p._1, p._2))
      val rrecs = (recs zip getFunction(id, tps).params.init).map(p => transform(p._1, p._2.getType))
      t.UnapplyPattern(ob map transform, rrecs, id, tps map transform, rsubs).copiedFrom(pat)

    case s.LiteralPattern(ob, lit) =>
      t.LiteralPattern(ob map transform, transform(lit).asInstanceOf[t.Literal[_]]).copiedFrom(pat)
  }

  def transform(expr: s.Expr, tpe: s.Type): t.Expr = expr match {
    case s.Assume(pred, body) =>
      t.Assume(transform(pred, s.BooleanType()), transform(body, tpe)).copiedFrom(expr)

    case s.Let(vd, e, b) =>
      t.Let(transform(vd), transform(e, vd.getType), transform(b, tpe)).copiedFrom(expr)

    case s.Application(caller, args) =>
      val s.FunctionType(from, to) = widen(caller.getType)
      t.Application(
        transform(caller, s.FunctionType(from, tpe)),
        (args zip from) map (p => transform(p._1, p._2))
      ).copiedFrom(expr)

    case s.Lambda(args, body) => widen(tpe) match {
      case s.FunctionType(from, to) => t.Lambda(args map transform, transform(body, to)).copiedFrom(expr)
      case _ => t.Lambda(args map transform, transform(body, s.AnyType())).copiedFrom(expr)
    }

    case s.Forall(args, body) =>
      t.Forall(args map transform, transform(body, s.BooleanType())).copiedFrom(expr)

    case s.Choose(res, pred) =>
      t.Choose(transform(res), transform(pred, s.BooleanType())).copiedFrom(expr)

    case fi @ s.FunctionInvocation(id, tps, args) =>
      t.FunctionInvocation(id, tps map transform,
        (args zip fi.tfd.params.map(_.getType)) map (p => transform(p._1, p._2))).copiedFrom(expr)

    case s.IfExpr(cond, thenn, elze) =>
      t.IfExpr(transform(cond, s.BooleanType()), transform(thenn, tpe), transform(elze, tpe)).copiedFrom(expr)

    case s.ADT(id, tps, args) =>
      t.ADT(id, tps map transform,
        (args zip getConstructor(id, tps).fields.map(_.getType)) map (p => transform(p._1, p._2))).copiedFrom(expr)

    case s.IsConstructor(e, id) =>
      t.IsConstructor(transform(e), id).copiedFrom(expr)

    case s.ADTSelector(e, sel) =>
      t.ADTSelector(transform(e), sel).copiedFrom(expr)

    case s.Equals(lhs, rhs) =>
      val lub = widen(leastUpperBound(lhs.getType, rhs.getType))
      t.Equals(transform(lhs, lub), transform(rhs, lub)).copiedFrom(expr)

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
      val tp = widen(lhs.getType)
      t.LessThan(transform(lhs, tp), transform(rhs, tp)).copiedFrom(expr)

    case s.GreaterThan(lhs, rhs) =>
      val tp = widen(lhs.getType)
      t.GreaterThan(transform(lhs, tp), transform(rhs, tp)).copiedFrom(expr)

    case s.LessEquals(lhs, rhs) =>
      val tp = widen(lhs.getType)
      t.LessEquals(transform(lhs, tp), transform(rhs, tp)).copiedFrom(expr)

    case s.GreaterEquals(lhs, rhs) =>
      val tp = widen(lhs.getType)
      t.GreaterEquals(transform(lhs, tp), transform(rhs, tp)).copiedFrom(expr)

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
      t.BVNarrowingCast(transform(expr), transform(tpe).asInstanceOf[t.BVType]).copiedFrom(expr)

    case s.BVWideningCast(expr, tpe) =>
      t.BVWideningCast(transform(expr), transform(tpe).asInstanceOf[t.BVType]).copiedFrom(expr)

    case s.BVUnsignedToSigned(expr) =>
      t.BVUnsignedToSigned(transform(expr)).copiedFrom(expr)

    case s.BVSignedToUnsigned(expr) =>
      t.BVSignedToUnsigned(transform(expr)).copiedFrom(expr)

    case s.Tuple(es) => widen(tpe) match {
      case s.TupleType(tps) => t.Tuple((es zip tps) map (p => transform(p._1, p._2))).copiedFrom(expr)
      case _ => t.Tuple(es map (transform(_, s.AnyType()))).copiedFrom(expr)
    }

    case s.TupleSelect(tuple, index) =>
      t.TupleSelect(transform(tuple), index).copiedFrom(expr)

    case s.FiniteSet(elems, base) =>
      t.FiniteSet(elems map (transform(_, base)), transform(base)).copiedFrom(expr)

    case s.SetAdd(set, elem) =>
      val st @ s.SetType(base) = widen(set.getType)
      t.SetAdd(transform(set, st), transform(elem, base)).copiedFrom(expr)

    case s.ElementOfSet(elem, set) =>
      val st @ s.SetType(base) = widen(set.getType)
      t.ElementOfSet(transform(elem, base), transform(set, st)).copiedFrom(expr)

    case s.SubsetOf(s1, s2) =>
      val tp = widen(s1.getType)
      t.SubsetOf(transform(s1, tp), transform(s2, tp)).copiedFrom(expr)

    case s.SetIntersection(s1, s2) =>
      val tp = widen(s1.getType)
      t.SetIntersection(transform(s1, tp), transform(s2, tp)).copiedFrom(expr)

    case s.SetUnion(s1, s2) =>
      val tp = widen(s1.getType)
      t.SetUnion(transform(s1, tp), transform(s2, tp)).copiedFrom(expr)

    case s.SetDifference(s1, s2) =>
      val tp = widen(s1.getType)
      t.SetDifference(transform(s1, tp), transform(s2, tp)).copiedFrom(expr)

    case s.FiniteBag(elems, base) =>
      t.FiniteBag(
        elems.map(p => (transform(p._1, base), transform(p._2, s.IntegerType()))),
        transform(base)
      ).copiedFrom(expr)

    case s.BagAdd(bag, elem) =>
      val bt @ s.BagType(base) = widen(bag.getType)
      t.BagAdd(transform(bag, bt), transform(elem, base)).copiedFrom(expr)

    case s.MultiplicityInBag(elem, bag) =>
      val bt @ s.BagType(base) = widen(bag.getType)
      t.MultiplicityInBag(transform(elem, base), transform(bag, bt)).copiedFrom(expr)

    case s.BagIntersection(b1, b2) =>
      val tp = widen(b1.getType)
      t.BagIntersection(transform(b1, tp), transform(b2, tp)).copiedFrom(expr)

    case s.BagUnion(b1, b2) =>
      val tp = widen(b1.getType)
      t.BagUnion(transform(b1, tp), transform(b2, tp)).copiedFrom(expr)

    case s.BagDifference(b1, b2) =>
      val tp = widen(b1.getType)
      t.BagDifference(transform(b1, tp), transform(b2, tp)).copiedFrom(expr)

    case s.FiniteMap(pairs, dflt, kt, vt) =>
      t.FiniteMap(
        pairs map (p => (transform(p._1, kt), transform(p._2, vt))),
        transform(dflt, vt),
        transform(kt),
        transform(vt)
      ).copiedFrom(expr)

    case s.MapApply(map, key) =>
      val mt @ s.MapType(from, _) = widen(map.getType)
      t.MapApply(transform(map, mt), transform(key, from)).copiedFrom(expr)

    case s.MapUpdated(map, key, value) =>
      val mt @ s.MapType(from, to) = widen(map.getType)
      t.MapUpdated(transform(map, mt), transform(key, from), transform(value, to)).copiedFrom(expr)

    case s.MapMerge(mask, map1, map2) =>
      val mt @ s.MapType(from, to) = widen(map1.getType)
      t.MapMerge(transform(mask, s.SetType(from)), transform(map1, mt), transform(map2, mt))

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
      val stpe = widen(scrut.getType)
      t.MatchExpr(
        transform(scrut),
        cses map { case cse @ s.MatchCase(pat, guard, rhs) =>
          t.MatchCase(
            transform(pat, stpe),
            guard map (transform(_, s.BooleanType())),
            transform(rhs, tpe)
          ).copiedFrom(cse)
        }).copiedFrom(expr)

    case s.Passes(in, out, cses) =>
      val stpe = widen(in.getType)
      t.Passes(
        transform(in),
        transform(out),
        cses map { case cse @ s.MatchCase(pat, guard, rhs) =>
          t.MatchCase(
            transform(pat, stpe),
            guard map (transform(_, s.BooleanType())),
            transform(rhs, tpe)
          ).copiedFrom(cse)
        }).copiedFrom(expr)

    case s.FiniteArray(elems, base) =>
      t.FiniteArray(elems map (transform(_, base)), transform(base)).copiedFrom(expr)

    case s.LargeArray(elems, dflt, size, base) =>
      t.LargeArray(
        elems.view.mapValues (transform(_, base)).toMap,
        transform(dflt, base),
        transform(size, s.Int32Type()),
        transform(base)
      ).copiedFrom(expr)

    case s.ArraySelect(array, index) =>
      t.ArraySelect(transform(array), transform(index, s.Int32Type())).copiedFrom(expr)

    case s.ArrayUpdated(array, index, value) =>
      val at @ s.ArrayType(base) = widen(array.getType)
      t.ArrayUpdated(
        transform(array, at),
        transform(index, s.Int32Type()),
        transform(value, base)
      ).copiedFrom(expr)

    case s.ArrayLength(array) =>
      t.ArrayLength(transform(array)).copiedFrom(expr)

    // Inner function expressions
    case s.LetRec(fds, body) =>
      t.LetRec(
        fds.map { case lfd @ s.LocalFunDef(id, tparams, params, returnType, fullBody, flags) =>
          t.LocalFunDef(
            transform(id),
            tparams map transform,
            params map transform,
            transform(returnType),
            transform(fullBody, returnType.getType),
            flags map transform
          ).copiedFrom(lfd)
        },
        transform(body, tpe)
      ).copiedFrom(expr)

    case s.ApplyLetRec(id, tparams, tpe, tps, args) =>
      val s.FunctionType(from, _) = s.typeOps.instantiateType(tpe.getType, (tparams zip tps).toMap)
      t.ApplyLetRec(
        transform(id),
        tparams map (tp => transform(tp).asInstanceOf[t.TypeParameter]),
        transform(tpe).asInstanceOf[t.FunctionType],
        tps map transform,
        (args zip from) map (p => transform(p._1, p._2.getType))
      ).copiedFrom(expr)

    // OO expressions
    case s.ClassConstructor(ct, args) =>
      t.ClassConstructor(
        transform(ct).asInstanceOf[t.ClassType],
        (args zip ct.tcd.fields.map(_.getType)) map (p => transform(p._1, p._2))
      ).copiedFrom(expr)

    case s.ClassSelector(e, sel) =>
      t.ClassSelector(transform(e), sel).copiedFrom(expr)

    case s.IsInstanceOf(e, tp) =>
      t.IsInstanceOf(transform(e), transform(tp)).copiedFrom(expr)

    case s.AsInstanceOf(e, tp) =>
      t.AsInstanceOf(transform(e), transform(tp)).copiedFrom(expr)

    // Termination expressions
    case s.Decreases(measure, body) =>
      t.Decreases(transform(measure), transform(body, tpe)).copiedFrom(expr)

    case term: t.Terminal => super.transform(term)
  }

  override def transform(e: s.Expr): t.Expr = transform(e, e.getType)

  override def transform(tpe: s.Type): t.Type = tpe match {
    case s.RefinementType(vd, pred) =>
      t.RefinementType(transform(vd), transform(pred, s.BooleanType())).copiedFrom(tpe)
    case _ => super.transform(tpe)
  }
}
