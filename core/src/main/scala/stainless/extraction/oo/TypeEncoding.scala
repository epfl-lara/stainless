/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

import inox.utils.Graphs._
import java.util.concurrent.atomic.AtomicReference

trait TypeEncoding
  extends ExtractionPipeline
     with SimpleSorts
     with SimpleFunctions
     with oo.CachingPhase
     with utils.SyntheticSorts { self =>

  val s: Trees
  val t: Trees

  import t._
  import t.dsl._
  import s.TypeParameterWrapper


  /* ====================================
   *             IDENTIFIERS
   * ==================================== */

  private[this] class CachedID[T](builder: T => Identifier)
    extends utils.ConcurrentCached[T, Identifier](builder)

  private[this] val refID = FreshIdentifier("Object")
  private[this] def ref = T(refID)()

  private[this] val (int,  intValue)  = (FreshIdentifier("Integer"),   FreshIdentifier("value"))
  private[this] val (bool, boolValue) = (FreshIdentifier("Boolean"),   FreshIdentifier("value"))
  private[this] val (char, charValue) = (FreshIdentifier("Character"), FreshIdentifier("value"))
  private[this] val (real, realValue) = (FreshIdentifier("Real"),      FreshIdentifier("value"))
  private[this] val (str,  strValue)  = (FreshIdentifier("String"),    FreshIdentifier("value"))
  private[this] val (open, openValue) = (FreshIdentifier("Open"),      FreshIdentifier("value"))
  private[this] val (arr,  arrValue)  = (FreshIdentifier("Array"),     FreshIdentifier("value"))
  private[this] val (set,  setValue)  = (FreshIdentifier("Set"),       FreshIdentifier("value"))
  private[this] val (bag,  bagValue)  = (FreshIdentifier("Bag"),       FreshIdentifier("value"))
  private[this] val (map,  mapValue)  = (FreshIdentifier("Map"),       FreshIdentifier("value"))
  private[this] val unit = FreshIdentifier("Unit")

  private[this] val bv: ((Boolean, Int)) => Identifier = new CachedID[(Boolean, Int)]({
    case (signed, i) => FreshIdentifier((if (signed) "Signed" else "Unsigned") + "Bitvector" + i)
  })
  private[this] val bvValue: ((Boolean, Int)) => Identifier =
    new CachedID[(Boolean, Int)](_ => FreshIdentifier("value"))

  private[this] val tpl: Int => Identifier = new CachedID[Int](i => FreshIdentifier("Tuple" + i))
  private[this] val tplValue: Int => Identifier = new CachedID[Int](i => FreshIdentifier("value"))

  private[this] val fun: Int => Identifier = new CachedID[Int](i => FreshIdentifier("Function" + i))
  private[this] val funValue: Int => Identifier = new CachedID[Int](_ => FreshIdentifier("value"))

  private[this] val adt: Identifier => Identifier = new CachedID[Identifier](_.freshen)
  private[this] val adtValue: Identifier => Identifier = new CachedID[Identifier](_ => FreshIdentifier("value"))


  /* ====================================
   *          OBJECT TESTING
   * ==================================== */

  private[this] def isObject(tpe: s.Type)(implicit scope: Scope): Boolean = tpe match {
    case _: s.ClassType => true
    case s.NothingType() | s.AnyType() => true
    case s.TypeBounds(_, _) => true
    case tp: s.TypeParameter => scope.tparams contains tp
    case _ => false
  }

  private[this] def isSimple(tpe: s.Type)(implicit scope: Scope): Boolean = !s.typeOps.exists(isObject)(tpe)


  private[this] def simplify(lambda: t.Lambda): t.Expr = lambda match {
    case t.Lambda(Seq(vd), t.Application(f: t.Variable, Seq(v: t.Variable))) if vd.toVariable == v => f
    case _ => lambda
  }

  /* ====================================
   *      WRAPPING AND UNWRAPPING
   * ==================================== */

  private[this] def erased[T <: s.Type](tpe: T): T = {
    val s.NAryType(tps, recons) = tpe
    recons(tps.map(tp => s.AnyType().copiedFrom(tp))).copiedFrom(tpe).asInstanceOf[T]
  }

  private[this] def wrap(e: t.Expr, tpe: s.Type)(implicit scope: Scope): t.Expr = (tpe match {
    case s.AnyType() => e
    case s.ClassType(id, tps) => e
    case tp: s.TypeParameter => e
    case s.ADTType(id, tps) => C(adt(id))(convert(e, tpe, erased(tpe)))
    case s.RefinementType(vd, pred) => wrap(e, vd.tpe)
    case (_: s.PiType | _: s.SigmaType) => wrap(e, erased(tpe))
    case s.FunctionType(from, _) => C(fun(from.size))(convert(e, tpe, erased(tpe)))
    case s.TupleType(tps) => C(tpl(tps.size))(convert(e, tpe, erased(tpe)))
    case (_: s.ArrayType) => C(arr)(convert(e, tpe, erased(tpe)))
    case (_: s.SetType) => C(set)(convert(e, tpe, erased(tpe)))
    case (_: s.BagType) => C(bag)(convert(e, tpe, erased(tpe)))
    case (_: s.MapType) => C(map)(convert(e, tpe, erased(tpe)))
    case s.BVType(signed, size) => C(bv(signed -> size))(e)
    case s.IntegerType() => C(int)(e)
    case s.BooleanType() => C(bool)(e)
    case s.CharType() => C(char)(e)
    case s.RealType() => C(real)(e)
    case s.StringType() => C(str)(e)
    case s.UnitType() => t.ADT(unit, Seq(), Seq())
  }).copiedFrom(e)

  private[this] def unwrap(e: t.Expr, tpe: s.Type)(implicit scope: Scope): t.Expr = (tpe match {
    case s.AnyType() => e
    case s.ClassType(id, tps) => e
    case tp: s.TypeParameter => e
    case s.ADTType(id, tps) => convert(e.getField(adtValue(id)).copiedFrom(e), erased(tpe), tpe)
    case s.RefinementType(vd, pred) => unwrap(e, vd.tpe)
    case (_: s.PiType | _: s.SigmaType) => unwrap(e, erased(tpe))
    case s.FunctionType(from, _) => convert(e.getField(funValue(from.size)).copiedFrom(e), erased(tpe), tpe)
    case s.TupleType(tps) => convert(e.getField(tplValue(tps.size)).copiedFrom(e), erased(tpe), tpe)
    case (_: s.ArrayType) => convert(e.getField(arrValue).copiedFrom(e), erased(tpe), tpe)
    case (_: s.SetType) => convert(e.getField(setValue).copiedFrom(e), erased(tpe), tpe)
    case (_: s.BagType) => convert(e.getField(bagValue).copiedFrom(e), erased(tpe), tpe)
    case (_: s.MapType) => convert(e.getField(mapValue).copiedFrom(e), erased(tpe), tpe)
    case s.BVType(signed, size) => e.getField(bvValue(signed -> size))
    case s.IntegerType() => e.getField(intValue)
    case s.BooleanType() => e.getField(boolValue)
    case s.CharType() => e.getField(charValue)
    case s.RealType() => e.getField(realValue)
    case s.StringType() => e.getField(strValue)
    case s.UnitType() => t.UnitLiteral()
  }).copiedFrom(e)


  /* ====================================
   *          TYPE CONVERSIONS
   * ==================================== */

  private[this] val convertID = new CachedID[Identifier](id => FreshIdentifier("as" + id.name))

  private[this] def convert(e: t.Expr, tpe: s.Type, expected: s.Type)(implicit scope: Scope): t.Expr =
    ((e, tpe.getType(scope.symbols), expected.getType(scope.symbols)) match {
      case (_, t1, t2) if t1 == t2 => e
      case (_, t1, t2) if isObject(t1) && isObject(t2) => e
      case (_, t1, t2) if isObject(t1) && isSimple(t2) => unwrap(e, t2)
      case (_, t1, t2) if isSimple(t1) && isObject(t2) => wrap(e, t1)

      case (_, t1, t2) if scope.converters contains (t1 -> t2) =>
        t.Application(scope.converters(t1 -> t2), Seq(e))

      case (_, t1, t2) if scope.converters contains t2 =>
        t.Application(scope.converters(t2), Seq(wrap(e, t1)))

      case (_, s.ADTType(id1, tps1), s.ADTType(id2, tps2)) if id1 == id2 =>
        t.FunctionInvocation(convertID(id1), (tps1 ++ tps2).map(tp => scope.transform(tp)),
          e +: (tps1 zip tps2 flatMap { case (tp1, tp2) => Seq(
            simplify(\(("x" :: scope.transform(tp1)).copiedFrom(tp1))(x => convert(x, tp1, tp2)).copiedFrom(tp1)),
            simplify(\(("x" :: scope.transform(tp2)).copiedFrom(tp2))(x => convert(x, tp2, tp1)).copiedFrom(tp2))
          )}
        ))

      case (t.Lambda(params, body), s.FunctionType(from1, to1), s.FunctionType(from2, to2)) =>
        val newParams = (params zip from2) map { case (vd, tpe) => vd.copy(tpe = scope.transform(tpe)).copiedFrom(vd) }
        val unifiedParams = newParams zip (from1 zip from2) map { case (vd, (tp1, tp2)) => convert(vd.toVariable, tp2, tp1) }
        val newBody = convert(t.exprOps.replaceFromSymbols((params.map(_.toVariable) zip unifiedParams).toMap, body), to1, to2)
        t.Lambda(newParams, newBody)

      case (_, s.FunctionType(from1, to1), s.FunctionType(from2, to2)) =>
        val newParams = from2.map(tp => t.ValDef.fresh("x", scope.transform(tp), true).copiedFrom(tp))
        val unifiedParams = newParams zip (from1 zip from2) map { case (vd, (tp1, tp2)) => convert(vd.toVariable, tp2, tp1) }
        t.Lambda(newParams, convert(t.Application(e, unifiedParams).copiedFrom(e), to1, to2))

      case (t.Tuple(es), s.TupleType(tps1), s.TupleType(tps2)) =>
        t.Tuple(es zip (tps1 zip tps2) map { case (e, (tp1, tp2)) => convert(e, tp1, tp2) })

      case (_, s.TupleType(tps1), s.TupleType(tps2)) =>
        t.Tuple((tps1 zip tps2).zipWithIndex map {
          case ((tp1, tp2), i) => convert(t.TupleSelect(e, i + 1).copiedFrom(e), tp1, tp2)
        })

      case (t.FiniteArray(elems, _), s.ArrayType(b1), s.ArrayType(b2)) =>
        t.FiniteArray(elems.map(e => convert(e, b1, b2)), scope.transform(b2))

      case (t.LargeArray(elems, dflt, size, base), s.ArrayType(b1), s.ArrayType(b2)) =>
        t.LargeArray(elems.map(p => p._1 -> convert(p._2, b1, b2)),
          convert(dflt, b1, b2), size, scope.transform(b2))

      case (t.ArrayUpdated(a, i, v), s.ArrayType(b1), s.ArrayType(b2)) =>
        t.ArrayUpdated(convert(a, tpe, expected), i, convert(v, b1, b2))

      case (_, s.ArrayType(b1), s.ArrayType(b2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.Unchecked)).copiedFrom(e)) {
          res => forall(("i" :: t.Int32Type().copiedFrom(e)).copiedFrom(e)) {
            i => t.Equals(
              convert(t.ArraySelect(e, i).copiedFrom(e), b1, b2),
              t.ArraySelect(res, i).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case (t.FiniteSet(elems, _), s.SetType(b1), s.SetType(b2)) =>
        t.FiniteSet(elems.map(e => convert(e, b1, b2)), scope.transform(b2))

      case (t.SetAdd(set, elem), s.SetType(b1), s.SetType(b2)) =>
        t.SetAdd(convert(set, tpe, expected), convert(elem, b1, b2))

      case (t.SetIntersection(lhs, rhs), s.SetType(b1), s.SetType(b2)) =>
        t.SetIntersection(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.SetUnion(lhs, rhs), s.SetType(b1), s.SetType(b2)) =>
        t.SetUnion(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.SetDifference(lhs, rhs), s.SetType(b1), s.SetType(b2)) =>
        t.SetDifference(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (_, s.SetType(b1), s.SetType(b2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.Unchecked)).copiedFrom(e)) {
          res => forall(("x" :: scope.transform(b1)).copiedFrom(e)) {
            x => t.Equals(
              t.ElementOfSet(x, e).copiedFrom(e),
              t.ElementOfSet(convert(x, b1, b2), res).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case (t.FiniteBag(elems, _), s.BagType(b1), s.BagType(b2)) =>
        t.FiniteBag(elems.map(p => p._1 -> convert(p._2, b1, b2)), scope.transform(b2))

      case (t.BagAdd(bag, elem), s.BagType(b1), s.BagType(b2)) =>
        t.BagAdd(convert(bag, tpe, expected), convert(elem, b1, b2))

      case (t.BagIntersection(lhs, rhs), s.BagType(b1), s.BagType(b2)) =>
        t.BagIntersection(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.BagUnion(lhs, rhs), s.BagType(b1), s.BagType(b2)) =>
        t.BagUnion(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (t.BagDifference(lhs, rhs), s.BagType(b1), s.BagType(b2)) =>
        t.BagDifference(convert(lhs, tpe, expected), convert(rhs, tpe, expected))

      case (_, s.BagType(b1), s.BagType(b2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.Unchecked)).copiedFrom(e)) {
          res => forall(("x" :: scope.transform(b1)).copiedFrom(e)) {
            x => t.Equals(
              t.MultiplicityInBag(x, e).copiedFrom(e),
              t.MultiplicityInBag(convert(x, b1, b2), res).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case (t.FiniteMap(pairs, dflt, _, _), s.MapType(f1, t1), s.MapType(f2, t2)) =>
        t.FiniteMap(pairs.map(p => convert(p._1, f1, f2) -> convert(p._2, t1, t2)),
          convert(dflt, t1, t2), scope.transform(f2), scope.transform(t2))

      case (t.MapUpdated(m, k, v), s.MapType(f1, t1), s.MapType(f2, t2)) =>
        t.MapUpdated(convert(m, tpe, expected), convert(k, f1, f2), convert(v, t1, t2))

      case (_, s.MapType(f1, t1), s.MapType(f2, t2)) =>
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.Unchecked)).copiedFrom(e)) {
          res => forall(("x" :: scope.transform(f1)).copiedFrom(e)) {
            x => t.Equals(
              convert(t.MapApply(e, x).copiedFrom(e), t1, t2),
              t.MapApply(res, convert(x, f1, f2)).copiedFrom(e)
            ).copiedFrom(e)
          }.copiedFrom(e)
        }

      case _ => t.Choose(
        t.ValDef.fresh("res", scope.transform(expected)).copiedFrom(e),
        t.BooleanLiteral(false).copiedFrom(e)
      )
    }).copiedFrom(e)


  /* ====================================
   *          INSTANCE TESTS
   * ==================================== */

  private[this] val instanceID = new CachedID[Identifier](id => FreshIdentifier("is" + id.name))

  private[this] def instanceOf(e: t.Expr, in: s.Type, tpe: s.Type)(implicit scope: Scope): t.Expr =
    ((in, tpe) match {
      case (tp1, tp2) if (
        tp1 == tp2 &&
        !s.typeOps.typeParamsOf(tp2).exists { t2 =>
          (scope.testers contains t2) ||
          s.typeOps.typeParamsOf(tp1).exists { t1 =>
            scope.testers contains (t1 -> t2)
          }
        }
      ) => t.BooleanLiteral(true)

      case (tp1, tp2) if scope.testers contains (tp1 -> tp2) =>
        t.Application(scope.testers(tp1 -> tp2), Seq(e))

      case (tp1, tp2) if scope.testers contains tp2 =>
        t.Application(scope.testers(tp2), Seq(wrap(e, tp1)))

      case (_, s.AnyType()) => t.BooleanLiteral(true)
      case (_, s.NothingType()) => t.BooleanLiteral(false)
      case (s.RefinementType(vd, pred), _) => instanceOf(e, vd.tpe, tpe)

      case (_, s.RefinementType(vd, pred)) =>
        instanceOf(e, in, vd.tpe) &&
        t.Let(
          scope.transform(vd),
          convert(e, in, vd.tpe),
          scope.transform(pred, s.BooleanType().copiedFrom(pred))
        ).copiedFrom(e)

      case (_, s.ClassType(id, tps)) if isObject(in) =>
        t.FunctionInvocation(
          instanceID(id), Seq(),
          e +: tps.map(tp => simplify(\(("x" :: ref).copiedFrom(tp)) { x =>
            instanceOf(x, s.AnyType().copiedFrom(tp), tp)
          }.copiedFrom(tp)))
        )

      case (s.ADTType(id1, tps1), s.ADTType(id2, tps2)) if id1 == id2 =>
        t.FunctionInvocation(
          instanceID(id1), tps1 map (tp => scope.transform(tp)),
          e +: (tps1 zip tps2 map { case (tp1, tp2) =>
            simplify(\(("x" :: scope.transform(tp1)).copiedFrom(tp1)) { x =>
              instanceOf(x, tp1, tp2).copiedFrom(tp1)
            })
          })
        )

      case (_, s.ADTType(id, tps)) if isObject(in) =>
        (e is adt(id)).copiedFrom(e) &&
        instanceOf(e.getField(adtValue(id)).copiedFrom(e), erased(tpe), tpe)

      case (ft1 @ (_: s.FunctionType | _: s.PiType), ft2 @ (_: s.FunctionType | _: s.PiType)) =>
        def extract(tpe: s.Type): (Seq[s.ValDef], s.Type) = tpe match {
          case s.FunctionType(from, to) => (from.map(tp => s.ValDef.fresh("x", tp).copiedFrom(tp)), to)
          case s.PiType(params, to) => (params, to)
        }

        val (nparams1, to1) = extract(ft1)
        val (nparams2, to2) = extract(ft2)

        val paramsCond = t.andJoin(nparams1 zip nparams2 map { case (vd1, vd2) =>
          instanceOf(scope.transform(vd2.toVariable), vd2.tpe, vd1.tpe)
        }).copiedFrom(e)

        val toCond = (nparams1 zip nparams2).foldRight(
          instanceOf(t.Application(e, nparams1 map (vd => scope.transform(vd.toVariable))).copiedFrom(e), to1, to2)
        ) { case ((vd1, vd2), e) =>
          t.Let(scope.transform(vd1), convert(scope.transform(vd2.toVariable), vd2.tpe, vd1.tpe), e).copiedFrom(e)
        }

        t.Forall(nparams2.map(vd => scope.transform(vd)), t.Implies(paramsCond, toCond).copiedFrom(e))

      case (_, s.FunctionType(from, _)) if isObject(in) =>
        (e is fun(from.size)).copiedFrom(e) &&
        instanceOf(e.getField(funValue(from.size)).copiedFrom(e), erased(tpe), tpe)

      case (_, s.PiType(params, _)) if isObject(in) =>
        (e is fun(params.size)).copiedFrom(e) &&
        instanceOf(e.getField(funValue(params.size)).copiedFrom(e), erased(tpe), tpe)

      case (tt1 @ (_: s.TupleType | _: s.SigmaType), tt2 @ (_: s.TupleType | _: s.SigmaType)) =>
        def extract(tpe: s.Type): (Seq[s.ValDef], s.Type) = tpe match {
          case s.TupleType(from :+ to) => (from.map(tp => s.ValDef.fresh("x", tp).copiedFrom(tp)), to)
          case s.SigmaType(params, to) => (params, to)
        }

        val (nparams1, to1) = extract(tt1)
        val (nparams2, to2) = extract(tt2)

        val paramsCond = t.andJoin((nparams1 zip nparams2).zipWithIndex map { case ((vd1, vd2), i) =>
          instanceOf(t.TupleSelect(e, i + 1).copiedFrom(e), vd2.tpe, vd1.tpe)
        }).copiedFrom(e)

        val toCond = (nparams1 zip nparams2).zipWithIndex.foldRight(
          nparams1.zipWithIndex.foldRight(
            instanceOf(t.TupleSelect(e, nparams1.size + 1).copiedFrom(e), to1, to2)) {
              case ((vd, i), body) =>
                t.Let(scope.transform(vd), t.TupleSelect(e, i + 1).copiedFrom(e), body).copiedFrom(body)
          }
        ) { case (((vd1, vd2), i), body) =>
          t.Let(
            scope.transform(vd2),
            convert(t.TupleSelect(e, i + 1).copiedFrom(e), vd1.tpe, vd2.tpe),
            body
          ).copiedFrom(body)
        }

        t.and(paramsCond, toCond)

      case (_, s.TupleType(tpes)) if isObject(in) =>
        (e is tpl(tpes.size)).copiedFrom(e) &&
        instanceOf(e.getField(tplValue(tpes.size)).copiedFrom(e), erased(tpe), tpe)

      case (_, s.SigmaType(params, to)) =>
        (e is tpl(params.size + 1)).copiedFrom(e) &&
        instanceOf(e.getField(tplValue(params.size + 1)).copiedFrom(e), erased(tpe), tpe)

      case (s.ArrayType(b1), s.ArrayType(b2)) =>
        forall(("i" :: Int32Type().copiedFrom(e)).copiedFrom(e)) { i =>
          ((
            (t.Int32Literal(0).copiedFrom(e) <= i).copiedFrom(e) &&
            (i < t.ArrayLength(e).copiedFrom(e)).copiedFrom(e)
          ) ==> (
            instanceOf(t.ArraySelect(e, i).copiedFrom(e), b1, b2)
          )).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.ArrayType(_)) if isObject(in) =>
        (e is arr).copiedFrom(e) &&
        instanceOf(e.getField(arrValue).copiedFrom(e), erased(tpe), tpe)

      case (s.SetType(b1), s.SetType(b2)) =>
        forall(("x" :: scope.transform(b1)).copiedFrom(e)) { x =>
          (t.ElementOfSet(x, e).copiedFrom(e) ==> instanceOf(x, b1, b2)).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.SetType(_)) if isObject(in) =>
        (e is set).copiedFrom(e) &&
        instanceOf(e.getField(setValue).copiedFrom(e), erased(tpe), tpe)

      case (s.BagType(b1), s.BagType(b2)) =>
        forall(("x" :: scope.transform(b1)).copiedFrom(e)) { x =>
          ((
            (t.MultiplicityInBag(x, e).copiedFrom(e) > IntegerLiteral(0).copiedFrom(e)).copiedFrom(e)
          ) ==> (
            instanceOf(x, b1, b2)
          )).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.BagType(_)) if isObject(in) =>
        (e is bag).copiedFrom(e) &&
        instanceOf(e.getField(bagValue).copiedFrom(e), erased(tpe), tpe)

      case (s.MapType(f1, t1), s.MapType(f2, t2)) =>
        forall(("x" :: scope.transform(f1)).copiedFrom(e)) { x =>
          instanceOf(t.MapApply(e, x).copiedFrom(e), t1, t2)
        }

      case (_, s.MapType(_, _)) if isObject(in) =>
        (e is map).copiedFrom(e) &&
        instanceOf(e.getField(mapValue).copiedFrom(e), erased(tpe), tpe)

      case (_, s.BVType(signed, size)) if isObject(in) => e is bv(signed -> size)
      case (_, s.IntegerType()) if isObject(in) => e is int
      case (_, s.BooleanType()) if isObject(in) => e is bool
      case (_, s.CharType()) if isObject(in) => e is char
      case (_, s.RealType()) if isObject(in) => e is real
      case (_, s.StringType()) if isObject(in) => e is str
      case (_, s.UnitType()) if isObject(in) => e is unit
      case _ => t.BooleanLiteral(false)
    }).copiedFrom(e)


  /* ====================================
   *         UNAPPLY FUNCTIONS
   * ==================================== */

  private[this] val unapplyAnyCache = OptionSort.cached(new AtomicReference[t.FunDef])
  private[this] def unapplyAny(implicit symbols: s.Symbols): t.FunDef = {
    val cell = unapplyAnyCache.get
    val value = cell.get
    if (value != null) value
    else {
      import OptionSort.{value => _, _}
      val fd = mkFunDef(
        FreshIdentifier("InstanceOf"), t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get)
      )("A", "B") { case Seq(a, b) =>
        (Seq("p" :: (a =>: t.BooleanType()), "t" :: (a =>: b), "x" :: a), T(option)(b), { case Seq(p, t, x) =>
          if_ (p(x)) {
            C(some)(b)(t(x))
          } else_ {
            C(none)(b)()
          }
        })
      }

      if (cell.compareAndSet(value, fd)) fd
      else cell.get
    }
  }


  /* ====================================
   *     ADT INSTANCE & CONVERTERS
   * ==================================== */

  private class SortInfo(val functions: Seq[t.FunDef])

  private[this] val sortCache = new ExtractionCache[s.ADTSort, SortInfo]
  private[this] def sortInfo(id: Identifier)(implicit context: TransformerContext): SortInfo = {
    import context.{symbols, emptyScope => scope}
    val sort = symbols.getSort(id)
    sortCache.cached(sort, symbols) {
      val convertFunction: t.FunDef = {
        val (in, out) = (sort.typeArgs.map(_.freshen), sort.typeArgs.map(_.freshen))
        val tin = in.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])
        val tout = out.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])

        val x = "x" :: T(id)(tin: _*)
        val fs = tin zip tout flatMap { case (i, o) => Seq(i.id.name :: (i =>: o), i.id.name :: (o =>: i)) }

        val newScope = scope converting (in zip out zip fs.grouped(2).toSeq flatMap {
          case ((ti, to), Seq(vd1, vd2)) => Seq((ti, to) -> vd1.toVariable, (to, ti) -> vd2.toVariable)
        })

        val conversions = sort.typed(in).constructors zip sort.typed(out).constructors map { case (ci, co) =>
          (x.toVariable is ci.id, C(ci.id)(tout: _*)(ci.fields zip co.fields map { case (vi, vo) =>
            convert(x.toVariable.getField(vi.id), vi.tpe, vo.tpe)(newScope)
          }: _*))
        }

        val fullBody = conversions.init.foldRight(conversions.last._2: Expr) {
          case ((cond, thenn), elze) => t.IfExpr(cond, thenn, elze)
        }

        new t.FunDef(
          convertID(id), (tin ++ tout).map(t.TypeParameterDef(_)), x +: fs, T(id)(tout: _*), fullBody,
          Seq(t.Unchecked, t.Synthetic)
        ).setPos(sort)
      }

      val instanceFunction: t.FunDef = {
        val in = sort.typeArgs.map(_.freshen)
        val tin = in.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])

        val x = "x" :: T(id)(tin: _*)
        val fs = tin map { i => i.id.name :: (i =>: t.BooleanType()) }

        val newScope = scope testing (in zip fs map { case (ti, vd) => (ti, ti) -> vd.toVariable })
        val fullBody = t.orJoin(sort.typed(in).constructors map { cons =>
          (x.toVariable is cons.id) &&
          t.andJoin(cons.fields.map(vd => instanceOf(x.toVariable.getField(vd.id), vd.tpe, vd.tpe)(newScope)))
        })

        new t.FunDef(
          instanceID(id), tin.map(t.TypeParameterDef(_)), x +: fs, t.BooleanType(), fullBody,
          Seq(t.Unchecked, t.Synthetic)
        ).setPos(sort)
      }

      new SortInfo(Seq(convertFunction, instanceFunction))
    }
  }


  /* ====================================
   *    CLASS INSTANCE & CONVERTERS
   * ==================================== */

  private class ClassInfo(
    val constructors: Seq[Identifier],
    val unapplyFunction: Identifier,
    val functions: Seq[t.FunDef],
    val sorts: Seq[t.ADTSort]
  )

  private[this] val classCache = OptionSort.cached(new ExtractionCache[s.ClassDef, ClassInfo])
  private[this] def classInfo(id: Identifier)(implicit context: TransformerContext): ClassInfo = {
    import context.symbols
    val cd = symbols.getClass(id)
    classCache.get(symbols).cached(cd, symbols) {
      import OptionSort._

      val classes = cd +: cd.descendants
      val extraConstructors = classes
        .filter(cd => (cd.flags contains s.IsAbstract) && !(cd.flags contains s.IsSealed))
        .map(_.id)

      val instanceFunction = mkFunDef(instanceID(id), t.Unchecked, t.Synthetic)() { _ =>
        (("x" :: ref) +: cd.typeArgs.map(_.id.name :: (ref =>: BooleanType())), BooleanType(), {
          case x +: tps =>
            implicit val scope = context.emptyScope.testing(cd.typeArgs zip tps)
            if (cd.children.nonEmpty || extraConstructors.nonEmpty) {
              t.orJoin(
                cd.typed.children.map(ccd => instanceOf(x, cd.typed.toType, ccd.toType)) ++
                extraConstructors.map(t.IsConstructor(x, _))
              )
            } else {
              (x is cd.id) &&
              t.andJoin(cd.fields.map(vd => instanceOf(t.ADTSelector(x, vd.id), vd.tpe, vd.tpe)))
            }
        })
      }

      val constructors = classes.filterNot(_.flags contains s.IsAbstract).map(_.id) ++ extraConstructors

      val unapplyFunction = mkFunDef(
        cd.id.freshen, t.Unchecked, t.Synthetic, t.IsUnapply(isEmpty, get)
      )() { _ =>
        def condition(e: t.Expr): t.Expr = t.orJoin(constructors.map(t.IsConstructor(e, _)))

        val vd = t.ValDef.fresh("v", ref)
        val returnType = t.RefinementType(vd, condition(vd.toVariable))
        (Seq("x" :: ref), T(option)(returnType), { case Seq(x) =>
          if_ (condition(x)) {
            C(some)(returnType)(x)
          } else_ {
            C(none)(returnType)()
          }
        })
      }

      new ClassInfo(constructors, unapplyFunction.id,
        unapplyFunction +: instanceFunction +: OptionSort.functions, OptionSort.sorts)
    }
  }

  /* ====================================
   *   TRANFORMATION/ENCODING CONTEXT
   * ==================================== */

  protected case class FunInfo(fun: s.FunAbstraction, outer: Option[Scope], rewrite: Boolean)

  protected class ExprMapping private(underlying: Map[(s.Type, Option[s.Type]), t.Expr]) {
    def contains(p: (s.Type, s.Type)): Boolean = underlying contains (p._1 -> Some(p._2))
    def contains(tpe: s.Type): Boolean = underlying contains (tpe -> None)

    def apply(p: (s.Type, s.Type)): t.Expr = underlying apply (p._1 -> Some(p._2))
    def apply(tpe: s.Type): t.Expr = underlying apply (tpe -> None)

    def ++(ps: Traversable[((s.Type, s.Type), t.Expr)]): ExprMapping =
      new ExprMapping(underlying ++ ps.map { case ((t1, t2), e) => ((t1, Some(t2)), e) })
    def ++(ps: Traversable[(s.Type, t.Expr)])(implicit dummyImplicit: DummyImplicit): ExprMapping =
      new ExprMapping(underlying ++ ps.map { case (tpe, e) => ((tpe, None), e) })

    override def toString = underlying.toString
  }

  protected object ExprMapping {
    def empty: ExprMapping = new ExprMapping(Map.empty)
  }

  protected class Scope protected(
    val functions: Map[Identifier, FunInfo],
    graph: DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]],
    val tparams: Set[s.TypeParameter],
    val testers: ExprMapping,
    val converters: ExprMapping
  )(implicit val context: TransformerContext) extends TransformerWithType {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    implicit val symbols = context.symbols
    protected implicit val scope = this

    import symbols.{let => _, forall => _, _}

    def converting(ps: Traversable[((s.Type, s.Type), t.Expr)]): Scope =
      new Scope(functions, graph, tparams, testers, converters ++ ps)

    def testing(ps: Traversable[((s.Type, s.Type), t.Expr)]): Scope =
      new Scope(functions, graph, tparams, testers ++ ps, converters)
    def testing(ps: Traversable[(s.Type, t.Expr)])(implicit dummy: DummyImplicit): Scope =
      new Scope(functions, graph, tparams, testers ++ ps, converters)
    def testing(p: (s.Type, t.Expr)): Scope =
      new Scope(functions, graph, tparams, testers ++ Seq(p), converters)

    def rewrite(id: Identifier): Boolean = functions(id).rewrite

    override def transform(tp: s.Type): t.Type = tp match {
      case s.AnyType() => ref.copiedFrom(tp)
      case s.NothingType() =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.BooleanLiteral(false).copiedFrom(tp)
        }.copiedFrom(tp)

      case ct: s.ClassType =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => instanceOf(x, s.AnyType().copiedFrom(tp), ct)
        }.copiedFrom(tp)

      case s.TypeBounds(_, s.AnyType()) => ref.copiedFrom(tp)
      case s.TypeBounds(_, upperBound) =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => instanceOf(x, s.AnyType().copiedFrom(tp), upperBound)
        }.copiedFrom(tp)

      case tp: s.TypeParameter if tparams contains tp => ref.copiedFrom(tp)

      case tp: s.TypeParameter => super.transform(tp.copy(
        flags = tp.flags.filterNot { case (_: s.Variance | _: s.Bounds) => true case _ => false }
      ).copiedFrom(tp))

      case _ => super.transform(tp)
    }

    def withFunctions(funs: Seq[s.FunAbstraction]): Scope = {
      val funMap = funs.map(fun => fun.id -> fun).toMap

      def isSimpleFunction(fun: s.FunAbstraction): Boolean = {
        var simple: Boolean = true
        object traverser extends s.TreeTraverser {
          protected def traverse(pat: s.Pattern, in: s.Type): Unit = pat match {
            case s.WildcardPattern(_) =>
            case s.InstanceOfPattern(_, tpe) if !isSimple(leastUpperBound(in.getType, tpe)) => simple = false
            case s.ClassPattern(_, _, _) => simple = false
            case s.ADTPattern(ob, id, tps, subs) =>
              val tcons = getConstructor(id, tps)
              if (!isSimple(leastUpperBound(in, s.ADTType(tcons.sort.id, tps)))) simple = false
              else (subs zip tcons.fields).foreach(p => traverse(p._1, p._2.tpe))

            case s.TuplePattern(ob, subs) => in match {
              case s.TupleType(tps) if tps.size == subs.size =>
                (subs zip tps).foreach(p => traverse(p._1, p._2))
              case _ => simple = false
            }

            case up @ s.UnapplyPattern(ob, recs, id, tps, subs) =>
              (subs zip up.subTypes(in)) foreach (p => traverse(p._1, p._2))

            case s.LiteralPattern(_, lit) if !isSimple(leastUpperBound(in.getType, lit.getType)) => simple = false
            case _ =>
          }

          override def traverse(e: s.Expr): Unit = e match {
            case s.ClassConstructor(_, _) => simple = false
            case s.ClassSelector(_, _) => simple = false
            case s.MatchExpr(scrut, cases) => cases.foreach { case s.MatchCase(pat, _, _) => traverse(pat, scrut.getType) }
            case s.IsInstanceOf(e, tpe) if !isSimple(leastUpperBound(e.getType, tpe)) => simple = false
            case s.AsInstanceOf(e, tpe) if !isSimple(leastUpperBound(e.getType, tpe)) => simple = false
            case _ => super.traverse(e)
          }

          override def traverse(tpe: s.Type): Unit = tpe match {
            case _ if isObject(tpe) => simple = false
            case _ => super.traverse(tpe)
          }

          override def traverse(flag: s.Flag): Unit = flag match {
            case s.Bounds(_, _) => simple = false
            case _ => super.traverse(flag)
          }
        }

        fun.tparams.foreach(traverser.traverse)
        fun.params.foreach(traverser.traverse)
        traverser.traverse(fun.returnType)
        traverser.traverse(fun.fullBody)
        fun.flags.foreach(traverser.traverse)
        simple
      }

      var newGraph = graph
      for (fun1 <- funs; fun2 <- s.exprOps.collect {
        case s.FunInvocation(id, tps, args, _) if functions contains id => Set(functions(id).fun)
        case s.FunInvocation(id, tps, args, _) if funMap contains id => Set(funMap(id))
        case s.MatchExpr(_, cases) => cases.flatMap(cse => s.patternOps.collect {
          case s.UnapplyPattern(_, _, id, _, _) if functions contains id => Set(functions(id).fun)
          case s.UnapplyPattern(_, _, id, _, _) if funMap contains id => Set(funMap(id))
          case _ => Set[s.FunAbstraction]()
        } (cse.pattern)).toSet
        case _ => Set[s.FunAbstraction]()
      } (fun1.fullBody)) newGraph += SimpleEdge(fun1, fun2)

      val baseSimple = funs.filter(isSimpleFunction).toSet
      val fixSimple = inox.utils.fixpoint { (funs: Set[s.FunAbstraction]) =>
        funs.filter(fun => newGraph.transitiveSucc(fun) subsetOf funs)
      } (baseSimple ++ functions.values.collect { case FunInfo(fun, _, _) => fun })

      val newFunctions = functions ++ funs.map(fun => fun.id -> FunInfo(fun, Some(this), !fixSimple(fun)))

      new Scope(newFunctions, newGraph, tparams, testers, converters)
    }

    def in(id: Identifier): Scope = {
      val extraTParams = functions.get(id).map(_.fun.tparams.map(_.tp))
        .orElse(sorts.get(id).map(_.typeArgs))
        .getOrElse(classes(id).typeArgs)
      new Scope(functions, graph, tparams ++ extraTParams, testers, converters)
    }

    override def transform(e: s.Expr, inType: s.Type): t.Expr = e match {
      case s.ClassConstructor(ct, args) =>
        t.ADT(ct.id, Seq(), (erased(ct).tcd.fields zip args).map {
          case (vd, arg) => convert(transform(arg), arg.getType, vd.tpe)
        }).copiedFrom(e)

      case s.ClassSelector(expr, id) =>
        convert(t.ADTSelector(transform(expr), id).copiedFrom(e), e.getType, inType)

      case s.IsInstanceOf(expr, tpe) =>
        instanceOf(transform(expr), expr.getType, tpe).copiedFrom(e)

      case s.AsInstanceOf(expr, tpe) =>
        val vd = s.ValDef.fresh("x", expr.getType).copiedFrom(e)
        transform(
          s.Let(vd, expr, s.Assert(
            s.IsInstanceOf(vd.toVariable, tpe).copiedFrom(e),
            Some("Cast error"),
            vd.toVariable
          ).copiedFrom(e)).copiedFrom(e), inType)

      case fi @ s.FunctionInvocation(id, tps, args) if scope rewrite id =>
        val funScope = this in id
        convert(t.FunctionInvocation(id, Seq(),
          (tps map (tp => simplify(\(("x" :: ref).copiedFrom(tp)) {
            x => instanceOf(x, s.AnyType().copiedFrom(tp), tp)
          }.copiedFrom(tp)))) ++
          (getFunction(id).params zip args).map { case (vd, arg) =>
            convert(transform(arg), arg.getType, vd.tpe)(funScope)
          }).copiedFrom(e), e.getType, inType)

      case app @ s.ApplyLetRec(v, tparams, tps, args) if scope rewrite v.id =>
        val funScope = this in v.id
        val fun = functions(v.id).fun
        val vd @ t.ValDef(id, t.FunctionType(from, to), flags) = funScope.transform(v.toVal)
        val nvd = vd.copy(tpe = t.FunctionType(
          tparams.map(tp => (ref =>: t.BooleanType().copiedFrom(tp)).copiedFrom(tp)) ++ from,
          to
        ).copiedFrom(vd.tpe))

        convert(t.ApplyLetRec(nvd.toVariable, Seq(), Seq(),
          (tps map (tp => \(("x" :: ref).copiedFrom(tp)) {
            x => instanceOf(x, s.AnyType().copiedFrom(tp), tp)
          }.copiedFrom(tp))) ++
          (fun.params zip args).map { case (vd, arg) =>
            convert(transform(arg), arg.getType, vd.tpe)(funScope)
          }).copiedFrom(app), e.getType, inType)

      case app @ s.ApplyLetRec(v, tparams, tps, args) =>
        val outerScope = functions(v.id).outer.get
        val s.FunctionType(from, _) = s.typeOps.instantiateType(v.getType, (tparams zip tps).toMap)
        convert(t.ApplyLetRec(
          outerScope.transform(v.toVal).toVariable,
          tparams map (outerScope.transform(_).asInstanceOf[t.TypeParameter]),
          tps map transform,
          (args zip from) map (p => transform(p._1, p._2.getType))
        ).copiedFrom(e), app.getType, inType)

      case s.LetRec(fds, body) =>
        val funs = fds.map(fd => s.Inner(fd))
        val newScope = scope withFunctions funs
        val newFuns = funs.map(fun => newScope transform fun)
        val newBody = newScope.transform(body, inType)
        t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

      case e if isObject(e.getType) != isObject(inType) =>
        convert(transform(e), e.getType, inType)

      case _ =>
        super.transform(e, inType)
    }

    private def instanceOfPattern(inner: t.Pattern, in: s.Type, tpe: s.Type): t.Pattern =
      if (isSubtypeOf(in, tpe) && isObject(tpe) == isObject(in)) {
        inner
      } else {
        t.UnapplyPattern(
          None, Seq(
            \(("x" :: transform(in)).copiedFrom(inner))(x => instanceOf(x, in, tpe)).copiedFrom(inner),
            \(("x" :: transform(in)).copiedFrom(inner))(x => convert(x, in, tpe)).copiedFrom(inner)
          ), unapplyAny.id, Seq(transform(in), transform(tpe)), Seq(inner)
        ).copiedFrom(inner)
      }

    override def transform(pat: s.Pattern, tpe: s.Type): t.Pattern = pat match {
      case s.WildcardPattern(None) => t.WildcardPattern(None).copiedFrom(pat)
      case s.WildcardPattern(Some(vd)) if isObject(vd.tpe) && isObject(tpe) =>
        t.WildcardPattern(Some(transform(vd))).copiedFrom(pat)
      case s.WildcardPattern(Some(vd)) =>
        instanceOfPattern(t.WildcardPattern(Some(transform(vd))).copiedFrom(pat), tpe, vd.getType)

      case s.InstanceOfPattern(ob, tp) =>
        instanceOfPattern(t.WildcardPattern(ob map transform).copiedFrom(pat), tpe, tp)

      case s.ClassPattern(ob, ct, subs) => tpe match {
        case cti: s.ClassType if (
          (cti +: cti.tcd.descendants.map(_.toType)).exists(isSubtypeOf(_, ct)) &&
          (!(ct.tcd.cd.flags contains s.IsAbstract) && ct.tcd.children.isEmpty)
        ) =>
          t.ADTPattern(
            ob map transform, ct.id, Seq(),
            subs zip erased(ct).tcd.fields map { case (sub, vd) => transform(sub, vd.getType) }
          ).copiedFrom(pat)

        case _ =>
          instanceOfPattern(t.UnapplyPattern(
            ob map transform, Seq(), classInfo(ct.id).unapplyFunction, Seq(),
            subs zip erased(ct).tcd.fields map { case (sub, vd) => transform(sub, vd.getType) }
          ).copiedFrom(pat), tpe, ct)
      }

      case s.ADTPattern(ob, id, tps, subs) =>
        val sort = s.ADTType(getConstructor(id).sort, tps).copiedFrom(tpe)
        instanceOfPattern(super.transform(pat, sort), tpe, sort)

      case s.TuplePattern(None, subs) => tpe match {
        case s.TupleType(tps) if subs.size == tps.size => super.transform(pat, tpe)
        case _ =>
          val tt = s.TupleType(subs.map(sub => s.AnyType().copiedFrom(sub))).copiedFrom(pat)
          instanceOfPattern(super.transform(pat, tt), tpe, tt)
      }

      case s.TuplePattern(Some(vd), _) =>
        instanceOfPattern(super.transform(pat, vd.tpe), tpe, vd.tpe)

      case up @ s.UnapplyPattern(ob, recs, id, tps, subs) =>
        if (rewrite(id)) {
          val funScope = this in id
          val newRecs = tps.flatMap(tp => Seq(
            \(("x" :: ref).copiedFrom(tp))(x => instanceOf(x, s.AnyType().copiedFrom(tp), tp)).copiedFrom(tp),
            \(("x" :: ref).copiedFrom(tp))(x => unwrap(x, tp)).copiedFrom(tp)
          )) ++ (recs zip getFunction(id).params.init).map {
            case (r, vd) => convert(transform(r), r.getType, vd.tpe)(funScope)
          }

          t.UnapplyPattern(
            ob map transform, newRecs, id, Seq(),
            subs zip up.subTypes(tpe) map (p => transform(p._1, p._2))
          ).copiedFrom(pat)
        } else {
          super.transform(pat, tpe)
        }

      case s.LiteralPattern(ob, lit) =>
        instanceOfPattern(super.transform(pat, lit.getType), tpe, lit.getType)
    }

    override def transform(fd: s.FunDef): t.FunDef = transform(s.Outer(fd)).toFun

    def transform(fd: s.FunAbstraction): t.FunAbstraction = {
      if (!rewrite(fd.id)) {
        fd.to(t)(
          fd.id,
          fd.tparams map (scope.transform(_)),
          fd.params map (scope.transform(_)),
          scope.transform(fd.returnType),
          scope.transform(fd.fullBody, fd.returnType.getType),
          fd.flags map (scope.transform(_))
        )
      } else {
        val (scope, tparamParams) = fd.tparams.map(_.tp).foldLeft((this in fd.id, Seq[t.ValDef]())) {
          case ((scope, vds), tp) =>
            val s.TypeBounds(lowerBound, upperBound) = tp.bounds

            val tpe = if (lowerBound == s.NothingType() && upperBound == s.AnyType()) {
              (ref.copiedFrom(tp) =>: t.BooleanType().copiedFrom(tp)).copiedFrom(tp)
            } else {
              pi(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) { x =>
                refinement(("b" :: t.BooleanType().copiedFrom(tp)).copiedFrom(tp)) { b =>
                  t.Annotated(t.and(
                    t.implies(instanceOf(x, tp, lowerBound)(scope), b).copiedFrom(lowerBound),
                    t.implies(b, instanceOf(x, tp, upperBound)(scope)).copiedFrom(upperBound)
                  ).copiedFrom(tp), Seq(t.Unchecked)).copiedFrom(tp)
                }.copiedFrom(tp)
              }.copiedFrom(tp)
            }

            val vd = t.ValDef(tp.id.freshen, tpe).copiedFrom(tp)
            (scope.testing(tp -> vd.toVariable), vds :+ vd)
        }

        fd.to(t)(
          fd.id,
          Seq(),
          tparamParams ++ fd.params.map(scope.transform(_)),
          scope.transform(fd.returnType),
          scope.transform(fd.fullBody, fd.returnType.getType),
          fd.flags map scope.transform
        )
      }
    }
  }

  private[this] object Scope {
    def empty(implicit context: TransformerContext): Scope = new Scope(
      Map.empty, new DiGraph[s.FunAbstraction, SimpleEdge[s.FunAbstraction]],
      Set.empty, ExprMapping.empty, ExprMapping.empty
    ) withFunctions context.symbols.functions.values.map(s.Outer(_)).toSeq
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit val symbols: s.Symbols) {
    implicit val emptyScope = Scope.empty(this)

    private val (tplSizes, funSizes, bvSizes) = {
      var tplSizes: Set[Int] = Set.empty
      var funSizes: Set[Int] = Set.empty
      var bvSizes: Set[(Boolean, Int)] = Set.empty

      object traverser extends s.TreeTraverser {
        override def traverse(pat: s.Pattern): Unit = pat match {
          case s.TuplePattern(_, subs) => tplSizes += subs.size; super.traverse(pat)
          case _ => super.traverse(pat)
        }

        override def traverse(tpe: s.Type): Unit = tpe match {
          case s.TupleType(tps) => tplSizes += tps.size; super.traverse(tpe)
          case s.SigmaType(params, _) => tplSizes += params.size + 1; super.traverse(tpe)
          case s.FunctionType(from, _) => funSizes += from.size; super.traverse(tpe)
          case s.PiType(params, _) => funSizes += params.size; super.traverse(tpe)
          case s.BVType(signed, size) => bvSizes += (signed -> size); super.traverse(tpe)
          case _ => super.traverse(tpe)
        }

        override def traverse(expr: s.Expr): Unit = expr match {
          case s.Tuple(es) => tplSizes += es.size; super.traverse(expr)
          case s.Lambda(params, _) => funSizes += params.size; super.traverse(expr)
          case s.BVLiteral(signed, _, size) => bvSizes += (signed -> size); super.traverse(expr)
          case _ => super.traverse(expr)
        }
      }

      emptyScope.functions.values
        .collect { case FunInfo(fun, _, true) => fun }
        .foreach { fun =>
          fun.tparams.foreach(traverser.traverse)
          fun.params.foreach(traverser.traverse)
          traverser.traverse(fun.returnType)
          traverser.traverse(fun.fullBody)
          fun.flags.foreach(traverser.traverse)
        }

      (tplSizes, funSizes, bvSizes)
    }

    val refSort = new t.ADTSort(refID, Seq(),
      symbols.classes.values.toSeq.flatMap { cd =>
        if ((cd.flags contains s.IsAbstract) && !(cd.flags contains s.IsSealed)) {
          val field = t.ValDef(FreshIdentifier("x"), t.IntegerType().copiedFrom(cd)).copiedFrom(cd)
          Some(new t.ADTConstructor(cd.id, refID, Seq(field)).copiedFrom(cd))
        } else if (cd.children.isEmpty) {
          val anys = cd.typeArgs.map(tp => s.AnyType().copiedFrom(tp))
          val fields = cd.typed(anys).fields.map(emptyScope.transform _)
          Some(new t.ADTConstructor(cd.id, refID, fields).copiedFrom(cd))
        } else {
          None
        }
      } ++ symbols.sorts.values.toSeq.map { sort =>
        new t.ADTConstructor(adt(sort.id), refID, Seq(t.ValDef(
          adtValue(sort.id),
          t.ADTType(sort.id, sort.typeArgs.map(tp => ref.copiedFrom(tp))).copiedFrom(sort)
        ).copiedFrom(sort))).copiedFrom(sort)
      } ++ funSizes.map { i =>
        new t.ADTConstructor(fun(i), refID, Seq(t.ValDef(funValue(i), t.FunctionType((1 to i).map(_ => ref), ref))))
      } ++ tplSizes.map { i =>
        new t.ADTConstructor(tpl(i), refID, Seq(t.ValDef(tplValue(i), t.TupleType((1 to i).map(_ => ref)))))
      } ++ bvSizes.map { case ss @ (signed, size) =>
        new t.ADTConstructor(bv(ss), refID, Seq(t.ValDef(bvValue(ss), t.BVType(signed, size))))
      } ++ Seq(
        new t.ADTConstructor(int,  refID, Seq(t.ValDef(intValue,  t.IntegerType()))),
        new t.ADTConstructor(bool, refID, Seq(t.ValDef(boolValue, t.BooleanType()))),
        new t.ADTConstructor(char, refID, Seq(t.ValDef(charValue, t.CharType()))),
        new t.ADTConstructor(real, refID, Seq(t.ValDef(realValue, t.RealType()))),
        new t.ADTConstructor(str,  refID, Seq(t.ValDef(strValue,  t.StringType()))),
        new t.ADTConstructor(arr,  refID, Seq(t.ValDef(arrValue,  t.ArrayType(ref)))),
        new t.ADTConstructor(set,  refID, Seq(t.ValDef(setValue,  t.SetType(ref)))),
        new t.ADTConstructor(bag,  refID, Seq(t.ValDef(bagValue,  t.BagType(ref)))),
        new t.ADTConstructor(map,  refID, Seq(t.ValDef(mapValue,  t.MapType(ref, ref)))),
        new t.ADTConstructor(unit, refID, Seq()),
        new t.ADTConstructor(open, refID, Seq(t.ValDef(openValue, t.IntegerType())))
      ), Seq(t.Uncached, t.Synthetic))

    def transform(fd: s.FunDef): t.FunDef = emptyScope.transform(fd)

    def transform(sort: s.ADTSort): t.ADTSort = emptyScope.transform(sort)

    def functions: Seq[t.FunDef] =
      symbols.classes.keys.toSeq.flatMap(id => classInfo(id)(this).functions) ++
      symbols.sorts.keys.flatMap(id => sortInfo(id)(this).functions) ++
      OptionSort.functions :+ unapplyAny

    def sorts: Seq[t.ADTSort] =
      symbols.classes.keys.toSeq.flatMap(id => classInfo(id)(this).sorts) ++
      OptionSort.sorts :+ refSort
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val newSymbols = super.extractSymbols(context, symbols)
      .withFunctions(context.functions)
      .withSorts(context.sorts)

    newSymbols.ensureWellFormed

    val dependencies: Set[Identifier] =
      (symbols.functions.keySet ++ symbols.sorts.keySet)
        .flatMap(id => newSymbols.dependencies(id) + id)

    val independentSymbols = t.NoSymbols
      .withFunctions(newSymbols.functions.values.toSeq.filter(fd => dependencies(fd.id)))
      .withSorts(newSymbols.sorts.values.toSeq.filter(sort => dependencies(sort.id)))

    independentSymbols.ensureWellFormed

    val constructors: Set[Identifier] = {
      import independentSymbols._

      var constructors: Set[Identifier] = Set.empty
      val traverser = new t.TreeTraverser {
        override def traverse(expr: t.Expr): Unit = expr match {
          case t.IsTyped(t.ADT(id, tps, es), t.ADTType(`refID`, _)) => constructors += id; super.traverse(expr)
          case t.IsConstructor(t.IsTyped(e, t.ADTType(`refID`, _)), id) => constructors += id; super.traverse(expr)
          case t.ADTSelector(t.IsTyped(e, t.ADTType(`refID`, _)), id) => constructors += id; super.traverse(expr)
          case _ => super.traverse(expr)
        }

        override def traverse(pat: t.Pattern): Unit = pat match {
          case t.ADTPattern(_, id, _, _) if getConstructor(id).sort == refID => constructors += id; super.traverse(pat)
          case _ => super.traverse(pat)
        }
      }

      independentSymbols.functions.values.foreach(traverser.traverse)
      independentSymbols.sorts.values.foreach(traverser.traverse)
      constructors
    }

    val result = t.NoSymbols
      .withFunctions(independentSymbols.functions.values.toSeq)
      .withSorts(independentSymbols.sorts.values.toSeq)
      .withSorts(Seq(new t.ADTSort(refID, Seq(), // overrides refSort in `independentSymbols.sorts`
        context.refSort.constructors.filter(cons => cons.id == open || constructors(cons.id)),
        context.refSort.flags)
      ))

    result.ensureWellFormed
    result
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = context.transform(fd)
  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)

  // Classes are simply dropped by this extraction phase
  override protected type ClassResult = Unit
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult = ()
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[Unit]): t.Symbols = symbols
}

object TypeEncoding {
  def apply(ts: Trees, tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new {
    override val s: ts.type = ts
    override val t: tt.type = tt
  } with TypeEncoding {
    override val context = ctx
  }
}
