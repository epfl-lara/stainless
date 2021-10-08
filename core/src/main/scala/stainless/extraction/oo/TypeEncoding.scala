/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

class TypeEncoding(override val s: Trees, override val t: Trees)
                  (using override val context: inox.Context)
  extends ExtractionPipeline
     with SimpleSorts
     with oo.CachingPhase
     with utils.SyntheticSorts { self =>

  import t._
  import t.dsl._

  override type FunctionResult = Seq[t.FunDef]
  protected def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols =
    symbols.withFunctions(functions.flatten)

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

  private[this] def isObject(tpe: s.Type)(using scope: Scope): Boolean = tpe match {
    case _: s.ClassType => true
    case s.NothingType() | s.AnyType() => true
    case s.UnknownType(_) => true
    case s.TypeBounds(_, _, _) => true
    case tp: s.TypeParameter => scope.tparams contains tp
    case ta: s.TypeApply => ta.isAbstract(using scope.symbols)
    case _ => false
  }

  private[this] def isSimple(tpe: s.Type)(using Scope): Boolean = !s.typeOps.exists(isObject)(tpe)


  private[this] def simplify(lambda: t.Lambda): t.Expr = lambda match {
    case t.Lambda(Seq(vd), t.Application(f: t.Variable, Seq(v: t.Variable))) if vd.toVariable == v => f
    case _ => lambda
  }

  /* ====================================
   *      WRAPPING AND UNWRAPPING
   * ==================================== */

  private[this] def getRefField(e: t.Expr, id: Identifier): t.Expr = e match {
    case v: t.Variable => t.Annotated(e.getField(id).copiedFrom(e), Seq(DropVCs)).copiedFrom(e)
    case _ => let(("x" :: ref.copiedFrom(e)).copiedFrom(e), e) { x =>
      t.Annotated(x.getField(id).copiedFrom(e), Seq(DropVCs)).copiedFrom(e)
    }.copiedFrom(e)
  }

  private[this] def erased[T <: s.Type](tpe: T): T = {
    val s.NAryType(tps, recons) = tpe
    recons(tps.map(tp => s.AnyType().copiedFrom(tp))).copiedFrom(tpe).asInstanceOf[T]
  }

  private[this] def erasedBy(tpe: s.Type)(using scope: Scope): s.Type = s.typeOps.postMap {
    case tp: s.TypeParameter if scope.tparams contains tp => Some(s.AnyType().copiedFrom(tp))
    case tb @ s.TypeBounds(s.NothingType(), s.AnyType(), _) => Some(s.AnyType().copiedFrom(tb))
    case _ => None
  } (tpe)

  private[this] def wrap(e: t.Expr, tpe: s.Type)(using Scope): t.Expr = (tpe match {
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
    case s.UnitType() => let(("u" :: t.UnitType()).copiedFrom(e), e) { _ => t.ADT(unit, Seq(), Seq()).copiedFrom(e) }
  }).copiedFrom(e)

  private[this] def unwrap(e: t.Expr, tpe: s.Type)(using Scope): t.Expr = (tpe match {
    case s.AnyType() => e
    case s.ClassType(id, tps) => e
    case tp: s.TypeParameter => e
    case s.ADTType(id, tps) => convert(getRefField(e, adtValue(id)), erased(tpe), tpe)
    case s.RefinementType(vd, pred) => unwrap(e, vd.tpe)
    case (_: s.PiType | _: s.SigmaType) => unwrap(e, erased(tpe))
    case s.FunctionType(from, _) => convert(getRefField(e, funValue(from.size)), erased(tpe), tpe)
    case s.TupleType(tps) => convert(getRefField(e, tplValue(tps.size)), erased(tpe), tpe)
    case (_: s.ArrayType) => convert(getRefField(e, arrValue), erased(tpe), tpe)
    case (_: s.SetType) => convert(getRefField(e, setValue), erased(tpe), tpe)
    case (_: s.BagType) => convert(getRefField(e, bagValue), erased(tpe), tpe)
    case (_: s.MapType) => convert(getRefField(e, mapValue), erased(tpe), tpe)
    case s.BVType(signed, size) => getRefField(e, bvValue(signed -> size))
    case s.IntegerType() => getRefField(e, intValue)
    case s.BooleanType() => getRefField(e, boolValue)
    case s.CharType() => getRefField(e, charValue)
    case s.RealType() => getRefField(e, realValue)
    case s.StringType() => getRefField(e, strValue)
    case s.UnitType() => let(("u" :: ref.copiedFrom(e)).copiedFrom(e), e) { _ => t.UnitLiteral().copiedFrom(e) }
  }).copiedFrom(e)


  /* ====================================
   *          TYPE CONVERSIONS
   * ==================================== */

  private[this] val convertID = new CachedID[Identifier](id => FreshIdentifier("as" + id.name))

  private[this] def convert(e: t.Expr, tpe: s.Type, expected: s.Type)(using scope: Scope): t.Expr = {
    val t1 = tpe.getType(using scope.symbols)
    val t2 = expected.getType(using scope.symbols)

    ((e, t1, t2) match {
      case (_, t1, t2) if erasedBy(t1) == erasedBy(t2) => e
      case (_, t1, t2) if isObject(t1) && isObject(t2) => e

      case (e, s.NothingType(), t2) if !isObject(t2) =>
        t.Error(scope.transform(t2), e match {
          case t.Error(_, descr) => descr
          case _ => s"Expression of type Nothing: ${e.toString}"
        })

      case (_, t1, t2) if isObject(t1) && !isObject(t2) => unwrap(e, t2)
      case (_, t1, t2) if !isObject(t1) && isObject(t2) => wrap(e, t1)

      case (_, t1, t2) if scope.converters contains (t1 -> t2) =>
        t.Application(scope.converters(t1 -> t2), Seq(e))

      case (_, t1, t2) if scope.converters contains t2 =>
        t.Application(scope.converters(t2), Seq(wrap(e, t1)))

      case (_, s.RefinementType(vd, pred), t2) =>
        convert(e, vd.tpe, t2)

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
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
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
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
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
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
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
        choose(t.ValDef(FreshIdentifier("res"), scope.transform(expected), Seq(t.DropVCs)).copiedFrom(e)) {
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
  }


  /* ====================================
   *          INSTANCE TESTS
   * ==================================== */

  private[this] val instanceID = new CachedID[Identifier](id => FreshIdentifier("is" + id.name))

  private[this] def instanceOf(e: t.Expr, in: s.Type, tpe: s.Type)(using scope: Scope): t.Expr = {
    ((in.getType(using scope.symbols), tpe.getType(using scope.symbols)) match {
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

      case (_, s.UnknownType(_)) => t.BooleanLiteral(true)

      case (s.TypeBounds(_, hi, _), _) => instanceOf(e, hi, tpe)
      case (_, s.TypeBounds(_, hi, _)) => instanceOf(e, in, hi)

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
        instanceOf(getRefField(e, adtValue(id)), erased(tpe), tpe)

      case (ft1 @ (_: s.FunctionType | _: s.PiType), ft2 @ (_: s.FunctionType | _: s.PiType)) =>
        def extract(tpe: s.Type): (Seq[s.ValDef], s.Type) = tpe match {
          case s.FunctionType(from, to) => (from.map(tp => s.ValDef.fresh("x", tp, true).copiedFrom(tp)), to)
          case s.PiType(params, to) => (params, to)
        }

        val (nparams1, to1) = extract(ft1)
        val (nparams2, to2) = extract(ft2)

        val paramsCond = t.andJoin(nparams1 zip nparams2 map { case (vd1, vd2) =>
          instanceOf(scope.transform(vd2.toVariable), vd2.tpe, vd1.tpe)
        }).copiedFrom(e)

        val app = t.Application(e, nparams1 map (vd => scope.transform(vd.toVariable))).copiedFrom(e)
        val toCond = (nparams1 zip nparams2).foldRight(instanceOf(app, to1, to2)) { case ((vd1, vd2), e) =>
          val nvd1 = scope.transform(vd1)
          if (t.exprOps.variablesOf(e) contains nvd1.toVariable) {
            t.Let(nvd1, convert(scope.transform(vd2.toVariable), vd2.tpe, vd1.tpe), e).copiedFrom(e)
          } else {
            e
          }
        }

        t.Forall(nparams2.map(vd => scope.transform(vd)), t.Implies(paramsCond, toCond).copiedFrom(e))

      case (_, s.FunctionType(from, _)) if isObject(in) =>
        (e is fun(from.size)).copiedFrom(e) &&
        instanceOf(getRefField(e, funValue(from.size)), erased(tpe), tpe)

      case (_, s.PiType(params, _)) if isObject(in) =>
        (e is fun(params.size)).copiedFrom(e) &&
        instanceOf(getRefField(e, funValue(params.size)), erased(tpe), tpe)

      case (tt1 @ (_: s.TupleType | _: s.SigmaType), tt2 @ (_: s.TupleType | _: s.SigmaType)) =>
        def extract(tpe: s.Type): (Seq[s.ValDef], s.Type) = tpe match {
          case s.TupleType(from :+ to) => (from.map(tp => s.ValDef.fresh("x", tp, true).copiedFrom(tp)), to)
          case s.SigmaType(params, to) => (params, to)
        }

        val (nparams1, to1) = extract(tt1)
        val (nparams2, to2) = extract(tt2)

        val paramsCond = t.andJoin((nparams1 zip nparams2).zipWithIndex map { case ((vd1, vd2), i) =>
          instanceOf(t.TupleSelect(e, i + 1).copiedFrom(e), vd1.tpe, vd2.tpe)
        }).copiedFrom(e)

        val innerCond = instanceOf(t.TupleSelect(e, nparams1.size + 1).copiedFrom(e), to1, to2)

        val wrappedCond1 = nparams1.zipWithIndex.foldRight(innerCond) { case ((vd, i), body) =>
          val nvd = scope.transform(vd)
          if (t.exprOps.variablesOf(body) contains nvd.toVariable) {
            t.Let(nvd, t.TupleSelect(e, i + 1).copiedFrom(e), body).copiedFrom(body)
          } else {
            body
          }
        }

        val toCond = (nparams1 zip nparams2).zipWithIndex.foldRight(wrappedCond1) { case (((vd1, vd2), i), body) =>
          val nvd2 = scope.transform(vd2)
          if (t.exprOps.variablesOf(body) contains nvd2.toVariable) {
            t.Let(nvd2, convert(t.TupleSelect(e, i + 1).copiedFrom(e), vd1.tpe, vd2.tpe), body).copiedFrom(body)
          } else {
            body
          }
        }

        t.and(paramsCond, toCond)

      case (_, s.TupleType(tpes)) if isObject(in) =>
        (e is tpl(tpes.size)).copiedFrom(e) &&
        instanceOf(getRefField(e, tplValue(tpes.size)), erased(tpe), tpe)

      case (_, s.SigmaType(params, to)) =>
        (e is tpl(params.size + 1)).copiedFrom(e) &&
        instanceOf(getRefField(e, tplValue(params.size + 1)), erased(tpe), tpe)

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
        instanceOf(getRefField(e, arrValue), erased(tpe), tpe)

      case (s.SetType(b1), s.SetType(b2)) =>
        forall(("x" :: scope.transform(b1)).copiedFrom(e)) { x =>
          (t.ElementOfSet(x, e).copiedFrom(e) ==> instanceOf(x, b1, b2)).copiedFrom(e)
        }.copiedFrom(e)

      case (_, s.SetType(_)) if isObject(in) =>
        (e is set).copiedFrom(e) &&
        instanceOf(getRefField(e, setValue), erased(tpe), tpe)

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
        instanceOf(getRefField(e, bagValue), erased(tpe), tpe)

      case (s.MapType(f1, t1), s.MapType(f2, t2)) =>
        forall(("x" :: scope.transform(f1)).copiedFrom(e)) { x =>
          instanceOf(t.MapApply(e, x).copiedFrom(e), t1, t2)
        }

      case (_, s.MapType(_, _)) if isObject(in) =>
        (e is map).copiedFrom(e) &&
        instanceOf(getRefField(e, mapValue), erased(tpe), tpe)

      case (_, s.BVType(signed, size)) if isObject(in) => e is bv(signed -> size)
      case (_, s.IntegerType()) if isObject(in) => e is int
      case (_, s.BooleanType()) if isObject(in) => e is bool
      case (_, s.CharType()) if isObject(in) => e is char
      case (_, s.RealType()) if isObject(in) => e is real
      case (_, s.StringType()) if isObject(in) => e is str
      case (_, s.UnitType()) if isObject(in) => e is unit
      case _ => t.BooleanLiteral(false)
    }).copiedFrom(e)
  }


  /* ====================================
   *           CLASS INSTANCE
   * ==================================== */

  private[this] def constructors(cd: s.ClassDef)(using s.Symbols): Seq[Identifier] =
    (cd +: cd.descendants).filterNot(_.flags contains s.IsAbstract).map(_.id)

  private[this] def constructors(id: Identifier)(using symbols: s.Symbols): Seq[Identifier] =
    constructors(symbols.getClass(id))

  // The class instance function depends on the current class as well as its children on
  // which the `instanceOf` call well be recursively performed, so the cache key consists of
  // - the class definition
  // - the children class definitions
  private[this] val classInstanceCache = new ExtractionCache[s.ClassDef, t.FunDef]({
    (cd, context) => ClassKey(cd) + SetKey(cd.children(using context.symbols).toSet)
  })

  private[this] def classInstance(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.symbols
    import symbols.{given, _}
    val cd = symbols.getClass(id)
    classInstanceCache.cached(cd, context) {
      mkFunDef(instanceID(id), t.DropVCs, t.Synthetic)() { _ =>
        (("x" :: ref) +: cd.typeArgs.map(_.id.name :: (ref =>: BooleanType())), BooleanType(), {
          case x +: tps =>
            given scope: Scope = context.emptyScope.testing(cd.typeArgs zip tps)
            if (cd.children.nonEmpty) {
              t.orJoin(
                cd.typed.children.map(ccd => instanceOf(x, cd.typed.toType, ccd.toType))
              )
            } else {
              (x is cd.id) &&
              t.andJoin(cd.fields.map(vd => instanceOf(t.ADTSelector(x, vd.id), vd.tpe, vd.tpe)))
            }
        })
      }
    }
  }


  /* ====================================
   *           CLASS UNAPPLY
   * ==================================== */

  private[this] val unapplyID = new CachedID[Identifier](_.freshen)

  // The class unapply function depends on the current class and all its descendants
  // as it directly checks the dominated constructor set (no use of `instanceOf`).
  // The dependencies are therefore
  // - the class definition
  // - the descendant class definitions
  // - the synthetic OptionSort definitions
  private[this] val classUnapplyCache = new ExtractionCache[s.ClassDef, t.FunDef]({ (cd, context) =>
    ClassKey(cd) + SetKey(cd.descendants(using context.symbols).toSet) + OptionSort.key(using context.symbols)
  })

  private[this] def classUnapply(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.symbols
    import symbols.given
    val cd = symbols.getClass(id)
    classUnapplyCache.cached(cd, context) {
      import OptionSort._
      mkFunDef(unapplyID(cd.id), t.DropVCs, t.Synthetic, t.IsUnapply(isEmpty, get))() { _ =>
        val cons = constructors(cd)
        def condition(e: t.Expr): t.Expr = t.orJoin(cons.map(t.IsConstructor(e, _)))

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
    }
  }


  /* ====================================
   *         UNAPPLY FUNCTION
   * ==================================== */

  // The unapply function only depends on the synthetic OptionSort
  private[this] val unapplyAnyCache = new ExtractionCache[s.Symbols, t.FunDef](
    (_, context) => OptionSort.key(using context.symbols)
  )

  private[this] def unapplyAny(using context: TransformerContext): t.FunDef = unapplyAnyCache.cached(context.symbols, context) {
    import context.symbols.given
    import OptionSort.{value => _, _}
    mkFunDef(FreshIdentifier("InstanceOf"), t.DropVCs, t.Synthetic, t.IsUnapply(isEmpty, get))("A", "B") {
      case Seq(a, b) => (
        Seq("p" :: (a =>: t.BooleanType()), "t" :: (a =>: b), "x" :: a),
        T(option)(b), { case Seq(p, t, x) =>
          if_ (p(x)) {
            C(some)(b)(t(x))
          } else_ {
            C(none)(b)()
          }
        }
      )
    }
  }


  /* ====================================
   *           SORT INSTANCE
   * ==================================== */

  // The sort instance function depends only on the sort definition, so
  // we can use a simple cache here
  private[this] val sortInstanceCache = new SimpleCache[s.ADTSort, t.FunDef]

  private[this] def sortInstance(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.{symbols, emptyScope => scope}
    import symbols.given
    val sort = symbols.getSort(id)
    sortInstanceCache.cached(sort, context) {
      val in = sort.typeArgs.map(_.freshen)
      val tin = in.map(tp => scope.transform(tp).asInstanceOf[t.TypeParameter])

      val x = "x" :: T(id)(tin: _*)
      val fs = tin map { i => i.id.name :: (i =>: t.BooleanType()) }

      val newScope = scope testing (in zip fs map { case (ti, vd) => (ti, ti) -> vd.toVariable })
      val fullBody = t.orJoin(sort.typed(in).constructors map { cons =>
        (x.toVariable is cons.id) &&
        t.andJoin(cons.fields.map(vd => instanceOf(x.toVariable.getField(vd.id), vd.tpe, vd.tpe)(using newScope)))
      })

      new t.FunDef(
        instanceID(id), tin.map(t.TypeParameterDef(_)), x +: fs, t.BooleanType(), fullBody,
        Seq(t.DropVCs, t.Synthetic)
      ).setPos(sort)
    }
  }


  /* ====================================
   *            SORT CONVERT
   * ==================================== */

  // The sort conversion function depends only on the sort definition, so
  // we can again use a simple cache here
  private[this] val sortConvertCache = new SimpleCache[s.ADTSort, t.FunDef]

  private[this] def sortConvert(id: Identifier)(using context: TransformerContext): t.FunDef = {
    import context.{symbols, emptyScope => scope}
    import symbols.given
    val sort = symbols.getSort(id)
    sortConvertCache.cached(sort, context) {
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
          convert(x.toVariable.getField(vi.id), vi.tpe, vo.tpe)(using newScope)
        }: _*))
      }

      val fullBody = conversions.init.foldRight(conversions.last._2: Expr) {
        case ((cond, thenn), elze) => t.IfExpr(cond, thenn, elze)
      }

      new t.FunDef(
        convertID(id), (tin ++ tout).map(t.TypeParameterDef(_)), x +: fs, T(id)(tout: _*), fullBody,
        Seq(t.DropVCs, t.Synthetic)
      ).setPos(sort)
    }
  }


  /* ====================================
   *   TRANFORMATION/ENCODING CONTEXT
   * ==================================== */

  /* Stores meta-data about functions useful during encoding.
   *
   * @param fun - function abstraction (FunDef or LocalFunDef)
   * @param outer - the scope in which the local function definition occurred
   * @param tparams - the type parameters that should be encoded to predicates
   */
  protected case class FunInfo(fun: s.FunAbstraction, tparams: Set[Int])

  protected class ExprMapping private(underlying: Map[(s.Type, Option[s.Type]), t.Expr]) {
    def contains(p: (s.Type, s.Type)): Boolean = underlying contains (p._1 -> Some(p._2))
    def contains(tpe: s.Type): Boolean = underlying contains (tpe -> None)

    def apply(p: (s.Type, s.Type)): t.Expr = underlying apply (p._1 -> Some(p._2))
    def apply(tpe: s.Type): t.Expr = underlying apply (tpe -> None)

    def ++(ps: Iterable[((s.Type, s.Type), t.Expr)]): ExprMapping =
      new ExprMapping(underlying ++ ps.map { case ((t1, t2), e) => ((t1, Some(t2)), e) })
    def ++(ps: Iterable[(s.Type, t.Expr)])(using DummyImplicit): ExprMapping =
      new ExprMapping(underlying ++ ps.map { case (tpe, e) => ((tpe, None), e) })

    override def toString = underlying.toString
  }

  protected object ExprMapping {
    def empty: ExprMapping = new ExprMapping(Map.empty)
  }

  protected class Scope private(
    override val s: self.s.type,
    override val t: self.t.type,
    val functions: Map[Identifier, FunInfo],
    val tparams: Set[s.TypeParameter],
    val testers: ExprMapping,
    val converters: ExprMapping,
  )(using val context: TransformerContext, override val symbols: context.symbols.type) extends TransformerWithType {

    def this(functions: Map[Identifier, FunInfo],
             tparams: Set[self.s.TypeParameter],
             testers: ExprMapping,
             converters: ExprMapping)(using context: TransformerContext) =
      this(self.s, self.t, functions, tparams, testers, converters)(using context, context.symbols)

    protected given givenScope: this.type = this
    import symbols.{let => _, forall => _, _}

    def converting(ps: Iterable[((s.Type, s.Type), t.Expr)]): Scope =
      new Scope(functions, tparams, testers, converters ++ ps)

    def testing(ps: Iterable[((s.Type, s.Type), t.Expr)]): Scope =
      new Scope(functions, tparams, testers ++ ps, converters)
    def testing(ps: Iterable[(s.Type, t.Expr)])(using DummyImplicit): Scope =
      new Scope(functions, tparams, testers ++ ps, converters)
    def testing(p: (s.Type, t.Expr)): Scope =
      new Scope(functions, tparams, testers ++ Seq(p), converters)

    override def transform(tp: s.Type): t.Type = tp match {
      case s.AnyType() => ref.copiedFrom(tp)
      case s.NothingType() =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(t.BooleanLiteral(false).copiedFrom(tp), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case s.UnknownType(_) => transform(s.AnyType().copiedFrom(tp))

      case ct: s.ClassType =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, s.AnyType().copiedFrom(tp), ct), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case s.TypeBounds(_, s.AnyType(), _) => ref.copiedFrom(tp)
      case s.TypeBounds(_, upperBound, _) =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, s.AnyType().copiedFrom(tp), upperBound), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case ta: s.TypeApply if ta.isAbstract =>
        transform(ta.bounds)

      case ta: s.TypeApply if !ta.isAbstract =>
        transform(ta.resolve)

      case tp: s.TypeParameter if testers contains tp =>
        refinement(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) {
          x => t.Annotated(instanceOf(x, s.AnyType().copiedFrom(tp), tp), Seq(t.DropConjunct)).copiedFrom(tp)
        }.copiedFrom(tp)

      case tp: s.TypeParameter if tparams contains tp => ref.copiedFrom(tp)

      case tp: s.TypeParameter => super.transform(tp.copy(
        flags = tp.flags.filterNot { case (_: s.Variance | _: s.Bounds) => true case _ => false }
      ).copiedFrom(tp))

      case _ => super.transform(tp)
    }

    def in(id: Identifier): Scope = {
      assert((functions contains id) || (classes contains id))
      val extraTParams = functions.get(id).map { case FunInfo(fun, tparams) =>
        fun.tparams.map(_.tp).zipWithIndex.collect { case (tp, i) if tparams(i) => tp }
      }.getOrElse(classes(id).typeArgs)
      new Scope(functions, tparams ++ extraTParams, testers, converters)
    }

    override def transform(e: s.Expr, inType: s.Type): t.Expr = e match {
      case s.ClassConstructor(ct, args) =>
        t.ADT(ct.id, Seq(), (erased(ct).tcd.fields zip args).map {
          case (vd, arg) => convert(transform(arg), arg.getType, vd.tpe)
        }).copiedFrom(e)

      case s.ClassSelector(expr, id) =>
        val field = erased(expr.getType).asInstanceOf[s.ClassType].tcd.fields.find(_.id == id).get
        convert(t.ADTSelector(transform(expr), id).copiedFrom(e), field.getType, inType)

      case s.IsInstanceOf(expr, tpe) =>
        instanceOf(transform(expr), expr.getType, tpe).copiedFrom(e)

      case s.AsInstanceOf(expr, tpe) =>
        val vd = t.ValDef.fresh("x", transform(expr.getType)).copiedFrom(e)
        val cond = instanceOf(vd.toVariable, expr.getType, tpe).copiedFrom(e)
        if (cond == BooleanLiteral(true))
          transform(expr)
        else
          t.Let(vd, transform(expr), t.Assert(
            cond,
            Some("Cast error"),
            convert(vd.toVariable, expr.getType, tpe).copiedFrom(e)
          ).copiedFrom(e)).copiedFrom(e)

      case fi @ s.FunctionInvocation(id, tps, args) =>
        val funScope = this in id
        val FunInfo(fun, tparams) = functions(id)
        val tpSubst = (fun.tparams.map(_.tp) zip tps).zipWithIndex.map {
          case ((tp, tpe), i) => tp -> (if (tparams(i)) tp else tpe)
        }.toMap

        convert(t.FunctionInvocation(id,
          tps.zipWithIndex.collect { case (tp, i) if !tparams(i) => transform(tp) },
          tps.zipWithIndex.collect { case (tp, i) if tparams(i) =>
            simplify(\(("x" :: ref).copiedFrom(tp))(x => instanceOf(x, s.AnyType().copiedFrom(tp), tp)).copiedFrom(tp))
          } ++ (fun.params zip args).map { case (vd, arg) =>
            convert(transform(arg), arg.getType, s.typeOps.instantiateType(vd.tpe, tpSubst))(using funScope)
          }).copiedFrom(e), s.typeOps.instantiateType(fun.returnType.getType, tpSubst), inType)(using funScope)

      case app @ s.ApplyLetRec(id, tparams, tpe, tps, args) =>
        val funScope = this in id
        val FunInfo(fun, ctparams) = functions(id)
        val tpSubst = (fun.tparams.map(_.tp) zip tps).zipWithIndex.map {
          case ((tp, tpe), i) => tp -> (if (ctparams(i)) tp else tpe)
        }.toMap

        val nparams = tparams.zipWithIndex.collect { case (tp, i) if ctparams(i) =>
          (ref =>: t.BooleanType().copiedFrom(tp)).copiedFrom(tp)
        }

        convert(t.ApplyLetRec(
          id,
          tparams.zipWithIndex.collect { case (tp, i) if !ctparams(i) => transform(tp).asInstanceOf[t.TypeParameter] },
          t.FunctionType(nparams ++ tpe.from.map(funScope.transform), funScope.transform(tpe.to)).copiedFrom(tpe),
          tps.zipWithIndex.collect { case (tp, i) if !ctparams(i) => transform(tp) },
          tps.zipWithIndex.collect {  case (tp, i) if ctparams(i) =>
            simplify(\(("x" :: ref).copiedFrom(tp))(x => instanceOf(x, s.AnyType().copiedFrom(tp), tp)).copiedFrom(tp))
          } ++ (fun.params zip args).map { case (vd, arg) =>
            convert(transform(arg), arg.getType, s.typeOps.instantiateType(vd.tpe, tpSubst))(using funScope)
          }).copiedFrom(app), s.typeOps.instantiateType(fun.returnType.getType, tpSubst), inType)(using funScope)

      case s.LetRec(fds, body) =>
        val funs = fds.map(fd => s.Inner(fd))
        val newFuns = funs.map(transform(_))
        val newBody = transform(body, inType)
        t.LetRec(newFuns.map(_.toLocal), newBody).copiedFrom(e)

      // push conversions down into branches/leaves
      case (_: s.IfExpr | _: s.MatchExpr | _: s.Let) => super.transform(e, inType)

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
          val erasedTps = ct.tps.map(tp => if (isObject(tp)) tp else s.AnyType().copiedFrom(tp))
          val semiErased = ct.copy(tps = erasedTps).copiedFrom(ct)
          t.ADTPattern(
            ob map transform, ct.id, Seq(),
            subs zip semiErased.tcd.fields map { case (sub, vd) => transform(sub, vd.getType) }
          ).copiedFrom(pat)

        case _ =>
          instanceOfPattern(t.UnapplyPattern(
            ob map transform, Seq(), unapplyID(ct.id), Seq(),
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
        val funScope = this in id
        val FunInfo(fun, tparams) = functions(id)
        val tpSubst = (fun.tparams.map(_.tp) zip tps).zipWithIndex.map {
          case ((tp, tpe), i) => tp -> (if (tparams(i)) tp else tpe)
        }.toMap

        t.UnapplyPattern(
          ob map transform,
          tps.zipWithIndex.flatMap { case (tp, i) =>
            if (tparams(i)) Seq(
              simplify(\(("x" :: ref).copiedFrom(tp)) { x =>
                instanceOf(x, s.AnyType().copiedFrom(tp), tp)
              }.copiedFrom(tp)),
              \(("x" :: ref).copiedFrom(tp))(x => unwrap(x, tp)).copiedFrom(tp)
            ) else Seq.empty[t.Expr]
          } ++ (recs zip fun.params.init).map {
            case (r, vd) => convert(transform(r), r.getType, s.typeOps.instantiateType(vd.tpe, tpSubst))(using funScope)
          }, id, tps.zipWithIndex.collect { case (tp, i) if !tparams(i) => transform(tp) },
          subs zip up.subTypes(tpe) map (p => transform(p._1, p._2))
        ).copiedFrom(pat)

      case s.LiteralPattern(ob, lit) =>
        instanceOfPattern(super.transform(pat, lit.getType), tpe, lit.getType)
    }

    override def transform(fd: s.FunDef): t.FunDef = transform(s.Outer(fd)).toFun

    def transform(fd: s.FunAbstraction): t.FunAbstraction = {
      val FunInfo(_, tparams) = functions(fd.id)

      val ntparams = fd.tparams.zipWithIndex.collect { case (tpd, i) if !tparams(i) => transform(tpd) }

      val (scope, tparamParams) = fd.tparams.map(_.tp).zipWithIndex
        .collect { case (tp, i) if tparams(i) => tp }
        .foldLeft((this in fd.id, Seq[t.ValDef]())) {
          case ((scope, vds), tp) =>
            val s.TypeBounds(lowerBound, upperBound, _) = tp.bounds

            val tpe = if (lowerBound == s.NothingType() && upperBound == s.AnyType()) {
              (ref.copiedFrom(tp) =>: t.BooleanType().copiedFrom(tp)).copiedFrom(tp)
            } else {
              pi(("x" :: ref.copiedFrom(tp)).copiedFrom(tp)) { x =>
                refinement(("b" :: t.BooleanType().copiedFrom(tp)).copiedFrom(tp)) { b =>
                  t.Annotated(t.and(
                    t.implies(instanceOf(x, tp, lowerBound)(using scope), b).copiedFrom(lowerBound),
                    t.implies(b, instanceOf(x, tp, upperBound)(using scope)).copiedFrom(upperBound)
                  ).copiedFrom(tp), Seq(t.DropConjunct)).copiedFrom(tp)
                }.copiedFrom(tp)
              }.copiedFrom(tp)
            }

            val vd = t.ValDef(tp.id.freshen, tpe).copiedFrom(tp)
            (scope.testing(tp -> vd.toVariable), vds :+ vd)
        }

      fd.to(t)(
        fd.id,
        ntparams,
        tparamParams ++ fd.params.map(scope.transform(_)),
        scope.transform(fd.returnType),
        scope.transform(fd.fullBody, fd.returnType.getType),
        fd.flags map scope.transform
      )
    }
  }

  private[this] object Scope {
    def empty(using context: TransformerContext): Scope = {
      import context.symbols
      import symbols.{given, _}

      def computeInfo(fun: s.FunAbstraction)(infos: Map[Identifier, FunInfo]): FunInfo = {
        val tparams: Seq[s.TypeParameter] = fun.tparams.map(_.tp)
        var simple: Set[s.TypeParameter] = tparams.toSet

        class Traverser(override val s: self.s.type, override val t: self.s.type)
                       (using override val symbols: context.symbols.type)
          extends TransformerWithType {

          override def transform(pat: s.Pattern, in: s.Type): t.Pattern = pat match {
            case s.InstanceOfPattern(_, tpe) if leastUpperBound(tpe, in) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(in.getType)
              simple --= s.typeOps.typeParamsOf(tpe.getType)
              super.transform(pat, in)

            case s.ClassPattern(_, ct, _) =>
              if (leastUpperBound(ct, in) == s.AnyType()) {
                simple --= s.typeOps.typeParamsOf(in.getType)
              }
              simple --= s.typeOps.typeParamsOf(ct.getType)
              super.transform(pat, in)

            case s.ADTPattern(ob, id, tps, subs) =>
              if (leastUpperBound(in, s.ADTType(getConstructor(id).sort, tps)) == s.AnyType()) {
                simple --= s.typeOps.typeParamsOf(in.getType)
                tps.foreach(tp => simple --= s.typeOps.typeParamsOf(tp.getType))
              }
              super.transform(pat, in)

            case s.TuplePattern(ob, subs) => widen(in.getType) match {
              case s.TupleType(tps) if tps.size == subs.size =>
                super.transform(pat, in)
              case _ =>
                simple --= s.typeOps.typeParamsOf(in.getType)
                super.transform(pat, in)
            }

            case up @ s.UnapplyPattern(ob, recs, id, tps, subs) =>
              val tparams = infos(id).tparams
              simple --= tps.zipWithIndex.flatMap { case (tp, i) =>
                if (tparams(i)) s.typeOps.typeParamsOf(tp.getType)
                else Set.empty[s.TypeParameter]
              }
              super.transform(pat, in)

            case s.LiteralPattern(_, lit) if leastUpperBound(lit.getType, in) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(in.getType)
              super.transform(pat, in)

            case _ => super.transform(pat, in)
          }

          override def transform(e: s.Expr, tpe: s.Type): t.Expr = e match {
            case s.IsInstanceOf(expr, tp) if leastUpperBound(expr.getType, tp) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(expr.getType)
              simple --= s.typeOps.typeParamsOf(tp.getType)
              super.transform(e, tpe)

            case s.AsInstanceOf(expr, tp) if leastUpperBound(expr.getType, tp) == s.AnyType() =>
              simple --= s.typeOps.typeParamsOf(expr.getType)
              simple --= s.typeOps.typeParamsOf(tp.getType)
              super.transform(e, tpe)

            case s.FunInvocation(id, tps, args, _) =>
              val tparams = infos(id).tparams
              simple --= tps.zipWithIndex.flatMap { case (tp, i) =>
                if (tparams(i)) s.typeOps.typeParamsOf(tp.getType)
                else Set.empty[s.TypeParameter]
              }
              super.transform(e, tpe)

            case _ => super.transform(e, tpe)
          }

          override def transform(tpe: s.Type): t.Type = tpe match {
            case s.ClassType(id, tps) =>
              simple --= tps.flatMap(tp => s.typeOps.typeParamsOf(tp))
              super.transform(tpe)

            case tp: s.TypeParameter if simple(tp) =>
              val bounds = tp.flags.collect {
                case s.Bounds(lo, hi) => Seq(lo, hi)
              }.flatten.toSet

              val boundParams = tparams.filter(bounds.flatMap(s.typeOps.typeParamsOf))

              if (bounds.nonEmpty) {
                simple -= tp
                boundParams foreach { param =>
                  simple -= param
                }
              }

              super.transform(tpe)

            case _ => super.transform(tpe)
          }
        }

        val traverser = new Traverser(self.s, self.s)(using context.symbols)

        fun.tparams map (traverser.transform(_))
        fun.params map (traverser.transform(_))
        traverser.transform(fun.returnType)
        traverser.transform(fun.fullBody, fun.returnType.getType)
        fun.flags map (traverser.transform(_))

        val nonSimpleParamsIndices = tparams.zipWithIndex.collect {
          case (tp, i) if !simple(tp) => i
        }.toSet

        FunInfo(fun, nonSimpleParamsIndices)
      }

      val functions = context.symbols.functions.values.toSeq.flatMap { fd =>
        val inners = s.exprOps.collect {
          case s.LetRec(fds, _) => fds.toSet
          case _ => Set.empty[s.LocalFunDef]
        } (fd.fullBody)

        Seq(s.Outer(fd)) ++ inners.map(s.Inner(_))
      }

      val infos = inox.utils.fixpoint { (infos: Map[Identifier, FunInfo]) =>
        infos.map { case (id, info) => id -> computeInfo(info.fun)(infos) }
      } (functions.map(fun => fun.id -> FunInfo(fun, Set.empty)).toMap)

      new Scope(infos, Set.empty, ExprMapping.empty, ExprMapping.empty)
    }
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) {
    import symbols.{given, _}
    given emptyScope: Scope = Scope.empty(using this)

    private val (tplSizes, funSizes, bvSizes) = {
      var tplSizes: Set[Int] = Set.empty
      var funSizes: Set[Int] = Set.empty
      var bvSizes: Set[(Boolean, Int)] = Set.empty

      object traverser extends s.ConcreteOOSelfTreeTraverser {
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
          case s.ArrayLength(_) => bvSizes += (true -> 32); super.traverse(expr)
          case _ => super.traverse(expr)
        }
      }

      symbols.functions.values.foreach(traverser.traverse)

      (tplSizes, funSizes, bvSizes)
    }

    val refSort = new t.ADTSort(refID, Seq(),
      symbols.classes.values.toSeq.filterNot(_.flags contains s.IsAbstract).map { cd =>
        val anys = cd.typeArgs.map(tp => s.AnyType().copiedFrom(tp))
        val fields = cd.typed(anys).fields.map(emptyScope.transform _)
        new t.ADTConstructor(cd.id, refID, fields).copiedFrom(cd)
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
      ), Seq(t.Synthetic))

    def transform(fd: s.FunDef): t.FunDef = emptyScope.transform(fd)

    def transform(sort: s.ADTSort): t.ADTSort = emptyScope.transform(sort)

    def functions: Seq[t.FunDef] =
      symbols.classes.keys.toSeq.flatMap(id => Seq(classInstance(id)(using this), classUnapply(id)(using this))) ++
      symbols.sorts.keys.flatMap(id => Seq(sortInstance(id)(using this), sortConvert(id)(using this))) ++
      OptionSort.functions :+ unapplyAny(using this)

    def sorts: Seq[t.ADTSort] =
      OptionSort.sorts :+ refSort

    /** Duplicate function [[encoded]] that was derived from [[original]] into
     *  another function without the reified type parameters and an empty body.
     *  The post of [[encoded]] is then modified to assert that its result
     *  is equals to the result of this new function, when applied
     *  to (non-type args) parameters. This allows the solver to deduce that the
     *  reified type parameters themselves do not influence the result of a call
     *  to [[encoded]], something that is needed eg., in the presence of GADTs where
     *  equivalent calls to the same method via both the top-level dispatcher,
     *  and a concrete implementation can carry different reified type parameters.
     */
    def createTypeArgsElimWitness(encoded: t.FunDef, original: s.FunDef): Seq[t.FunDef] = {
      def dropRefinements(tpe: t.Type): t.Type = {
        t.typeOps.preMap {
          case t.RefinementType(base, _) => Some(base.tpe)
          case _ => None
        } (tpe)
      }

      val reifiedTypeArgsCount = encoded.params.size - original.params.size
      assert(reifiedTypeArgsCount > 0)

      val elimParams = encoded.params
        .drop(reifiedTypeArgsCount)
        .map(vd => vd.copy(tpe = dropRefinements(vd.tpe)))

      val eliminated = t.exprOps.freshenSignature(new t.FunDef(
        original.id.freshen,
        encoded.tparams,
        elimParams,
        dropRefinements(encoded.returnType),
        t.NoTree(dropRefinements(encoded.returnType)),
        Seq(t.Derived(Some(original.id)))
      ).copiedFrom(encoded))

      val specced = t.exprOps.BodyWithSpecs(encoded.fullBody)
      val (vd, post) = specced.getSpec(t.exprOps.PostconditionKind) match {
        case Some(t.exprOps.Postcondition(Lambda(Seq(vd), post))) => (vd, post)
        case None => (
          t.ValDef.fresh("res", encoded.returnType),
          t.BooleanLiteral(true).copiedFrom(encoded.fullBody)
        )
      }

      val newPostLambda = t.Lambda(Seq(vd),
        t.and(
          post,
          t.Annotated(
            t.Equals(
              vd.toVariable.copiedFrom(post),
              t.FunctionInvocation(
                eliminated.id,
                encoded.tparams.map(_.tp),
                encoded.params.drop(reifiedTypeArgsCount).map(_.toVariable.copiedFrom(post))
              ).copiedFrom(post)
            ).copiedFrom(post),
            Seq(t.DropConjunct)
          ).copiedFrom(post)
        )
      )
      val newPost = t.exprOps.Postcondition(newPostLambda).setPos(post.getPos)

      val newBody = specced.withSpec(newPost).reconstructed
      Seq(encoded.copy(fullBody = newBody), eliminated)
    }
  }

  override protected def extractSymbols(context: TransformerContext, symbols: s.Symbols): t.Symbols = {
    val newSymbols = super.extractSymbols(context, symbols)
      .withFunctions(context.functions)
      .withSorts(context.sorts)

    // newSymbols.ensureWellFormed

    val dependencies: Set[Identifier] =
      (symbols.functions.keySet ++ symbols.sorts.keySet)
        .flatMap(id => newSymbols.dependencies(id) + id)

    val independentSymbols = t.NoSymbols
      .withFunctions(newSymbols.functions.values.toSeq.filter(fd => dependencies(fd.id)))
      .withSorts(newSymbols.sorts.values.toSeq.filter(sort => dependencies(sort.id)))

    // independentSymbols.ensureWellFormed

    val constructors: Set[Identifier] = {
      import independentSymbols.{given, _}

      var constructors: Set[Identifier] = Set.empty
      val traverser = new t.ConcreteStainlessSelfTreeTraverser {
        override def traverse(expr: t.Expr): Unit = expr match {
          case t.IsTyped(t.ADT(id, tps, es), t.ADTType(`refID`, _)) => constructors += id; super.traverse(expr)
          case t.IsConstructor(t.IsTyped(e, t.ADTType(`refID`, _)), id) => constructors += id; super.traverse(expr)
          case t.ADTSelector(t.IsTyped(e, t.ADTType(`refID`, _)), id) =>
            constructors ++= context.refSort.constructors.find(_.fields.exists(_. id == id)).map(_.id)
            super.traverse(expr)
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

    // result.ensureWellFormed
    result
  }

  // The computation of which type parameters must be rewritten considers all
  // dependencies, so we use a dependency cache for function transformations
  override protected val funCache = new ExtractionCache[s.FunDef, FunctionResult]({
    (fd, context) => getDependencyKey(fd.id)(using context.symbols)
  })

  // Sort transformations are straightforward and can be simply cached
  override protected val sortCache = new SimpleCache[s.ADTSort, SortResult]

  // Classes are simply dropped by this phase, so any cache is valid here
  override protected val classCache = new SimpleCache[s.ClassDef, ClassResult]

  // Type definitions are simply dropped by this phase, so any cache is valid here
  override protected val typeDefCache = new SimpleCache[s.TypeDef, TypeDefResult]

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): Seq[t.FunDef] = {
    val encoded = context.transform(fd)

    // If function has gained new parameters for reifed types,
    // we create a dummy version of it without any type arguments
    // as a witness that type arguments do not influence the result
    // of the computation of its invocation.
    if (encoded.params.size > fd.params.size) {
      context.createTypeArgsElimWitness(encoded, fd)
    } else {
      Seq(encoded)
    }
  }

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort): t.ADTSort = context.transform(sort)

  // Classes are simply dropped by this extraction phase
  override protected type ClassResult = Unit
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult = ()
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[Unit]): t.Symbols = symbols

  // Type definitions are simply dropped by this extraction phase
  override protected type TypeDefResult = Unit
  override protected def extractTypeDef(context: TransformerContext, cd: s.TypeDef): TypeDefResult = ()
  override protected def registerTypeDefs(symbols: t.Symbols, typeDefs: Seq[Unit]): t.Symbols = symbols
}

object TypeEncoding {
  def apply(ts: Trees, tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends TypeEncoding(s, t)
    new Impl(ts, tt)
  }
}
