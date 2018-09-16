/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package oo

trait TypeOps extends imperative.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols._

  // Simplified version of CNF optimized for subtyping between refinement types
  // Note that the sort function we use to ensure normal CNF forms is consistent
  // with the ADT constructor sort function in AdtSpecialization.
  protected def cnf(pred: Expr): Expr = {
    def rec(pred: Expr): Seq[Expr] = pred match {
      case And(es) =>
        es.flatMap(rec).sortBy(_.toString)
      case Or(es) =>
        es.map(rec).foldLeft(Seq[Expr](BooleanLiteral(false))) {
          case (clauses, es) => es.flatMap(e => clauses.map(c => or(c, e) match {
            case TopLevelOrs(es) => orJoin(es.sortBy(_.toString))
          }))
        }.sortBy(_.toString)
      case e => Seq(e)
    }

    // We don't use simplifyByConstructors here because we don't want more
    // simplifications than the CNF form, otherwise syntactic equalities upon
    // which we rely for refinement type checking may be broken during the
    // transformation pipeline.
    andJoin(rec(pred))
  }

  protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = ((tp1, tp2) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => Some(Untyped)
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => Some(Untyped)
    case (ct1: ClassType, ct2: ClassType) =>
      if (upper) {
        leastUpperClassBound(ct1, ct2)
      } else {
        greatestLowerClassBound(ct1, ct2)
      }

    case (adt: ADTType, _) if adt.lookupSort.isEmpty => Some(Untyped)
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => Some(Untyped)
    case (adt1: ADTType, adt2: ADTType) if adt1 == adt2 => Some(adt1)

    case (RefinementType(vd1, p1), RefinementType(vd2, p2)) if vd1.tpe == vd2.tpe =>
      // Here we preserve `vd2` as the typeBound used in subtyping checks will compare the
      // typeBound result with the second type. This gets around the issue of identifier
      // normalization in refinement types.
      val np1 = exprOps.replaceFromSymbols(Map(vd1 -> vd2.toVariable), p1)
      Some(RefinementType(vd2, if (upper) cnf(or(np1, p2)) else cnf(and(np1, p2))))
    case (rt @ RefinementType(vd, p), tpe) if vd.tpe == tpe => Some(if (upper) tpe else rt)
    case (tpe, rt @ RefinementType(vd, p)) if tpe == vd.tpe => Some(if (upper) tpe else rt)

    case (TypeBounds(lo, hi), tpe) => Some(typeBound(if (upper) hi else lo, tpe, upper))
    case (tpe, TypeBounds(lo, hi)) => Some(typeBound(tpe, if (upper) hi else lo, upper))

    case (tp1: TypeParameter, tp2: TypeParameter) if tp1 == tp2 => Some(tp1)
    case (tp: TypeParameter, tpe) if upper && isSubtypeOf(tpe, tp.lowerBound) => Some(tp)
    case (tp: TypeParameter, tpe) if !upper && isSubtypeOf(tp.upperBound, tpe) => Some(tp)
    case (tpe, tp: TypeParameter) if upper && isSubtypeOf(tpe, tp.lowerBound) => Some(tp)
    case (tpe, tp: TypeParameter) if !upper && isSubtypeOf(tp.upperBound, tpe) => Some(tp)

    case (tp: TypeParameter, tpe) => Some(typeBound(tp.bounds, tpe, upper))
    case (tpe, tp: TypeParameter) => Some(typeBound(tpe, tp.bounds, upper))

    case (tp, AnyType()) if tp.getType.isTyped => Some(if (upper) AnyType() else tp)
    case (AnyType(), tp) if tp.getType.isTyped => Some(if (upper) AnyType() else tp)
    case (NothingType(), tp) if tp.getType.isTyped => Some(if (upper) tp else NothingType())
    case (tp, NothingType()) if tp.getType.isTyped => Some(if (upper) tp else NothingType())

    case (FunctionType(from1, to1), FunctionType(from2, to2)) if from1.size == from2.size =>
      val in = (from1 zip from2).map { case (tp1, tp2) => typeBound(tp1, tp2, !upper) }
      val out = typeBound(to1, to2, upper)
      Some(FunctionType(in, out))

    case (TupleType(ts1), TupleType(ts2)) if ts1.size == ts2.size =>
      val tps = (ts1 zip ts2).map { case (tp1, tp2) => typeBound(tp1, tp2, upper) }
      Some(TupleType(tps))

    case (t1, t2) if t1 == t2 => Some(t1)

    case _ => None
  }).getOrElse(if (upper) AnyType() else NothingType()).getType

  /** Computes the tightest bound (upper or lower) of a sequence of types */
  private def typeBound(tps: Seq[Type], upper: Boolean): Type = {
    if (tps.isEmpty) Untyped
    else tps.reduceLeft(typeBound(_, _, upper))
  }

  def leastUpperClassBound(ct1: ClassType, ct2: ClassType): Option[ClassType] = {
    val cd1Ans = ct1.tcd.ancestors.map(_.id).toSet + ct1.id
    val cd2Ans = ct2.tcd.ancestors.map(_.id).toSet + ct2.id
    val ans1 = (ct1.tcd +: ct1.tcd.ancestors).find(tcd => cd2Ans contains tcd.id)
    val ans2 = (ct2.tcd +: ct2.tcd.ancestors).find(tcd => cd1Ans contains tcd.id)
    (ans1, ans2) match {
      case (Some(tcd1), Some(tcd2)) =>
        val tps = (tcd1.cd.typeArgs zip tcd1.tps zip tcd2.tps).map {
          case ((tp, tpe1), tpe2) =>
            if (tp.isCovariant) Some(leastUpperBound(tpe1, tpe2))
            else if (tp.isContravariant) Some(greatestLowerBound(tpe1, tpe2))
            else if (tpe1 == tpe2) Some(tpe1)
            else None
        }
        if (tps.forall(_.isDefined)) Some(ClassType(tcd1.id, tps.map(_.get)))
        else None
      case _ => None
    }
  }

  def greatestLowerClassBound(ct1: ClassType, ct2: ClassType): Option[ClassType] = {
    val cd1Desc = ct1.tcd.descendants.map(_.id).toSet + ct1.id
    val cd2Desc = ct2.tcd.descendants.map(_.id).toSet + ct2.id
    val desc1 = (ct1.tcd +: ct1.tcd.descendants).find(tcd => cd2Desc contains tcd.id)
    val desc2 = (ct2.tcd +: ct2.tcd.descendants).find(tcd => cd1Desc contains tcd.id)
    (desc1, desc2) match {
      case (Some(tcd1), Some(tcd2)) =>
        val tps = (tcd1.cd.typeArgs zip tcd1.tps zip tcd2.tps).map {
          case ((tp, tpe1), tpe2) =>
            if (tp.isCovariant) Some(greatestLowerBound(tpe1, tpe2))
            else if (tp.isContravariant) Some(leastUpperBound(tpe1, tpe2))
            else if (tpe1 == tpe2) Some(tpe1)
            else None
        }
        if (tps.forall(_.isDefined)) Some(ClassType(tcd1.id, tps.map(_.get)))
        else None
      case _ => None
    }
  }

  override def leastUpperBound(tp1: Type, tp2: Type): Type = typeBound(tp1, tp2, true)
  override def leastUpperBound(tps: Seq[Type]): Type = typeBound(tps, true)

  override def greatestLowerBound(tp1: Type, tp2: Type): Type = typeBound(tp1, tp2, false)
  override def greatestLowerBound(tps: Seq[Type]): Type = typeBound(tps, false)

  override def isSubtypeOf(t1: Type, t2: Type): Boolean = {
    (!t1.isTyped && !t2.isTyped) || (t1.isTyped && t2.isTyped && leastUpperBound(t1, t2) == t2)
  }

  def typesCompatible(t1: Type, t2s: Type*) = {
    leastUpperBound(t1 +: t2s) != Untyped
  }

  private class Unsolvable extends Exception
  protected def unsolvable = throw new Unsolvable

  /** Collects the constraints that need to be solved for [[unify]].
    * Note: this is an override point. */
  protected def unificationConstraints(t1: Type, t2: Type, free: Seq[TypeParameter]): List[(TypeParameter, Type)] = (t1, t2) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => unsolvable
    case (adt: ADTType, _) if adt.lookupSort.isEmpty => unsolvable
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => unsolvable
    case _ if t1 == t2 => Nil
    case (ct1: ClassType, ct2: ClassType) if ct1.tcd.cd == ct2.tcd.cd =>
      (ct1.tps zip ct2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case (adt1: ADTType, adt2: ADTType) if adt1.id == adt2.id =>
      (adt1.tps zip adt2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case (RefinementType(vd1, p1), RefinementType(vd2, p2)) => unify(vd1.tpe, vd2.tpe, free) match {
      case Some(tpMap) if exprOps.postMap {
        case v: Variable if v.id == vd1.id => Some(v.copy(id = vd2.id))
        case _ => None
      } (typeOps.instantiateType(p1, tpMap.toMap)) == p2 => tpMap
      case _ => unsolvable
    }
    case (TypeBounds(lo, hi), tpe) if lo == hi => unificationConstraints(hi, tpe, free)
    case (tpe, TypeBounds(lo, hi)) if lo == hi => unificationConstraints(hi, tpe, free)
    case (tp: TypeParameter, _) if !(typeOps.typeParamsOf(t2) contains tp) && (free contains tp) => List(tp -> t2)
    case (_, tp: TypeParameter) if !(typeOps.typeParamsOf(t1) contains tp) && (free contains tp) => List(tp -> t1)
    case (_: TypeParameter, _) => unsolvable
    case (_, _: TypeParameter) => unsolvable
    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) if ts1.size == ts2.size =>
      (ts1 zip ts2).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case _ => unsolvable
  }

  /** Solves the constraints collected by [[unificationConstraints]].
    * Note: this is an override point. */
  protected def unificationSolution(const: List[(Type, Type)]): List[(TypeParameter, Type)] = const match {
    case Nil => Nil
    case (tp: TypeParameter, t) :: tl =>
      val replaced = tl map { case (t1, t2) =>
        (typeOps.instantiateType(t1, Map(tp -> t)), typeOps.instantiateType(t2, Map(tp -> t)))
      }
      (tp -> t) :: unificationSolution(replaced)
    case (adt: ADTType, _) :: tl if adt.lookupSort.isEmpty => unsolvable
    case (_, adt: ADTType) :: tl if adt.lookupSort.isEmpty => unsolvable
    case (ADTType(id1, tps1), ADTType(id2, tps2)) :: tl if id1 == id2 =>
      unificationSolution((tps1 zip tps2).toList ++ tl)
    case (ct: ClassType, _) :: tl if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) :: tl if ct.lookupClass.isEmpty => unsolvable
    case (ClassType(id1, tps1), ClassType(id2, tps2)) :: tl if id1 == id2 =>
      unificationSolution((tps1 zip tps2).toList ++ tl)
    case typeOps.Same(NAryType(ts1, _), NAryType(ts2, _)) :: tl if ts1.size == ts2.size =>
      unificationSolution((ts1 zip ts2).toList ++ tl)
    case _ =>
      unsolvable
  }

  /** Unifies two types, under a set of free variables */
  def unify(t1: Type, t2: Type, free: Seq[TypeParameter]): Option[List[(TypeParameter, Type)]] = {
    try {
      Some(unificationSolution(unificationConstraints(t1, t2, free)))
    } catch {
      case _: Unsolvable => None
    }
  }

  def freshenTypeParams(tps: Seq[TypeParameter]): Seq[TypeParameter] = {
    class Freshener(mapping: Map[TypeParameter, TypeParameter]) extends oo.TreeTransformer {
      val s: trees.type = trees
      val t: trees.type = trees

      override def transform(tpe: s.Type): t.Type = tpe match {
        case tp: TypeParameter if mapping contains tp => mapping(tp)
        case _ => super.transform(tpe)
      }
    }

    val tpMap = tps.foldLeft(Map[TypeParameter, TypeParameter]()) { case (tpMap, tp) =>
      val freshener = new Freshener(tpMap)
      val freshTp = freshener.transform(tp.freshen).asInstanceOf[TypeParameter]
      tpMap + (tp -> freshTp)
    }

    tps.map(tpMap)
  }

  def patternInType(pat: Pattern): Type = pat match {
    case WildcardPattern(ob) => ob.map(_.tpe).getOrElse(AnyType())
    case LiteralPattern(_, lit) => lit.getType
    case ADTPattern(_, id, tps, _) =>
      lookupConstructor(id)
        .map(cons => ADTType(cons.sort, tps))
        .getOrElse(Untyped)
    case TuplePattern(_, subs) => TupleType(subs map patternInType)
    case ClassPattern(_, ct, subs) => ct
    case UnapplyPattern(_, rec, id, tps, _) =>
      val optFd = lookupFunction(id).filter(fd => fd.tparams.size == tps.size)
      optFd.filter(_.params.size == 1 && rec.isEmpty).map(_.typed(tps).params.head.tpe)
        .orElse(optFd.filter(_.params.size == 2 && rec.nonEmpty).map(_.typed(tps).params(1).tpe))
        .getOrElse(Untyped)
    case InstanceOfPattern(_, tpe) => tpe
  }

  override def patternIsTyped(in: Type, pat: Pattern): Boolean = (in, pat) match {
    case (_, _) if !isSubtypeOf(patternInType(pat), in) =>
      pat.binder.forall(vd => isSubtypeOf(in, vd.tpe)) &&
      patternIsTyped(patternInType(pat), pat)

    case (_, ClassPattern(ob, ct, subs)) => in match {
      case ct2 @ ClassType(id, tps) if isSubtypeOf(ct, ct2) =>
        lookupClass(ct.id).exists { cls =>
          cls.fields.size == subs.size &&
          cls.tparams.size == ct.tps.size &&
          (cls.typed(ct.tps).fields zip subs).forall { case (vd, sub) => patternIsTyped(vd.tpe, sub) }
        }
      case _ => patternIsTyped(patternInType(pat), pat)
    }

    case (_, InstanceOfPattern(ob, tpe)) =>
      ob.forall(vd => isSubtypeOf(tpe, vd.tpe))

    case (AnyType(), _) =>
      if (patternInType(pat) == AnyType()) {
        pat.binders.forall(vd => isSubtypeOf(AnyType(), vd.tpe))
      } else {
        patternIsTyped(patternInType(pat), pat)
      }

    case _ => super.patternIsTyped(in, pat)
  }
}

