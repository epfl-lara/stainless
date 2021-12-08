/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait TypeOps extends innerfuns.TypeOps { self =>
  protected val trees: Trees
  import trees._
  import symbols.{given, _}

  protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = ((tp1, tp2) match {
    case (Untyped, _) => Some(Untyped)
    case (_, Untyped) => Some(Untyped)

    // We need to disallow ? <: Any, otherwise it becomes possible to prove that A <: B for any A, B.
    case (UnknownType(_), AnyType()) if upper  => Some(Untyped)
    case (AnyType(), UnknownType(_)) if !upper => Some(Untyped)

    // Impure unknown type is not a subtype of pure unknown type
    case (UnknownType(false), UnknownType(true)) =>
      Some(Untyped)

    case (UnknownType(true), UnknownType(false)) =>
      if (upper) Some(UnknownType(false))
      else Some(UnknownType(true))

    case (tp, UnknownType(_)) if tp.getType.isTyped => Some(tp)
    case (UnknownType(_), tp) if tp.getType.isTyped => Some(tp)

    case (ct: ClassType, _) if ct.lookupClass.isEmpty => Some(Untyped)
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => Some(Untyped)
    case (ct1: ClassType, ct2: ClassType) =>
      if (upper) {
        leastUpperClassBound(ct1, ct2)
      } else {
        greatestLowerClassBound(ct1, ct2)
      }

    case (ta: TypeApply, _) if ta.lookupTypeDef.isEmpty => Some(Untyped)
    case (_, ta: TypeApply) if ta.lookupTypeDef.isEmpty => Some(Untyped)

    case (ta1: TypeApply, ta2: TypeApply) if ta1 == ta2 => Some(ta1)

    // NOTE: Below are the DOT rules for type members subtyping, which unfortunately do not
    //       work in our context, as it erases too much information. @romac
    //
    // case (ta: TypeApply, tpe) if upper  && isSubtypeOf(ta.upperBound, tpe) => Some(tpe)
    // case (ta: TypeApply, tpe) if !upper && isSubtypeOf(ta.upperBound, tpe) => Some(ta)
    // case (tpe, ta: TypeApply) if upper  && isSubtypeOf(tpe, ta.lowerBound) => Some(ta)
    // case (tpe, ta: TypeApply) if !upper && isSubtypeOf(tpe, ta.lowerBound) => Some(tpe)
    // case (ta: TypeApply, tpe) => Some(typeBound(ta.bounds, tpe, upper))
    // case (tpe, ta: TypeApply) => Some(typeBound(tpe, ta.bounds, upper))

    case (ta: TypeApply, tpe) if !ta.isAbstract => typeBound(ta.resolve, tpe, upper) match {
      case Untyped           => Some(Untyped)
      case lub if lub == tpe => Some(tpe)
      case _                 => Some(ta)
    }

    case (tpe, ta: TypeApply) if !ta.isAbstract => typeBound(tpe, ta.resolve, upper) match {
      case Untyped           => Some(Untyped)
      case lub if lub == tpe => Some(tpe)
      case _                 => Some(ta)
    }

    case (ta: TypeApply, tpe) if ta.isAbstract => typeBound(ta.bounds, tpe, upper) match {
      case Untyped           => Some(Untyped)
      case _   if upper      => Some(tpe)
      case _                 => Some(ta)
    }
    case (tpe, ta: TypeApply) if ta.isAbstract => typeBound(tpe, ta.bounds, upper) match {
      case Untyped           => Some(Untyped)
      case _ if upper        => Some(ta)
      case _                 => Some(tpe)
    }

    case (adt: ADTType, _) if adt.lookupSort.isEmpty => Some(Untyped)
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => Some(Untyped)

    case (adt1: ADTType, adt2: ADTType) if adt1 == adt2 => Some(adt1)

    case (rt: RefinementType, _) => Some(typeBound(rt.getType, tp2, upper))
    case (_, rt: RefinementType) => Some(typeBound(tp1, rt.getType, upper))

    case (pi: PiType, _) => Some(typeBound(pi.getType, tp2, upper))
    case (_, pi: PiType) => Some(typeBound(tp1, pi.getType, upper))

    case (sigma: SigmaType, _) => Some(typeBound(sigma.getType, tp2, upper))
    case (_, sigma: SigmaType) => Some(typeBound(tp1, sigma.getType, upper))

    case (TypeBounds(lo, hi, _), tpe) => Some(typeBound(if (upper) hi else lo, tpe, upper))
    case (tpe, TypeBounds(lo, hi, _)) => Some(typeBound(tpe, if (upper) hi else lo, upper))

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

    // maps are covariant in the OO type system
    case (MapType(f1, t1), MapType(f2, t2)) if f1 == f2 =>
      Some(MapType(f1, typeBound(t1, t2, upper)))

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
          // NOTE: We need to preserve type applications for the subtyping checks to go through. @romac
          case ((tp, tpe1: TypeApply), tpe2) if typesCompatible(tpe1, tpe2) => Some(tpe1)
          case ((tp, tpe1), tpe2: TypeApply) if typesCompatible(tpe1, tpe2) => Some(tpe2)

          case ((tp, tpe1), tpe2) =>
            lazy val lub = leastUpperBound(tpe1, tpe2)
            lazy val glb = greatestLowerBound(tpe1, tpe2)

            if      (tp.isCovariant)     Some(lub)
            else if (tp.isContravariant) Some(glb)
            else if (tpe1 == tpe2)       Some(tpe2)
            else                         None
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
          // NOTE: We need to preserve type applications for the subtyping checks to go through. @romac
          case ((tp, tpe1: TypeApply), tpe2) if typesCompatible(tpe1, tpe2) => Some(tpe1)
          case ((tp, tpe1), tpe2: TypeApply) if typesCompatible(tpe1, tpe2) => Some(tpe2)

          case ((tp, tpe1), tpe2) =>
            lazy val lub = leastUpperBound(tpe1, tpe2)
            lazy val glb = greatestLowerBound(tpe1, tpe2)

            if      (tp.isCovariant)     Some(glb)
            else if (tp.isContravariant) Some(lub)
            else if (tpe1 == tpe2)       Some(tpe1)
            else                         None
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
    lazy val lub = leastUpperBound(t1, t2)
    t1.isTyped && t2.isTyped && (lub == t2.getType || lub.getType == t2.getType)
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

    case (ta: TypeApply, _) if ta.lookupTypeDef.isEmpty => unsolvable
    case (_, ta: TypeApply) if ta.lookupTypeDef.isEmpty => unsolvable

    case (adt: ADTType, _) if adt.lookupSort.isEmpty => unsolvable
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => unsolvable

    case _ if t1 == t2 => Nil

    case (ct1: ClassType, ct2: ClassType) if ct1.tcd.cd == ct2.tcd.cd =>
      (ct1.tps zip ct2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))

    case (ta1: TypeApply, ta2: TypeApply) if ta1.selector == ta2.selector =>
      (ta1.tps zip ta2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))

    case (ta1: TypeApply, tp2) =>
      unificationConstraints(ta1.bounds, tp2, free)

    case (tp1, ta2: TypeApply) =>
      unificationConstraints(tp1, ta2.bounds, free)

    case (adt1: ADTType, adt2: ADTType) if adt1.id == adt2.id =>
      (adt1.tps zip adt2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))

    case (rt: RefinementType, _) => unificationConstraints(rt.getType, t2, free)
    case (_, rt: RefinementType) => unificationConstraints(t1, rt.getType, free)

    case (pi: PiType, _) => unificationConstraints(pi.getType, t2, free)
    case (_, pi: PiType) => unificationConstraints(t1, pi.getType, free)

    case (sigma: SigmaType, _) => unificationConstraints(sigma.getType, t2, free)
    case (_, sigma: SigmaType) => unificationConstraints(t1, sigma.getType, free)

    case (TypeBounds(lo, hi, _), tpe) if lo == hi => unificationConstraints(hi, tpe, free)
    case (tpe, TypeBounds(lo, hi, _)) if lo == hi => unificationConstraints(hi, tpe, free)

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

  def patternInType(pat: Pattern): Type = pat match {
    case WildcardPattern(ob) => ob.map(_.getType).getOrElse(AnyType())
    case LiteralPattern(_, lit) => lit.getType
    case ADTPattern(_, id, tps, _) =>
      lookupConstructor(id)
        .map(cons => ADTType(cons.sort, tps))
        .getOrElse(Untyped)
    case TuplePattern(_, subs) => TupleType(subs map patternInType)
    case ClassPattern(_, ct, subs) => ct
    case UnapplyPattern(_, recs, id, tps, _) =>
      lookupFunction(id)
        .filter(fd => fd.tparams.size == tps.size)
        // .filter(_.params.size == recs.size - 1)
        .map(_.typed(tps))
        .map(_.params.last.getType)
        .getOrElse(Untyped)
    case InstanceOfPattern(_, tpe) => tpe.getType
  }

  override def patternIsTyped(in: Type, pat: Pattern): Boolean = {
    require(in != Untyped)
    (in, pat) match {
      case (_, _) if !isSubtypeOf(patternInType(pat), in) =>
        pat.binder.forall(vd => isSubtypeOf(in, vd.getType)) &&
        patternIsTyped(patternInType(pat), pat)

      case (_, ClassPattern(ob, ct, subs)) => in match {
        case ct2 @ ClassType(id, tps) if isSubtypeOf(ct, ct2) =>
          lookupClass(ct.id).exists { cls =>
            cls.fields.size == subs.size &&
            cls.tparams.size == ct.tps.size &&
            (cls.typed(ct.tps).fields zip subs).forall { case (vd, sub) => patternIsTyped(vd.getType, sub) }
          }
        case _ => patternIsTyped(patternInType(pat), pat)
      }

      case (_, InstanceOfPattern(ob, tpe)) =>
        ob.forall(vd => isSubtypeOf(tpe.getType, vd.getType))

      case (AnyType(), _) =>
        if (patternInType(pat) == AnyType()) {
          pat.binders.forall(vd => isSubtypeOf(AnyType(), vd.getType))
        } else {
          patternIsTyped(patternInType(pat), pat)
        }

      case _ => super.patternIsTyped(in, pat)
    }
  }
}

