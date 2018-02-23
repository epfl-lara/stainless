/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

trait TypeOps extends imperative.TypeOps {
  protected val trees: Trees
  import trees._

  protected def unionType(tps: Seq[Type]): Type = tps match {
    case Seq() => NothingType()
    case Seq(tp) => tp
    case tp1 +: tps =>
      tps.map(tp => tp1 -> tp).view.flatMap {
        case (tp1, tp2) => typeBound(tp1, tp2, true) match {
          case _: UnionType => None
          case ntpe => Some((tp1, tp2, ntpe))
        }
      }.headOption match {
        case Some((tp1, tp2, ntpe)) => unionType(ntpe +: tps.filter(tp => tp != tp1 && tp != tp2))
        case None => unionType(tps) match {
          case UnionType(tps) => UnionType(tp1 +: tps)
          case tp2 => UnionType(Seq(tp1, tp2))
        }
      }
  }

  protected def intersectionType(tps: Seq[Type]): Type = tps match {
    case Seq() => AnyType()
    case Seq(tp) => tp
    case tp1 +: tps =>
      tps.map(tp => tp1 -> tp).view.flatMap {
        case (tp1, tp2) => typeBound(tp1, tp2, false) match {
          case _: IntersectionType => None
          case ntpe => Some((tp1, tp2, ntpe))
        }
      }.headOption match {
        case Some((tp1, tp2, ntpe)) => intersectionType(ntpe +: tps.filter(tp => tp != tp1 && tp != tp2))
        case None => intersectionType(tps) match {
          case IntersectionType(tps) => IntersectionType(tp1 +: tps)
          case tp2 => IntersectionType(Seq(tp1, tp2))
        }
      }
  }

  protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = ((tp1, tp2) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => Some(Untyped)
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => Some(Untyped)
    case (ct1: ClassType, ct2: ClassType) =>
      val (c1, c2) = (ct1.tcd, ct2.tcd)

      if (upper) {
        val (an1, an2) = (c1 +: c1.ancestors, c2 +: c2.ancestors)
        val bounds = an1.find(_.cd == c2.cd).map(_ -> c2)
          .orElse(an2.find(_.cd == c1.cd).map(c1 -> _))

        bounds.flatMap { case (c1, c2) =>
          val tps = (c1.cd.typeArgs zip (c1.tps zip c2.tps)).map { case (tp, (t1, t2)) =>
            if (tp.isCovariant) typeBound(t1, t2, upper)
            else if (tp.isContravariant) typeBound(t1, t2, !upper)
            else if (t1 == t2) t1
            else Untyped
          }

          if ((tps zip (c1.tps zip c2.tps)).forall { case (tp, (t1, t2)) => tp == t1 || tp == t2 }) {
            Some(c1.cd.typed(tps).toType)
          } else {
            None
          }
        }
      } else {
        val (ds1, ds2) = (c1 +: c1.descendants, c2 +: c2.descendants)
        val bounds = ds1.find(_.cd == c2.cd).map(_ -> c2)
          .orElse(ds2.find(_.cd == c1.cd).map(c1 -> _))

        bounds.flatMap { case (c1, c2) =>
          val tps = (c1.cd.typeArgs zip (c1.tps zip c2.tps)).map { case (tp, (t1, t2)) =>
            if (t1 == tp) t2
            else if (t2 == tp) t1
            else if (tp.isCovariant) typeBound(t1, t2, upper)
            else if (tp.isContravariant) typeBound(t1, t2, !upper)
            else if (t1 == t2) t1
            else Untyped
          }

          if ((tps zip (c1.tps zip c2.tps)).forall { case (tp, (t1, t2)) => tp == t1 || tp == t2 }) {
            Some(c1.cd.typed(tps).toType)
          } else {
            None
          }
        }
      }

    case (adt: ADTType, _) if adt.lookupSort.isEmpty => Some(Untyped)
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => Some(Untyped)
    case (adt1: ADTType, adt2: ADTType) if adt1 == adt2 => Some(adt1)

    case (tp1: TypeParameter, tp2: TypeParameter) if tp1 == tp2 => Some(tp1)
    case (tp: TypeParameter, tpe) => Some(typeBound(tp.bounds, tpe, upper))
    case (tpe, tp: TypeParameter) => Some(typeBound(tpe, tp.bounds, upper))
    case (TypeBounds(lo, hi), tpe) => Some(typeBound(if (upper) hi else lo, tpe, upper))
    case (tpe, TypeBounds(lo, hi)) => Some(typeBound(tpe, if (upper) hi else lo, upper))

    case (tp, AnyType()) if tp.unveilUntyped.isTyped => Some(if (upper) AnyType() else tp)
    case (AnyType(), tp) if tp.unveilUntyped.isTyped => Some(if (upper) AnyType() else tp)
    case (NothingType(), tp) if tp.unveilUntyped.isTyped => Some(if (upper) tp else NothingType())
    case (tp, NothingType()) if tp.unveilUntyped.isTyped => Some(if (upper) tp else NothingType())

    case (UnionType(tps), tp) if upper => Some(unionType(tp +: tps))
    case (UnionType(tps), tp) if !upper => Some(unionType(tps.map(tpe => typeBound(tpe, tp, false))))
    case (tp, ut: UnionType) => Some(typeBound(ut, tp, upper))

    case (IntersectionType(tps), tp) if !upper => Some(intersectionType(tp +: tps))
    case (IntersectionType(tps), tp) if upper => Some(intersectionType(tps.map(tpe => typeBound(tpe, tp, true))))
    case (tp, it: IntersectionType) => Some(typeBound(it, tp, upper))

    case (FunctionType(from1, to1), FunctionType(from2, to2)) if from1.size == from2.size =>
      val in = (from1 zip from2).map { case (tp1, tp2) => typeBound(tp1, tp2, !upper) }
      val out = typeBound(to1, to2, upper)
      Some(FunctionType(in, out))

    case (TupleType(ts1), TupleType(ts2)) if ts1.size == ts2.size =>
      val tps = (ts1 zip ts2).map { case (tp1, tp2) => typeBound(tp1, tp2, upper) }
      Some(TupleType(tps))

    case (t1, t2) if t1 == t2 => Some(t1)

    case _ => None
  }).getOrElse(if (upper) UnionType(Seq(tp1, tp2)) else IntersectionType(Seq(tp1, tp2))).unveilUntyped

  /** Computes the tightest bound (upper or lower) of a sequence of types */
  private def typeBound(tps: Seq[Type], upper: Boolean): Type = {
    if (tps.isEmpty) Untyped
    else tps.reduceLeft(typeBound(_, _, upper))
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
    case (TypeBounds(lo, hi), tpe) if lo == hi => unificationConstraints(hi, tpe, free)
    case (tpe, TypeBounds(lo, hi)) if lo == hi => unificationConstraints(hi, tpe, free)
    case (tp: TypeParameter, _) if !(typeParamsOf(t2) contains tp) && (free contains tp) => List(tp -> t2)
    case (_, tp: TypeParameter) if !(typeParamsOf(t1) contains tp) && (free contains tp) => List(tp -> t1)
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
        (instantiateType(t1, Map(tp -> t)), instantiateType(t2, Map(tp -> t)))
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
}

