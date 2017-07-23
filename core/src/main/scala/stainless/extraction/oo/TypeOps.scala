/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

trait TypeOps extends ast.TypeOps {
  protected val trees: Trees
  import trees._

  override protected def instantiationConstraints(toInst: Type, bound: Type, isUpper: Boolean): Constraint = (toInst, bound) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => False
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => False
    case (ct1: ClassType, ct2: ClassType) =>
      val (ctl, ctu) = if (isUpper) (ct1, ct2) else (ct2, ct1)
      ctu.tcd.ancestors.find(_.id == ctl.id).map { tcd =>
        Conjunction(for {
          (tp, (t1, t2)) <- tcd.cd.typeArgs zip (ctl.tps zip tcd.tps)
          variance <- if (tp.isCovariant) Seq(isUpper) else if (tp.isContravariant) Seq(!isUpper) else Seq(true, false)
        } yield instantiationConstraints(t1, t2, variance))
      }.getOrElse(False)

    // @nv: ADTs have to be invariant in the full type lattice!
    case (adt: ADTType, _) if !adt.isInstanceOf[ClassType] && adt.lookupADT.isEmpty => False
    case (_, adt: ADTType) if !adt.isInstanceOf[ClassType] && adt.lookupADT.isEmpty => False
    case (adt1: ADTType, adt2: ADTType) =>
      val (d1, d2) = (adt1.getADT.definition, adt2.getADT.definition)
      val (dl, du) = if (isUpper) (d1, d2) else (d2, d1)
      if (dl != du && dl.root != du) False
      else {
        Conjunction(for {
          (t1, t2) <- adt1.tps zip adt2.tps
          variance <- Seq(true, false) // invariant!
        } yield instantiationConstraints(t1, t2, variance))
      }

    case (TypeBounds(lo, hi), tpe) => instantiationConstraints(if (isUpper) hi else lo, tpe, isUpper)
    case (tpe, TypeBounds(lo, hi)) => instantiationConstraints(tpe, if (isUpper) hi else lo, isUpper)

    case (UnionType(tps), _) if isUpper => Conjunction(tps.map(instantiationConstraints(_, bound, true)))
    case (IntersectionType(tps), _) if isUpper => Disjunction(tps.map(instantiationConstraints(_, bound, true)))

    case (UnionType(tps), tpe) => instantiationConstraints(IntersectionType(tps), tpe, !isUpper)
    case (_, _: UnionType) => instantiationConstraints(bound, toInst, !isUpper)

    case (IntersectionType(tps), tpe) => instantiationConstraints(UnionType(tps), tpe, !isUpper)
    case (_, _: IntersectionType) => instantiationConstraints(bound, toInst, !isUpper)

    case (tp, AnyType) if tp.isTyped && isUpper => True
    case (AnyType, tp) if tp.isTyped && !isUpper => True
    case (NothingType, tp) if tp.isTyped && isUpper => True
    case (tp, NothingType) if tp.isTyped && !isUpper => True

    case _ => super.instantiationConstraints(toInst, bound, isUpper)
  }

  protected def unionType(tps: Seq[Type]): Type = tps match {
    case Seq() => NothingType
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
    case Seq() => AnyType
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

  override protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = ((tp1, tp2) match {
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

    // @nv: ADTs have to be invariant in the full type lattice!
    case (adt: ADTType, _) if !adt.isInstanceOf[ClassType] && adt.lookupADT.isEmpty => Some(Untyped)
    case (_, adt: ADTType) if !adt.isInstanceOf[ClassType] && adt.lookupADT.isEmpty => Some(Untyped)
    case (adt1: ADTType, adt2: ADTType) if adt1.tps == adt2.tps => // invariant!
      val (d1, d2) = (adt1.getADT.definition, adt2.getADT.definition)
      val (an1, an2) = (Seq(d1, d1.root), Seq(d2, d2.root))

      val bound = if (upper) {
        (an1.reverse zip an2.reverse)
          .takeWhile(((_: ADTDefinition) == (_: ADTDefinition)).tupled)
          .lastOption.map(_._1)
      } else {
        if (an1 contains d2) Some(d1)
        else if (an2 contains d1) Some(d2)
        else None
      }

      bound.map(_.typed(adt1.tps).toType)

    case (tp1: TypeParameter, tp2: TypeParameter) if tp1 == tp2 => Some(tp1)
    case (tp: TypeParameter, tpe) => Some(typeBound(tp.bounds, tpe, upper))
    case (tpe, tp: TypeParameter) => Some(typeBound(tpe, tp.bounds, upper))
    case (TypeBounds(lo, hi), tpe) => Some(typeBound(if (upper) hi else lo, tpe, upper))
    case (tpe, TypeBounds(lo, hi)) => Some(typeBound(tpe, if (upper) hi else lo, upper))

    case (tp, AnyType) if tp.unveilUntyped.isTyped => Some(if (upper) AnyType else tp)
    case (AnyType, tp) if tp.unveilUntyped.isTyped => Some(if (upper) AnyType else tp)
    case (NothingType, tp) if tp.unveilUntyped.isTyped => Some(if (upper) tp else NothingType)
    case (tp, NothingType) if tp.unveilUntyped.isTyped => Some(if (upper) tp else NothingType)

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

  override protected def unificationConstraints(t1: Type, t2: Type, free: Seq[TypeParameter]): List[(TypeParameter, Type)] = (t1, t2) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => unsolvable
    case (ct1: ClassType, ct2: ClassType) if ct1.tcd.cd == ct2.tcd.cd =>
      (ct1.tps zip ct2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case (TypeBounds(lo, hi), tpe) if lo == hi => unificationConstraints(hi, tpe, free)
    case (tpe, TypeBounds(lo, hi)) if lo == hi => unificationConstraints(hi, tpe, free)
    case _ => super.unificationConstraints(t1, t2, free)
  }

  override protected def unificationSolution(const: List[(Type, Type)]): List[(TypeParameter, Type)] = const match {
    case (ct: ClassType, _) :: tl if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) :: tl if ct.lookupClass.isEmpty => unsolvable
    case (ClassType(id1, tps1), ClassType(id2, tps2)) :: tl if id1 == id2 =>
      unificationSolution((tps1 zip tps2).toList ++ tl)
    case _ => super.unificationSolution(const)
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

