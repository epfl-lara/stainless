/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait TypeOps extends methods.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols.{given, _}

  import ClassTypeAbs.{Local, Global}

  override protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = {
    (tp1, tp2) match {
      case (lct: LocalClassType, rct: LocalClassType) => {
        if (upper) lub(Local(lct), Local(rct))
        else glb(Local(lct), Local(rct))
      }.map(_.underlying).getOrElse(Untyped)

      case (lct: LocalClassType, rct: ClassType) => {
        if (upper) lub(Local(lct), Global(rct))
        else glb(Local(lct), Global(rct))
      }.map(_.underlying).getOrElse(Untyped)

      case (lct: ClassType, rct: LocalClassType) => {
        if (upper) lub(Global(lct), Local(rct))
        else glb(Global(lct), Local(rct))
      }.map(_.underlying).getOrElse(Untyped)

      case _ => super.typeBound(tp1, tp2, upper)
    }
  }

  private[this] def lub(ct1: ClassTypeAbs, ct2: ClassTypeAbs): Option[ClassTypeAbs] = {
    val cd1Ans = ct1.ancestors.map(_.id).toSet + ct1.id
    val cd2Ans = ct2.ancestors.map(_.id).toSet + ct2.id
    val ans1 = (ct1 +: ct1.ancestors).find(ct => cd2Ans contains ct.id)
    val ans2 = (ct2 +: ct2.ancestors).find(ct => cd1Ans contains ct.id)

    (ans1, ans2) match {
      case (Some(act1), Some(act2)) =>
        val tps = (act1.typeArgs zip (act1.tps zip act2.tps)).map {
          case (tp, (tpe1, tpe2)) if tp.isCovariant => Some(leastUpperBound(tpe1, tpe2))
          case (tp, (tpe1, tpe2)) if tp.isContravariant => Some(greatestLowerBound(tpe1, tpe2))
          case (tp, (tpe1, tpe2)) if tpe1 == tpe2 => Some(tpe1)
          case _ => None
        }
        if (tps.forall(_.isDefined)) Some(act1.applied(tps.map(_.get)))
        else None
      case _ => None
    }
  }

  private[this] def glb(ct1: ClassTypeAbs, ct2: ClassTypeAbs): Option[ClassTypeAbs] = {
    val cd1Ans = ct1.ancestors.map(_.id).toSet + ct1.id
    val cd2Ans = ct2.ancestors.map(_.id).toSet + ct2.id
    val (desc1, desc2) = {
      if (cd2Ans.contains(ct1.id)) (Some(ct2), Some(ct1))
      else if (cd1Ans.contains(ct2.id)) (Some(ct1), Some(ct2))
      else (None, None)
    }

    (desc1, desc2) match {
      case (Some(act1), Some(act2)) =>
        val tps = (act1.typeArgs zip (act1.tps zip act2.tps)).map {
          case (tp, (tpe1, tpe2)) if tp.isCovariant => Some(greatestLowerBound(tpe1, tpe2))
          case (tp, (tpe1, tpe2)) if tp.isContravariant => Some(leastUpperBound(tpe1, tpe2))
          case (tp, (tpe1, tpe2)) if tpe1 == tpe2 => Some(tpe1)
          case _ => None
        }
        if (tps.forall(_.isDefined)) Some(act1.applied(tps.map(_.get)))
        else None
      case _ => None
    }
  }
}
