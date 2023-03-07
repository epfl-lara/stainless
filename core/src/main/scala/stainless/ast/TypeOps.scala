/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

trait TypeOps extends inox.ast.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols.{given, _}

  def unapplyAccessorResultType(id: Identifier, inType: Type): Option[Type] =
    lookupFunction(id)
      .filter(_.params.size == 1)
      .flatMap { fd =>
        instantiation(fd.params.head.tpe, inType)
          .filter(tpMap => fd.typeArgs forall (tpMap contains _))
          .map(typeOps.instantiateType(fd.returnType, _))
      }

  def patternIsTyped(in: Type, pat: Pattern): Boolean = {
    require(in != Untyped)
    pat match {
      case WildcardPattern(ob) => ob.forall(vd => isSubtypeOf(in, vd.getType))

      case LiteralPattern(ob, lit) =>
        ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
        isSubtypeOf(lit.getType, in)

      case ADTPattern(ob, id, tps, subs) => in.getType match {
        case ADTType(sort, tps2) =>
          tps.map(_.getType) == tps2 &&
          ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
          lookupConstructor(id).exists { cons =>
            cons.sort == sort &&
            cons.fields.size == subs.size &&
            lookupSort(sort).exists(sort => sort.tparams.size == tps.size) &&
            (cons.typed(tps).fields zip subs).forall { case (vd, sub) => patternIsTyped(vd.getType, sub) }
          }
        case _ => false
      }

      case TuplePattern(ob, subs) => in match {
        case TupleType(tps) =>
          tps.size == subs.size &&
          ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
          ((tps zip subs) forall (patternIsTyped(_, _)).tupled)
        case _ => false
      }

      case up @ UnapplyPattern(ob, recs, id, tps, subs) =>
        ob.forall(vd => isSubtypeOf(vd.getType, in)) &&
        lookupFunction(id).exists(_.tparams.size == tps.size) && {
          val unapp = up.getFunction
          unapp.params.nonEmpty &&
          ob.forall(vd => isSubtypeOf(unapp.params.last.getType, vd.getType)) &&
          (recs zip unapp.params.init).forall { case (r, vd) => isSubtypeOf(r.getType, vd.getType) } &&
          unapp.flags
            .collectFirst { case IsUnapply(isEmpty, get) => (isEmpty, get) }
            .exists { case (isEmpty, get) =>
              unapplyAccessorResultType(isEmpty, unapp.returnType).exists(isSubtypeOf(_, BooleanType())) &&
              unapplyAccessorResultType(get, unapp.returnType).exists {
                case TupleType(tps) =>
                  tps.size == subs.size &&
                  ((tps zip subs) forall patternIsTyped.tupled)
                case tpe if subs.size == 1 =>
                  patternIsTyped(tpe, subs.head)
                case _ => subs.isEmpty
              }
            }
        }
    }
  }

  def replaceKeepPositions(subst: Map[Variable, Expr], tpe: Type): Type = {
    new ConcreteStainlessSelfTreeTransformer {
      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => subst.getOrElse(v, v).copiedFrom(v)
        case _ => super.transform(expr)
      }
    }.transform(tpe)
  }

  protected class Unsolvable extends Exception
  protected def unsolvable = throw new Unsolvable

  /** Collects the constraints that need to be solved for [[unify]].
   * Note: this is an override point. */
  protected def unificationConstraints(t1: Type, t2: Type, free: Seq[TypeParameter]): List[(TypeParameter, Type)] = (t1, t2) match {
    case (adt: ADTType, _) if adt.lookupSort.isEmpty => unsolvable
    case (_, adt: ADTType) if adt.lookupSort.isEmpty => unsolvable

    case _ if t1 == t2 => Nil

    case (adt1: ADTType, adt2: ADTType) if adt1.id == adt2.id =>
      (adt1.tps zip adt2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))

    case (rt: RefinementType, _) => unificationConstraints(rt.getType, t2, free)
    case (_, rt: RefinementType) => unificationConstraints(t1, rt.getType, free)

    case (pi: PiType, _) => unificationConstraints(pi.getType, t2, free)
    case (_, pi: PiType) => unificationConstraints(t1, pi.getType, free)

    case (sigma: SigmaType, _) => unificationConstraints(sigma.getType, t2, free)
    case (_, sigma: SigmaType) => unificationConstraints(t1, sigma.getType, free)

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

}
