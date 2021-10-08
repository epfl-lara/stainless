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
                  ((tps zip subs) forall (patternIsTyped(_, _)).tupled)
                case tpe if subs.size == 1 =>
                  patternIsTyped(tpe, subs.head)
                case UnitType() if subs.isEmpty => true
                case _ => false
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

}
