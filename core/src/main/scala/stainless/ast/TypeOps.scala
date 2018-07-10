/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

trait TypeOps extends inox.ast.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols._

  def unapplyAccessorResultType(id: Identifier, inType: Type): Option[Type] =
    lookupFunction(id)
      .filter(_.params.size == 1)
      .flatMap { fd =>
        instantiation(fd.params.head.tpe, inType)
          .filter(tpMap => fd.typeArgs forall (tpMap contains _))
          .map(typeOps.instantiateType(fd.returnType, _))
      }

  def patternIsTyped(in: Type, pat: Pattern): Boolean = pat match {
    case WildcardPattern(ob) => ob.forall(vd => isSubtypeOf(in, vd.tpe))

    case LiteralPattern(ob, lit) =>
      ob.forall(vd => isSubtypeOf(vd.tpe, in)) &&
      isSubtypeOf(lit.getType, in)

    case ADTPattern(ob, id, tps, subs) => in match {
      case ADTType(sort, tps2) =>
        tps == tps2 &&
        ob.forall(vd => isSubtypeOf(vd.tpe, in)) &&
        lookupConstructor(id).exists { cons =>
          cons.sort == sort &&
          cons.fields.size == subs.size &&
          lookupSort(sort).exists(sort => sort.tparams.size == tps.size) &&
          (cons.typed(tps).fields zip subs).forall { case (vd, sub) => patternIsTyped(vd.tpe, sub) }
        }
      case _ => false
    }

    case TuplePattern(ob, subs) => in match {
      case TupleType(tps) =>
        tps.size == subs.size &&
        ob.forall(vd => isSubtypeOf(vd.tpe, in)) && 
        ((tps zip subs) forall (patternIsTyped(_, _)).tupled)
      case _ => false
    }

    case up @ UnapplyPattern(ob, rec, id, tps, subs) =>
      ob.forall(vd => isSubtypeOf(vd.tpe, in)) &&
      lookupFunction(id).exists(_.tparams.size == tps.size) && {
        val unapp = up.getFunction
        (if (rec.isEmpty) {
          unapp.params.size == 1 &&
          ob.forall(vd => isSubtypeOf(unapp.params.head.tpe, vd.tpe))
        } else {
          unapp.params.size == 2 &&
          isSubtypeOf(rec.get.getType, unapp.params.head.tpe) &&
          ob.forall(vd => isSubtypeOf(unapp.params(1).tpe, vd.tpe))
        }) && unapp.flags
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
