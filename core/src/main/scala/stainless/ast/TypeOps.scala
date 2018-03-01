/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

trait TypeOps extends inox.ast.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols._

  def patternIsTyped(in: Type, pat: Pattern): Boolean = pat match {
    case WildcardPattern(ob) => ob.forall(vd => isSubtypeOf(in, vd.tpe))

    case LiteralPattern(ob, lit) =>
      ob.forall(vd => isSubtypeOf(vd.tpe, in)) &&
      isSubtypeOf(lit.getType, in)

    case ADTPattern(ob, id, tps, subs) => in match {
      case ADTType(sort, tps2) =>
        tps == tps2 &&
        ob.forall(vd => isSubtypeOf(in, vd.tpe)) &&
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

    case up @ UnapplyPattern(ob, id, tps, subs) =>
      ob.forall(vd => isSubtypeOf(vd.tpe, in)) &&
      lookupFunction(id).exists(_.tparams.size == tps.size) && {
        val unapp = up.getFunction
        unapp.params.size == 1 &&
        ob.forall(vd => isSubtypeOf(unapp.params.head.tpe, vd.tpe)) &&
        unapp.flags
          .collectFirst { case IsUnapply(isEmpty, get) => (isEmpty, get) }
          .exists { case (isEmpty, get) =>
            lookupFunction(isEmpty).exists { isEmpty =>
              isEmpty.params.size == 1 && {
                val tpMap = instantiation(isEmpty.params.head.tpe, unapp.returnType)
                tpMap.isDefined &&
                (isEmpty.typeArgs forall (tpMap.get contains _)) &&
                isEmpty.returnType == BooleanType()
              }
            } && lookupFunction(get).exists { get =>
              get.params.size == 1 && {
                val tpMap = instantiation(get.params.head.tpe, unapp.returnType)
                tpMap.isDefined &&
                (get.typeArgs forall (tpMap.get contains _)) && {
                  val tfd = get.typed(get.typeArgs map tpMap.get)
                  get.returnType match {
                    case TupleType(tps) =>
                      tps.size == subs.size &&
                      ((tps.map(tfd.instantiate) zip subs) forall (patternIsTyped(_, _)).tupled)
                    case tpe if subs.size == 1 =>
                      patternIsTyped(tfd.instantiate(tpe), subs.head)
                    case _ => false
                  }
                }
              }
            }
          }
      }
  }
}
