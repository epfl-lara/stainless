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
      ob.forall(vd => isSubtypeOf(in, vd.tpe)) &&
      isSubtypeOf(lit.getType, in)
    case ADTPattern(ob, id, tps, subs) =>
      ob.forall(vd => isSubtypeOf(in, vd.tpe)) &&
      lookupConstructor(id, tps).exists { tcons =>
        tcons.fields.size == subs.size &&
        (tcons.fields zip subs).forall { case (vd, sub) => patternIsTyped(vd.tpe, sub) }
      }
    case TuplePattern(ob, subs) =>
      ob.forall(vd => isSubtypeOf(in, vd.tpe)) && (in match {
        case TupleType(tps) =>
          tps.size == subs.size &&
          ((tps zip subs) forall (patternIsTyped(_, _)).tupled)
        case _ => false
      })
    case up @ UnapplyPattern(ob, id, tps, subs) =>
      ob.forall(vd => isSubtypeOf(in, vd.tpe)) &&
      lookupFunction(id).exists(_.tparams.size == tps.size) && {
        val unapp = up.getFunction
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
