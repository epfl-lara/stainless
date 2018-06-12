/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait TypeOps extends methods.TypeOps {
  protected val trees: Trees
  import trees._
  import symbols._

  // @romac - FIXME
  override protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = (tp1, tp2) match {
    case (lct: LocalClassType, rct: LocalClassType) if lct == rct => lct
    case (lct: LocalClassType, rct: LocalClassType) => Untyped
    case (lct: LocalClassType, rct) => rct
    case (lct, rct: LocalClassType) => lct
    case _ => super.typeBound(tp1, tp2, upper)
  }
}
