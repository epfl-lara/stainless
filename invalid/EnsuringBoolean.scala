/* Copyright 2009-2016 EPFL, Lausanne */

import leon._
import leon.lang._
import leon.annotation._
import scala.language.postfixOps 
object EnsuringBoolean {
  def congR(x: BigInt)(implicit mod: BigInt): Unit = {
    require(mod >= 1);
    ()
  } ensuring(false)
}
