/* Copyright 2009-2021 EPFL, Lausanne */

import stainless._
import stainless.lang._
import stainless.annotation._
import scala.language.postfixOps

object EnsuringBoolean {
  def congR(x: BigInt)(implicit mod: BigInt): Unit = {
    require(mod >= 1);
    ()
  }.ensuring(false)
}
