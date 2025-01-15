/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object Acc {

  case class Acc(checking: Int, savings: Int)

  def putAside(x: Int, a: Acc): Acc = {
    require(x > 0 && notRed(a) && a.checking >= x)
    Acc(a.checking - x, a.savings + x)
  }.ensuring {
    r => notRed(r) && sameTotal(a, r)
  }


  def sameTotal(a1: Acc, a2: Acc): Boolean = {
    a1.checking + a1.savings == a2.checking + a2.savings
  }

  def notRed(a: Acc): Boolean = {
    a.checking >= 0 && a.savings >= 0
  }

}
