/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._

object TwoOptions {

  @cCode.`export`
  def twoOptions: Unit = {
    var opt1: Option[Long] = None()
    val opt2: Option[Int] = None()
    opt1.isEmpty
    opt2.isEmpty
  }

  @cCode.`export`
  def main() = {
  }

}
