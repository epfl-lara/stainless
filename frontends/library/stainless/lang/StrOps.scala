/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang

import scala.language.implicitConversions

import stainless.annotation._

/**
 * @author Mikael
 */
object StrOps {
  @ignore
  def concat(a: String, b: String): String = {
    a + b
  }
  @ignore
  def bigLength(s: String): BigInt = {
    BigInt(s.length)
  }
  @ignore
  def bigSubstring(s: String, start: BigInt, end: BigInt): String = {
    s.substring(start.toInt, end.toInt)
  }
}

