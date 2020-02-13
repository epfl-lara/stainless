/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.codegen.runtime

object StringOps {

  def concat(s1: String, s2: String): String = s1 + s2

  def length(str: String): BigInt = new BigInt(str.length())

  def substring(str: String, start: BigInt, end: BigInt): String = {
    str.substring(start.toInt, end.toInt)
  }
}
