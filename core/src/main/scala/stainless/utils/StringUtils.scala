/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package utils

object StringUtils {

  def indent(text: String, spaces: Int): String = {
    val prefix = " " * spaces
    text.linesIterator.map(prefix ++ _).mkString("\n")
  }

}
