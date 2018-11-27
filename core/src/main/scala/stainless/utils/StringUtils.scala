/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

object StringUtils {

  def indent(text: String, spaces: Int): String = {
    val prefix = " " * spaces
    text.lines.map(prefix ++ _).mkString("\n")
  }

}
