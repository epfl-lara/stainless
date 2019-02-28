/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package utils

object StringUtils {

  def indent(str: String, spaces: Int, firstLine: Boolean = true): String = {
    str.split("\n").zipWithIndex.map {
      case (line, 0) if !firstLine => line
      case (line, _) => (" " * spaces) + line
    }.mkString("\n")
  }

}
