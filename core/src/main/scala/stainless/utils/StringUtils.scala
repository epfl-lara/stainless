/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

object StringUtils {

  def indent(text: String, spaces: Int): String = {
    require(spaces >= 0)

    val prefix = " " * spaces
    text.linesIterator.map(prefix ++ _).mkString("\n")
  }

  def trim(text: String, maxLength: Int): String = {
    require(maxLength >= 0)
    val trimmed = text.trim
    if (trimmed.length > maxLength) {
      trimmed.take(maxLength) + "..."
    } else {
      trimmed
    }
  }

}
