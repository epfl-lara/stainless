/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package utils

import inox.utils.{ NoPosition, OffsetPosition, Position, RangePosition }

import org.json4s.JsonDSL._
import org.json4s.JsonAST.{ JObject, JValue }

/**
 * Provide basic tools to convert some stainless/inox data into
 * JSON format.
 */
object JsonConvertions {

  private def pos2JsonImpl(pos: OffsetPosition): JObject =
    ("line" -> pos.line) ~ ("col" -> pos.col)

  implicit class Position2Json(pos: Position) {
    def toJson: JValue = pos match {
      case NoPosition =>
        "Unknown"

      case pos @ OffsetPosition(_, _, _, file) =>
        pos2JsonImpl(pos) ~ ("file" -> file.getPath)

      case range: RangePosition =>
        ("begin" -> pos2JsonImpl(range.focusBegin)) ~
        ("end" -> pos2JsonImpl(range.focusEnd)) ~
        ("file" -> range.file.getPath)
    }
  }

}

