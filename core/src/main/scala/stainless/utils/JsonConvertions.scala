/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package utils

import inox.utils.{ NoPosition, OffsetPosition, Position, RangePosition }

import java.io.File

import org.json4s.JsonDSL._
import org.json4s.JsonAST._

/**
 * Provide basic tools to convert some stainless/inox data into
 * JSON format.
 */
object JsonConvertions {

  private def pos2JsonImpl(pos: OffsetPosition): JObject = {
    ("line" -> pos.line) ~ ("col" -> pos.col) ~
    ("point" -> pos.point) ~ ("fullpath" -> pos.file.getAbsolutePath)
  }

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

  def parsePosition(json: JValue): Position = json match {
    case JString("Unknown") => NoPosition
    case json @ JObject(fields) if fields exists { _._1 == "begin" } =>
      val start = parsePosition(json \ "begin")
      val end = parsePosition(json \ "end")
      Position.between(start, end)

    case json =>
      val JInt(line) = json \ "line"
      val JInt(col) = json \ "col"
      val JInt(point) = json \ "point"
      val JString(path) = json \ "fullpath"
      val file = new File(path)
      OffsetPosition(line.intValue, col.intValue, point.intValue, file)
  }

  implicit class Identifier2Json(id: Identifier) {
    def toJson: JValue = ("name" -> id.name) ~ ("gid" -> id.globalId) ~ ("id" -> id.id)
  }

  def parseIdentifier(json: JValue): Identifier = {
    val JString(name) = json \ "name"
    val JInt(gid) = json \ "gid"
    val JInt(id) = json \ "id"

    new Identifier(name, gid.intValue, id.intValue)
  }
}

