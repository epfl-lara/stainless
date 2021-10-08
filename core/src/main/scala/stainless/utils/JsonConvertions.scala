/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import inox.utils.{ NoPosition, OffsetPosition, Position, RangePosition }

import java.io.File

import io.circe._
import io.circe.syntax._
import io.circe.generic.semiauto._

/**
 * Provide basic tools to convert some stainless/inox data into
 * JSON format.
 */
object JsonConvertions {

  private object PositionHelpers {
    sealed abstract class Kind
    case object Unknown extends Kind
    case object Offset extends Kind
    case object Range extends Kind

    given kindEncoder: Encoder[Kind] = deriveEncoder
    given kindDecoder: Decoder[Kind] = deriveDecoder
  }

  import PositionHelpers._

  given positionDecoder: Decoder[Position] = Decoder.instance[Position] { cursor =>
    def impl(c: ACursor): Decoder.Result[Position] = for {
      line <- c.get[Int]("line")
      col <- c.get[Int]("col")
      point <- c.get[Int]("point")
      file <- c.get[String]("file")
    } yield OffsetPosition(line, col, point, new File(file))

    cursor.downField("kind").as[Kind] flatMap {
      case Unknown => Right(NoPosition)
      case Offset => impl(cursor)
      case Range =>
        for {
          begin <- impl(cursor.downField("begin"))
          end <- impl(cursor.downField("end"))
        } yield Position.between(begin, end)
    }
  }

  given positionEncoder: Encoder[Position] = Encoder.instance[Position] { pos =>
    def impl(p: OffsetPosition): Seq[(String, Json)] = Seq(
      "line" -> p.line.asJson,
      "col" -> p.col.asJson,
      "point" -> p.point.asJson,
      "file" -> p.file.getAbsolutePath.asJson
    )

    pos match {
      case NoPosition =>
        Json.obj("kind" -> (Unknown: Kind).asJson)
        // Mind the explicit cast.. It helps circe find the right implicit encoder.

      case pos @ OffsetPosition(_, _, _, file) =>
        Json.fromFields(("kind" -> (Offset: Kind).asJson) +: impl(pos))

      case range: RangePosition =>
        Json.obj(
          "kind" -> (Range: Kind).asJson,
          "begin" -> Json.fromFields(impl(range.focusBegin)),
          "end" -> Json.fromFields(impl(range.focusEnd))
        )
    }
  }

  given identifierDecoder: Decoder[Identifier] =
    Decoder.forProduct3[Identifier, String, Int, Int]("name", "gid", "id") {
      case (name, gid, id) => new Identifier(name, gid, id)
    }

  given identifierEncoder: Encoder[Identifier] =
    Encoder.forProduct3("name", "gid", "id") {
      (id: Identifier) => (id.name, id.globalId, id.id)
    }
}