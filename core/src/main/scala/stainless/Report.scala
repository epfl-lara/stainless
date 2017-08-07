/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import inox.utils.ASCIIHelpers._
import org.json4s.JsonAST.JArray

case class ReportStats(total: Int, time: Long, valid: Int, validFromCache: Int, invalid: Int, unknown: Int) {
  def +(more: ReportStats) = ReportStats(
    total + more.total,
    time + more.time,
    valid + more.valid,
    validFromCache + more.validFromCache,
    invalid + more.invalid,
    unknown + more.unknown
  )
}

trait AbstractReport { self =>
  val name: String
  def emitJson: JArray

  protected def emitRowsAndStats: Option[(Seq[Row], ReportStats)]

  final def emit(ctx: inox.Context): Unit = emitTable match {
    case None => ctx.reporter.info("No verification conditions were analyzed.")
    case Some(t) => ctx.reporter.info(t.render)
  }

  def ~(other: AbstractReport) = new AbstractReport {
    assert(other.width == self.width)

    override val name = if (self.name == other.name) self.name else self.name + " ~ " + other.name

    override def emitJson: JArray = {
      val JArray(as) = self.emitJson
      val JArray(bs) = other.emitJson
      JArray(as ++ bs)
    }

    override val width = self.width

    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = (self.emitRowsAndStats, other.emitRowsAndStats) match {
      case (None, None) => None
      case (a, None) => a
      case (None, b) => b
      case (Some((rowsA, statsA)), Some((rowsB, statsB))) => Some((rowsA ++ rowsB, statsA + statsB))
    }
  }

  protected val width: Int

  private def emitTable: Option[Table] = emitRowsAndStats map { case (rows, stats) =>
    var t = Table(s"$name summary")
    t ++= rows
    t += Separator
    t += Row(Seq(
      Cell(
        f"total: ${stats.total}%-4d   valid: ${stats.valid}%-4d (${stats.validFromCache} from cache)   " +
        f"invalid: ${stats.invalid}%-4d   unknown: ${stats.unknown}%-4d  " +
        f"time: ${stats.time/1000d}%7.3f",
        spanning = width
      )
    ))

    t
  }
}

object NoReport extends AbstractReport {
  override val name = "no-report"
  override def emitJson = JArray(Nil)
  override def emitRowsAndStats = None
  override val width = 0
}


