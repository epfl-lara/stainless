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

trait AbstractReport[SelfType <: AbstractReport[_]] { self =>
  val name: String

  def emitJson: JArray

  /** Create a new report without information about the given functions/classes/.... */
  def removeSubreports(ids: Seq[Identifier]): SelfType

  /** Merge two reports, considering [[other]] to contain the last information in case of update. */
  def ~(other: SelfType): SelfType

  protected def emitRowsAndStats: Option[(Seq[Row], ReportStats)]

  final def emit(ctx: inox.Context): Unit = emitTable match {
    case None => ctx.reporter.info("No verification conditions were analyzed.")
    case Some(t) => ctx.reporter.info(t.render)
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

class NoReport extends AbstractReport[NoReport] { // can't do this CRTP with object...
  override val name = "no-report"
  override def emitJson = JArray(Nil)
  override def emitRowsAndStats = None
  override val width = 0
  override def removeSubreports(ids: Seq[Identifier]) = this
  override def ~(other: NoReport) = this
}

object NoReport {
  def apply() = new NoReport
}


