/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import inox.utils.ASCIIHelpers._
import io.circe.Json

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

/**
 * Text version of [[AbstractAnalysis]] that holds the basic information a user might be interested in.
 *
 * Provide facilities for I/O serialisation (through a JSON interface), generating a human-readable view
 * of the results (through an ASCCI table) and the ability to maintain an up-to-date view of the results
 * by means of concatenation of reports and invalidation of some part of the report itself.
 *
 * [[SelfType]] is used for typechecking purposes: it should denote the subclass itself. E.g.:
 * class SpecificReport extends AbstractReport[SpecificReport] { /* ... */ }
 */
trait AbstractReport[SelfType <: AbstractReport[SelfType]] { self: SelfType =>
  val name: String // The same name as the [[AbstractAnalysis]] this report was derived from.

  def emitJson: Json

  /** Create a new report with *only* the information about the given functions/classes/... */
  def filter(ids: Set[Identifier]): SelfType

  /** Merge two reports, considering [[other]] to contain the latest information in case of update. */
  def ~(other: SelfType): SelfType

  def isSuccess: Boolean

  protected def emitRowsAndStats: Option[(Seq[Row], ReportStats)]

  final def emit(ctx: inox.Context): Unit = emitTable match {
    case None => ctx.reporter.info("No verification conditions were analyzed.")
    case Some(t) => ctx.reporter.info(t.render)
  }

  private def emitTable: Option[Table] = emitRowsAndStats map { case (rows, stats) =>
    val width = if (rows.isEmpty) 1 else rows.head.cellsSize // all rows must have the same size
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

object AbstractReportHelper {
  trait Record { val derivedFrom: Identifier }

  /**
   * Keep records which `id` are present in [[ids]], and returns the next generation counter.
   */
  def filter[R <: Record](records: Seq[R], ids: Set[Identifier], lastGen: Long): (Seq[R], Long) =
    (records filter { ids contains _.derivedFrom }, lastGen + 1)

  /**
   * Merge two sets of records [[R]] into one, and returns the next generation counter.
   *
   * Records in [[prevs]] which have the same `id` as the ones in [[news]] are removed.
   * The [[updater0]] function takes as first parameter the next generation counter.
   */
  def merge[R <: Record](prevs: Seq[R], news: Seq[R], lastGen: Long, updater0: Long => R => R): (Seq[R], Long) = {
    def buildMapping(subs: Seq[R]): Map[Identifier, Seq[R]] = subs groupBy { _.derivedFrom }

    val prev = buildMapping(prevs)
    val next0 = buildMapping(news)

    val updated = (prev.keySet & next0.keySet).nonEmpty
    val nextGen = if (updated) lastGen + 1 else lastGen
    val updater = updater0(nextGen)

    val next = next0 mapValues { records => records map updater }

    val fused = (prev ++ next).values.fold(Seq.empty) { _ ++ _ }

    (fused, nextGen)
  }
}

class NoReport extends AbstractReport[NoReport] { // can't do this CRTP with object...
  override val name = "no-report"
  override def emitJson = Json.arr()
  override def isSuccess = true
  override def emitRowsAndStats = None
  override def filter(ids: Set[Identifier]) = this
  override def ~(other: NoReport) = this
}

