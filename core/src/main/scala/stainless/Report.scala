/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import inox.utils.Position
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

  def isValid = unknown + invalid == 0
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

  final def emit(ctx: inox.Context): Unit = {
    val watch = isWatchModeOn(ctx)
    val table = emitTable(!watch)
    ctx.reporter.info(table.render)
  }

  /** Create a new report with *only* the information about the given functions/classes/... */
  def filter(ids: Set[Identifier]): SelfType

  /** Merge two reports, considering [[other]] to contain the latest information in case of update. */
  def ~(other: SelfType): SelfType

  final def isSuccess: Boolean = stats.isValid

  protected object Level extends Enumeration {
    type Type = Value
    val Error, Warning, Normal = Value
  }
  protected type Level = Level.Type

  protected case class RecordRow(
    id: Identifier,
    pos: Position,
    level: Level,
    extra: Seq[String],
    time: Long
  )

  protected def annotatedRows: Seq[RecordRow]
  protected def stats: ReportStats

  /** Filter, sort & process rows. */
  private def processRows(full: Boolean): Seq[Row] = {
    for {
      RecordRow(id, pos, level, extra, time) <- annotatedRows sortBy { r => r.id -> r.pos }
      if full || level != Level.Normal
      contents = (id.name +: extra) ++ Seq(pos.fullString, f"${time / 1000d}%3.3f")
    } yield Row(contents map { str => Cell(withColor(str, level)) })
  }

  private def withColor(str: String, level: Level): String = withColor(str, colorOf(level))
  private def withColor(str: String, color: String): String = color + str + Console.RESET
  private def colorOf(level: Level): String = level match {
    case Level.Normal => Console.GREEN
    case Level.Warning => Console.YELLOW
    case Level.Error => Console.RED
  }

  // Emit the report table, with all VCs when full is true, otherwise only with unknown/invalid VCs.
  private def emitTable(full: Boolean): Table = {
    val rows = processRows(full)
    val width = if (rows.isEmpty) 1 else rows.head.cellsSize // all rows must have the same size
    val color = if (isSuccess) Console.GREEN else Console.RED

    val footer =
      f"total: ${stats.total}%-4d " +
      f"valid: ${stats.valid}%-4d (${stats.validFromCache} from cache) " +
      f"invalid: ${stats.invalid}%-4d " +
      f"unknown: ${stats.unknown}%-4d " +
      f"time: ${stats.time/1000d}%7.3f"

    var t = Table(withColor(s"$name summary", color))
    t ++= rows
    t += Separator
    t += Row(Seq(Cell(withColor(footer, color), spanning = width)))

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
  override val emitJson = Json.arr()
  override val annotatedRows = Seq.empty
  override val stats = ReportStats(0, 0, 0, 0, 0, 0)
  override def filter(ids: Set[Identifier]) = this
  override def ~(other: NoReport) = this
}

