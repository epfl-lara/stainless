/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.utils.Position
import inox.utils.ASCIIHelpers._

import io.circe._
import io.circe.syntax._

import stainless.utils.JsonConvertions.given

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

object Level extends Enumeration {
  type Type = Value
  val Error, Warning, Normal = Value
}

case class RecordRow(
  id: Identifier,
  pos: Position,
  level: Level.Type,
  extra: Seq[String],
  time: Long
)

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

  def stats: ReportStats

  final def emit(ctx: inox.Context): Unit = {
    val compact = isCompactModeOn(using ctx)
    val table = emitTable(!compact)(using ctx)
    val asciiOnly = ctx.options.findOptionOrDefault(inox.optNoColors)
    ctx.reporter.info(table.render(asciiOnly))
  }

  /** Create a new report with *only* the information about the given functions/classes/... */
  def filter(ids: Set[Identifier]): SelfType

  /** Merge two reports, considering [[other]] to contain the latest information in case of update. */
  def ~(other: SelfType): SelfType

  final def isSuccess: Boolean = stats.isValid

  protected type Level = Level.Type

  protected[stainless] def annotatedRows: Seq[RecordRow]

  /** Filter, sort & process rows. */
  private def processRows(full: Boolean)(using ctx: inox.Context): Seq[Row] = {
    val printUniqueName = ctx.options.findOptionOrDefault(inox.ast.optPrintUniqueIds)
    for {
      RecordRow(id, pos, level, extra, time) <- annotatedRows.sortBy(r => r.id -> r.pos)
      if full || level != Level.Normal
      name = if (printUniqueName) id.uniqueName else id.name
      contents = Position.smartPos(pos) +: (name +: (extra :+ f"${time / 1000d}%3.1f"))
    } yield Row(contents map { str => Cell(withColor(str, level)) })
  }

  private def withColor(str: String, level: Level)(using inox.Context): String =
    withColor(str, colorOf(level))

  private def withColor(str: String, color: String)(using ctx: inox.Context): String =
    if (ctx.options.findOptionOrDefault(inox.optNoColors)) str
    else s"$color$str${Console.RESET}"

  private def colorOf(level: Level): String = level match {
    case Level.Normal  => Console.GREEN
    case Level.Warning => Console.YELLOW
    case Level.Error   => Console.RED
  }

  def hasError(identifier: Identifier)(using inox.Context): Boolean = {
    annotatedRows.exists(elem => elem match {
      case RecordRow(id, pos, level, extra, time) => level == Level.Error && id == identifier
    })
  }

  def hasUnknown(identifier: Identifier)(using inox.Context): Boolean = {
    annotatedRows.exists(elem => elem match {
      case RecordRow(id, pos, level, extra, time) => level == Level.Warning && id == identifier
    })
  }

  // Emit the report table, with all VCs when full is true, otherwise only with unknown/invalid VCs.
  private def emitTable(full: Boolean)(using inox.Context): Table = {
    val rows  = processRows(full)
    val width = if (rows.isEmpty) 1 else rows.head.cellsSize // all rows must have the same size
    val color = if (isSuccess) Console.GREEN else Console.RED

    val footer =
      f"total: ${stats.total}%-4d " +
      f"valid: ${stats.valid}%-4d (${stats.validFromCache} from cache) " +
      f"invalid: ${stats.invalid}%-4d " +
      f"unknown: ${stats.unknown}%-4d " +
      f"time: ${stats.time/1000d}%7.1f"

    var t = Table(withColor(s"$name summary", color))
    t ++= rows
    t += Separator
    t += Row(Seq(Cell(withColor(footer, color), spanning = width)))

    t
  }
}

// Provide all the logic for typical Report.
trait BuildableAbstractReport[Record <: AbstractReportHelper.Record,
                              SelfType <: BuildableAbstractReport[Record, SelfType]]
  extends AbstractReport[SelfType] { self: SelfType =>

  protected val encoder: Encoder[Record]
  given Encoder[Record] = encoder

  protected val results: Seq[Record]
  protected val sources: Set[Identifier]

  // Somewhat similar to a regular clone, but more factory-like.
  protected def build(results: Seq[Record], sources: Set[Identifier]): SelfType

  final override def ~(other: SelfType) = build(
    AbstractReportHelper.merge(this.results, other.sources, other.results),
    this.sources ++ other.sources
  )

  final override def filter(ids: Set[Identifier]) = build(
    AbstractReportHelper.filter(results, ids),
    sources & ids
  )

  final override def emitJson: Json = (results, sources).asJson
}

object AbstractReportHelper {
  trait Record { val derivedFrom: Identifier }

  /**
   * Keep records which are derived from one of the given identifiers.
   */
  def filter[R <: Record](records: Seq[R], ids: Set[Identifier]): Seq[R] =
    records filter { ids contains _.derivedFrom }

  /**
   * Merge two sets of records [[R]] into one, keeping only the latest information.
   *
   * Obselete records for a source X are removed from [[prevs]]
   * and replaced by the ones in [[news]] (if it contains some records for X).
   */
  def merge[R <: Record](prevs: Seq[R], newSources: Set[Identifier], news: Seq[R]): Seq[R] = {
    def buildMapping(subs: Seq[R]): Map[Identifier, Seq[R]] = subs groupBy { _.derivedFrom }

    val prev = buildMapping(prevs) -- newSources // erase all the obselete information
    val next = buildMapping(news)
    val fused = (prev ++ next).values.fold(Seq.empty) { _ ++ _ }

    fused
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

