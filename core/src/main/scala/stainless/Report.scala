/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.utils.Position
import inox.utils.ASCIIHelpers.*
import io.circe.*
import io.circe.syntax.*
import stainless.extraction._
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
    ctx.reporter.info(emitSummary(ctx))
  }

  /** Create a new report with *only* the information about the given functions/classes/... */
  def filter(ids: Set[Identifier]): SelfType

  /** Merge two reports, considering [[other]] to contain the latest information in case of update. */
  def ~(other: SelfType): SelfType

  final def isSuccess: Boolean = stats.isValid

  protected type Level = Level.Type

  protected[stainless] def annotatedRows: Seq[RecordRow]
  protected[stainless] def extractionSummary: ExtractionSummary

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

  private def withColor(str: String, color: String, style: String = "")(using ctx: inox.Context): String =
    if (ctx.options.findOptionOrDefault(inox.optNoColors)) str
    else s"$style$color$str${Console.RESET}"

  private def colorOf(level: Level): String = level match {
    case Level.Normal  => Console.GREEN
    case Level.Warning => Console.YELLOW
    case Level.Error   => Console.RED
  }

  def hasError(identifier: Option[Identifier])(using inox.Context): Boolean = identifier match {
    case None => false
    case Some(i) => annotatedRows.exists(elem => elem match {
      case RecordRow(id, pos, level, extra, time) => {
        (level == Level.Error && id == i)
      }
    })
  }

  def hasUnknown(identifier: Option[Identifier])(using inox.Context): Boolean = identifier match {
    case None => false
    case Some(i) => annotatedRows.exists(elem => elem match {
      case RecordRow(id, pos, level, extra, time) => level == Level.Warning && id == i
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
      f"time: ${stats.time/1000d}%7.2f"

    var t = Table(withColor(s"$name summary", color))
    t ++= rows
    t += Separator
    t += Row(Seq(Cell(withColor(footer, color), spanning = width)))

    t
  }

  private def emitSummary(ctx: inox.Context): String = {
    given inox.Context = ctx
    def join(strs: Seq[String], prefix: String = "", sep: String = ", ", charsPerLine: Int = 80): String = {
      def loop(strs: Seq[String], currLine: String, prevLines: String): String = {
        def flushedCurrLine: String = {
          if (prevLines.isEmpty) prefix ++ currLine
          else if (currLine.isEmpty) prevLines
          else {
            val sep2 = if (prevLines.endsWith("\n" ++ prefix)) "" else sep
            prevLines ++ sep2 ++ currLine
          }
        }

        strs match {
          case Seq() => flushedCurrLine
          case str +: rest =>
            val newLine = prefix.length + currLine.length + str.length >= charsPerLine &&
              prefix.length + str.length <= charsPerLine // To guard against strings that are over charsPerLine long

            if (newLine) {
              val newPrevLines = flushedCurrLine ++ sep ++ "\n" ++ prefix
              loop(rest, str, newPrevLines)
            } else {
              val newCurrLine = if (currLine.isEmpty) str else currLine ++ sep ++ str
              loop(rest, newCurrLine, prevLines)
            }
        }
      }
      loop(strs, "", "")
    }
    def withMultilineColor(str: String, color: String, style: String = ""): String = {
      if (ctx.options.findOptionOrDefault(inox.optNoColors)) str // To not unnecessarily process a string that would result in itself anyway...
      else str.split("\n").map(withColor(_, color, style)).mkString("\n")
    }

    val sd = prepareExtractionSummaryData
    val admitted = ctx.options.findOptionOrDefault(verification.optAdmitVCs)
    val termOff = ctx.options.findOptionOrDefault(stainless.termination.optCheckMeasures).isNo
    val oldVC = !ctx.options.findOptionOrDefault(verification.optTypeChecker)
    val cache = ctx.options.findOptionOrDefault(verification.optVCCache)
    val solvers = ctx.options.findOptionOrDefault(inox.optSelectedSolvers).toSeq.sorted.mkString(", ")
    val batched = ctx.options.findOptionOrDefault(frontend.optBatchedProgram)

    if (isExtendedSummaryOn) {
      val admitStr = if (admitted) withColor("Admitted VCs", Console.RED, Console.BOLD) else ""
      val termOffStr = if (termOff) withColor("Termination turned off", Console.RED, Console.BOLD) else ""
      val oldVCStr = if (oldVC) withColor("Old VCs generation", Console.RED, Console.BOLD) else ""
      val cacheStr = if (cache) "Cache used" else ""

      def touched(sentance: String, ids: Set[Identifier], prefix: String): String =
        s"""$sentance
           |${join(ids.toSeq.map(_.name).sorted, prefix = prefix)}""".stripMargin

      def touchedFns(phaseName: String, fns: Set[Identifier]): String =
        touched(s"$phaseName phase transformed the following functions:", fns, " " * 4)

      val aaStr = if (sd.antiAliasing.hasRun) touchedFns("Anti-aliasing", sd.antiAliasing.affectedFns) else ""
      val reStr = if (sd.retAndWhileTran.hasReturnRun) touchedFns("Return transformation", sd.retAndWhileTran.retAffectedFns) else ""
      val weStr = if (sd.retAndWhileTran.hasWhileRun) touchedFns("While transformation", sd.retAndWhileTran.whileAffectedFns) else ""
      val ieStr = if (sd.imperativeElim.hasRun) touchedFns("Imperative elimination", sd.imperativeElim.affectedFns) else ""
      val teStr = if (sd.typeEncoding.hasRun) {
        val te = sd.typeEncoding
        val fns = if (te.affectedFns.nonEmpty) touched("-Functions:", te.affectedFns, " " * 6) else ""
        val sorts = if (te.affectedSorts.nonEmpty) touched("-Sorts:", te.affectedSorts, " " * 6) else ""
        val classes = if (te.classes.nonEmpty) touched("-Classes:", te.classes, " " * 6) else ""
        val items = Seq(fns, sorts, classes).filter(_.nonEmpty).mkString(" " * 4, "\n    ", "")
        s"""Type-encoding transformed the following:
           |$items""".stripMargin
      } else ""
      val ceStr = if (sd.chooseInjection.hasRun) {
        val ce = sd.chooseInjection
        val user = if (ce.affectedUserFns.nonEmpty) withMultilineColor(touched("-User:", ce.affectedUserFns, " " * 6), Console.YELLOW, Console.BOLD) else ""
        val lib = if (ce.affectedLibFns.nonEmpty) touched("-Library:", ce.affectedLibFns, " " * 6) else ""
        val items = Seq(user, lib).filter(_.nonEmpty).mkString(" " * 4, "\n    ", "")
        s"""Choose injected in the following functions:
           |$items""".stripMargin
      } else ""

      val solversUsed = s"Solvers used: $solvers"
      val procMode = s"Processing mode: ${if (batched) "batched" else "partial"}"

      val items = Seq(admitStr, termOffStr, oldVCStr, cacheStr, aaStr, reStr, weStr, ieStr, teStr, ceStr, solversUsed, procMode).filter(_.nonEmpty)
      s"""Verification pipeline summary:
         |${items.mkString("  ", "\n  ", "")}""".stripMargin // No join(items) here as their sub-items are already split according to the character limit
    } else {
      val admitStr = if (admitted) withColor("admitted VCs", Console.RED, Console.BOLD) else ""
      val termOffStr = if (termOff) withColor("termination off", Console.RED, Console.BOLD) else ""
      val oldVCStr = if (oldVC) withColor("old VCs gen", Console.RED, Console.BOLD) else ""
      val cacheStr = if (cache) "cache" else ""
      val aaStr = if (sd.antiAliasing.hasRun) "anti-aliasing" else ""
      val reStr = if (sd.retAndWhileTran.hasReturnRun) "return transformation" else ""
      val weStr = if (sd.retAndWhileTran.hasWhileRun) "while transformation" else ""
      val ieStr = if (sd.imperativeElim.hasRun) "imperative elimination" else ""
      val teStr = if (sd.typeEncoding.hasRun) "type encoding" else ""
      val ceStr = if (sd.chooseInjection.hasRun) withColor("choose injection", Console.YELLOW, Console.BOLD) else ""
      val batchedStr = if (batched) "batched" else ""
      val items = Seq(admitStr, termOffStr, oldVCStr, cacheStr, aaStr, reStr, weStr, ieStr, teStr, ceStr, solvers, batchedStr).filter(_.nonEmpty)
      s"""Verification pipeline summary:
         |${join(items, prefix = "  ")}""".stripMargin
    }
  }

  private case class SummaryData(
    antiAliasing: imperative.AntiAliasing.SummaryData = imperative.AntiAliasing.SummaryData(),
    retAndWhileTran: imperative.ReturnElimination.SummaryData = imperative.ReturnElimination.SummaryData(),
    imperativeElim: imperative.ImperativeCodeElimination.SummaryData = imperative.ImperativeCodeElimination.SummaryData(),
    typeEncoding: oo.TypeEncoding.SummaryData = oo.TypeEncoding.SummaryData(),
    chooseInjection: inlining.ChooseInjector.SummaryData = inlining.ChooseInjector.SummaryData(),
  ) {
    def ++(other: SummaryData): SummaryData = SummaryData(
      antiAliasing ++ other.antiAliasing,
      retAndWhileTran ++ other.retAndWhileTran,
      imperativeElim ++ other.imperativeElim,
      typeEncoding ++ other.typeEncoding,
      chooseInjection ++ other.chooseInjection
    )
    def +(other: imperative.AntiAliasing.SummaryData): SummaryData = copy(antiAliasing = antiAliasing ++ other)
    def +(other: imperative.ReturnElimination.SummaryData): SummaryData = copy(retAndWhileTran = retAndWhileTran ++ other)
    def +(other: imperative.ImperativeCodeElimination.SummaryData): SummaryData = copy(imperativeElim = imperativeElim ++ other)
    def +(other: oo.TypeEncoding.SummaryData): SummaryData = copy(typeEncoding = typeEncoding ++ other)
    def +(other: inlining.ChooseInjector.SummaryData): SummaryData = copy(chooseInjection = chooseInjection ++ other)
  }

  private def prepareExtractionSummaryData: SummaryData = {
    extractionSummary.leafs.foldLeft(SummaryData()) {
      case (acc, l@ExtractionSummary.Leaf(extraction.imperative.AntiAliasing)) =>
        acc + l.summary.asInstanceOf[extraction.imperative.AntiAliasing.SummaryData]

      case (acc, l@ExtractionSummary.Leaf(extraction.imperative.ReturnElimination)) =>
        acc + l.summary.asInstanceOf[extraction.imperative.ReturnElimination.SummaryData]

      case (acc, l@ExtractionSummary.Leaf(extraction.imperative.ImperativeCodeElimination)) =>
        acc + l.summary.asInstanceOf[extraction.imperative.ImperativeCodeElimination.SummaryData]

      case (acc, l@ExtractionSummary.Leaf(extraction.oo.TypeEncoding)) =>
        acc + l.summary.asInstanceOf[extraction.oo.TypeEncoding.SummaryData]

      case (acc, l@ExtractionSummary.Leaf(extraction.inlining.ChooseInjector)) =>
        acc + l.summary.asInstanceOf[extraction.inlining.ChooseInjector.SummaryData]

      case (acc, _) => acc
    }
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
  override val extractionSummary = ExtractionSummary.NoSummary
  override val stats = ReportStats(0, 0, 0, 0, 0, 0)
  override def filter(ids: Set[Identifier]) = this
  override def ~(other: NoReport) = this
}

