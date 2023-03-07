/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.utils.Position
import inox.utils.ASCIIHelpers.*
import io.circe.*
import io.circe.syntax.*
import stainless.extraction.*
import stainless.utils.JsonConvertions.given

case class ReportStats(total: Int, time: Long, valid: Int, validFromCache: Int, trivial: Int, invalid: Int, unknown: Int) {
  def +(more: ReportStats) = ReportStats(
    total + more.total,
    time + more.time,
    valid + more.valid,
    validFromCache + more.validFromCache,
    trivial + more.trivial,
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

  private def redBold(msg: String)(using ctx: inox.Context): String = withColor(msg, Console.RED, Console.BOLD)

  private def yellowBold(msg: String)(using ctx: inox.Context): String = withColor(msg, Console.YELLOW, Console.BOLD)

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
      f"valid: ${stats.valid}%-4d (${stats.validFromCache} from cache, ${stats.trivial} trivial) " +
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

    val sd = prepareExtractionSummaryData
    val admitted = ctx.options.findOptionOrDefault(verification.optAdmitVCs)
    val termOff = ctx.options.findOptionOrDefault(stainless.termination.optCheckMeasures).isNo
    val explicitChoose = sd.constructsUsage.hasExplicitChoose
    val missingImpl = sd.constructsUsage.hasMissingImpl
    val externs = sd.constructsUsage.hasExtern
    val cache = ctx.options.findOptionOrDefault(verification.optVCCache)
    val solvers = ctx.options.findOptionOrDefault(inox.optSelectedSolvers).toSeq.sorted.mkString(", ")
    val batched = ctx.options.findOptionOrDefault(frontend.optBatchedProgram)

    val indent = 2
    if (isExtendedSummaryOn) {
      // Critical
      val admitStr = if (admitted) Some(redBold("Admitted VCs")) else None
      val termOffStr = if (termOff) Some(redBold("Termination turned off")) else None

      // Constructs usage
      val constructsSummary = usageConstructExtendedSummary(sd.constructsUsage, indent)
      // Cache
      val cacheStr = if (cache) Some("Cache used") else None
      // Transformations
      val transformationSummary = transformationExtendedSummary(sd, indent)
      // Misc
      val solversUsed = s"Solvers used: $solvers"
      val procMode = s"Processing mode: ${if (batched) "batched" else "partial"}"

      // Putting everything together
      val items =
        Seq(admitStr, termOffStr).flatten.map(indent.spaces + _) ++ // These needs to be indented
        constructsSummary.toSeq ++ // But neither constructsSummary nor transformationSummary
        cacheStr.toSeq.map(indent.spaces + _) ++
        transformationSummary.toSeq ++
        Seq(solversUsed, procMode).map(indent.spaces + _)
      s"""Verification pipeline summary:
         |${items.mkString("\n")}""".stripMargin // No join(items) here as their sub-items are already split according to the character limit
    } else {
      val admitStr = if (admitted) Some(redBold("admitted VCs")) else None
      val termOffStr = if (termOff) Some(redBold("termination off")) else None
      val explicitChooseStr = if (explicitChoose) Some(redBold("explicit choose")) else None
      val missingImplsStr = if (missingImpl) Some(redBold("missing implementations")) else None
      val externsStr = if (externs) Some(yellowBold("@extern")) else None
      val cacheStr = if (cache) Some("cache") else None
      val aaStr = if (sd.antiAliasing.hasRun) Some("anti-aliasing") else None
      val reStr = if (sd.retAndWhileTran.hasReturnRun) Some("return transformation") else None
      val weStr = if (sd.retAndWhileTran.hasWhileRun) Some("while transformation") else None
      val ieStr = if (sd.imperativeElim.hasRun) Some("imperative elimination") else None
      val teStr = if (sd.typeEncoding.hasRun) Some("type encoding") else None
      val ceStr = if (sd.chooseInjection.hasRun) Some(yellowBold("choose injection")) else None
      val batchedStr = if (batched) Some("batched") else Some("non-batched")
      val items = Seq(admitStr, termOffStr, explicitChooseStr, missingImplsStr, externsStr, cacheStr,
        aaStr, reStr, weStr, ieStr, teStr, ceStr, Some(solvers), batchedStr).flatten
      s"""Verification pipeline summary:
         |${join(items, prefix = indent.spaces)}""".stripMargin
    }
  }

  /*
  Build a summary as follows (here for @extern):
  The following definitions are @extern:
    -User:
      -Free functions:
        X, Y, Z (defined in X)
      -Class X:
        -Methods:
          X, Y, Z (defined in X)
        -Fields:
          F1, F2
      -Class Y (and its declaration): // note: this means that Y is itself annotated with @extern
        -Methods:
          X, Y, Z (defined in X)
        -Fields:
          F1, F2
    -Library:
      (same patterns)
  */
  private def usageConstructExtendedSummary(sd: xlang.ConstructsUsage.SummaryData, indent: Int)(using ctx: inox.Context): Option[String] = {
    import xlang.ConstructsUsage._
    // Either a FreeFunction or a MethodOrInner, unified into Fn
    enum Fn {
      case Inner(id0: Identifier, outer: Identifier)
      case Outer(id0: Identifier)
      def id: Identifier = this match {
        case Inner(id, _) => id
        case Outer(id) => id
      }
    }

    def summaryForConstruct(c: UsedConstruct): Option[String] = {
      def helper(isLib: Boolean, cu: ConstructsOccurrences): String = {
        val res =
          s"""${(indent + 2).spaces}-${if (isLib) "Library" else "User"}:
             |${Seq(freeFns(cu.freeFns, indent + 4), classes(cu.classes, indent + 4)).flatten.mkString("\n")}""".stripMargin
        if (isLib || c == UsedConstruct.NotImplemented) withMultilineColor(res, Console.YELLOW, Console.BOLD)
        else withMultilineColor(res, Console.RED, Console.BOLD)
      }

      val user = sd.userUsage.get(c).map(helper(false, _))
      val lib = sd.libUsage.get(c).map(helper(true, _))
      if (user.isEmpty && lib.isEmpty) None
      else {
        val header = {
          val msg = c match {
            case UsedConstruct.Extern => "The following definitions are @extern"
            case UsedConstruct.Choose => "The following definitions contain explicit choose"
            case UsedConstruct.NotImplemented => "The following definitions contain missing implementation"
          }
          val msg2 = s"${indent.spaces}-$msg:"
          val headerColor = {
            if (user.isEmpty || c == UsedConstruct.NotImplemented) Console.YELLOW
            else Console.RED
          }
          withColor(msg2, headerColor, Console.BOLD)
        }
        Some(Seq(Some(header), user, lib).flatten.mkString("\n"))
      }
    }

    def freeFns(freeFns: Set[FreeFunction], indent: Int): Option[String] =
      if (freeFns.isEmpty) None
      else {
        val fns = freeFns.map {
          case FreeFunction.Inner(id, outer) => Fn.Inner(id, outer)
          case FreeFunction.Outer(id) => Fn.Outer(id)
        }
        Some(listedFns(s"${indent.spaces}-Free functions:", fns, (indent + 2).spaces))
      }

    def classes(clss: Set[Class], indent: Int): Option[String] = {
      def helper(c: Class): String = {
        assert(c.isAffected)
        val declAffected = if (c.clsDeclAffected) " (and its declaration)" else ""
        val header = s"${indent.spaces}-Class ${c.id}$declAffected:"
        Seq(Some(header), methods(c.methods, indent + 2), fields(c.fields, indent + 2)).flatten.mkString("\n")
      }
      if (clss.isEmpty) None
      else Some(clss.toSeq.sortBy(_.id).map(helper).mkString("\n"))
    }

    def methods(meths: Set[MethodOrInner], indent: Int): Option[String] = {
      if (meths.isEmpty) None
      else {
        val ms = meths.map {
          case MethodOrInner.Inner(id, outer) => Fn.Inner(id, outer)
          case MethodOrInner.Method(id) => Fn.Outer(id)
        }
        Some(listedFns(s"${indent.spaces}-Methods:", ms, (indent + 2).spaces))
      }
    }

    def fields(ids: Set[Identifier], indent: Int): Option[String] = {
      if (ids.isEmpty) None
      else {
        Some(s"""${indent.spaces}-Fields:
           |${join(ids.toSeq.map(_.name).sorted, (indent + 2).spaces)}""".stripMargin)
      }
    }

    def listedFns(sentence: String, ids: Set[Fn], prefix: String): String = {
      val idsStr = ids.toSeq.sortBy(_.id).map {
        case Fn.Inner(id, outer) => s"${id.name} (defined in ${outer.name})"
        case Fn.Outer(id) => id.name
      }
      s"""$sentence
         |${join(idsStr, prefix = prefix)}""".stripMargin
    }

    val summary = UsedConstruct.values.flatMap(summaryForConstruct)
    if (summary.isEmpty) None else Some(summary.mkString("\n"))
  }

  /*
  Builds a summary as follows (here for anti-aliasing):
  -Anti-aliasing transformed the following functions:
    X, Y, Z, W, T

  For type-encoding, sorts and classes are also listed as follows:
  -Type-encoding transformed the following:
    -Functions:
      X, Y, Z
    -Sorts:
      X, Y, Z
    -Classes:
      X, Y, Z

  Finally, choose injection differentiate between user-defined and library-defined functions:
  -Choose injected in the following functions:
    -User:
      X, Y, Z
    -Library:
      X, Y, Z
  */
  private def transformationExtendedSummary(sd: SummaryData, indent: Int)(using inox.Context): Option[String] = {
    def listedFns(sentence: String, ids: Set[Identifier], indent: Int): Option[String] = {
      if (ids.isEmpty) None
      else {
        Some(s"""${indent.spaces}$sentence
            |${join(ids.toSeq.map(_.name).sorted, prefix = (indent + 2).spaces)}""".stripMargin)
      }
    }

    def transformedFns(phaseName: String, fns: Set[Identifier], indent: Int): Option[String] =
      listedFns(s"-$phaseName phase transformed the following functions:", fns, indent)

    val aaStr = transformedFns("Anti-aliasing", sd.antiAliasing.affectedFns, indent)
    val reStr = transformedFns("Return transformation", sd.retAndWhileTran.retAffectedFns, indent)
    val weStr = transformedFns("While transformation", sd.retAndWhileTran.whileAffectedFns, indent)
    val ieStr = transformedFns("Imperative elimination", sd.imperativeElim.affectedFns, indent)
    val teStr = if (sd.typeEncoding.hasRun) {
      val te = sd.typeEncoding
      val fns = listedFns("-Functions:", te.affectedFns, indent + 2)
      val sorts = listedFns("-Sorts:", te.affectedSorts, indent + 2)
      val classes = listedFns("-Classes:", te.classes, indent + 2)
      val items = Seq(fns, sorts, classes).flatten
      Some(s"""${indent.spaces}-Type-encoding transformed the following:
              |${items.mkString("\n")}""".stripMargin)
    } else None
    val ceStr = if (sd.chooseInjection.hasRun) {
      val ce = sd.chooseInjection
      val user = listedFns("-User:", ce.affectedUserFns, indent + 2).map(withMultilineColor(_, Console.YELLOW, Console.BOLD))
      val lib = listedFns("-Library:", ce.affectedLibFns, indent + 2)
      val items = Seq(user, lib).flatten
      Some(s"""${indent.spaces}${yellowBold("-Choose injected in the following functions:")}
              |${items.mkString("\n")}""".stripMargin)
    } else None

    val all = Seq(aaStr, reStr, weStr, ieStr, teStr, ceStr).flatten
    if (all.isEmpty) None
    else Some(all.mkString("\n"))
  }

  private def join(strs: Seq[String], prefix: String = "", sep: String = ", ", charsPerLine: Int = 80): String = {
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

  private def withMultilineColor(str: String, color: String, style: String = "")(using ctx: inox.Context): String = {
    if (ctx.options.findOptionOrDefault(inox.optNoColors)) str // To not unnecessarily process a string that would result in itself anyway...
    else str.split("\n").map(withColor(_, color, style)).mkString("\n")
  }

  private case class SummaryData(
    constructsUsage: xlang.ConstructsUsage.SummaryData = xlang.ConstructsUsage.SummaryData(),
    antiAliasing: imperative.AntiAliasing.SummaryData = imperative.AntiAliasing.SummaryData(),
    retAndWhileTran: imperative.ReturnElimination.SummaryData = imperative.ReturnElimination.SummaryData(),
    imperativeElim: imperative.ImperativeCodeElimination.SummaryData = imperative.ImperativeCodeElimination.SummaryData(),
    typeEncoding: oo.TypeEncoding.SummaryData = oo.TypeEncoding.SummaryData(),
    chooseInjection: inlining.ChooseInjector.SummaryData = inlining.ChooseInjector.SummaryData(),
  ) {
    def ++(other: SummaryData): SummaryData = SummaryData(
      constructsUsage ++ other.constructsUsage,
      antiAliasing ++ other.antiAliasing,
      retAndWhileTran ++ other.retAndWhileTran,
      imperativeElim ++ other.imperativeElim,
      typeEncoding ++ other.typeEncoding,
      chooseInjection ++ other.chooseInjection
    )
    def +(other: xlang.ConstructsUsage.SummaryData): SummaryData = copy(constructsUsage = constructsUsage ++ other)
    def +(other: imperative.AntiAliasing.SummaryData): SummaryData = copy(antiAliasing = antiAliasing ++ other)
    def +(other: imperative.ReturnElimination.SummaryData): SummaryData = copy(retAndWhileTran = retAndWhileTran ++ other)
    def +(other: imperative.ImperativeCodeElimination.SummaryData): SummaryData = copy(imperativeElim = imperativeElim ++ other)
    def +(other: oo.TypeEncoding.SummaryData): SummaryData = copy(typeEncoding = typeEncoding ++ other)
    def +(other: inlining.ChooseInjector.SummaryData): SummaryData = copy(chooseInjection = chooseInjection ++ other)
  }

  private def prepareExtractionSummaryData: SummaryData = {
    extractionSummary.leafs.foldLeft(SummaryData()) {
      case (acc, l@ExtractionSummary.Leaf(xlang.ConstructsUsage)) =>
        acc + l.summary.asInstanceOf[xlang.ConstructsUsage.SummaryData]

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

  extension (indent: Int) {
    private def spaces: String = " " * indent
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
  override val stats = ReportStats(0, 0, 0, 0, 0, 0, 0)
  override def filter(ids: Set[Identifier]) = this
  override def ~(other: NoReport) = this
}

