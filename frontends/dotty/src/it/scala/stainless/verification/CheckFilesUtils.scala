package stainless
package verification

import inox.utils.Position
import stainless.Utils.Solver
import stainless.verification.{VC, VCKind, VCResult, VCStatus}

import java.io.File
import java.nio.file.{FileSystems, Files}
import scala.util.Try
import scala.collection.immutable.{Map, Seq}

object CheckFilesUtils {

  case class ExpectedVCInfos(infosByScalaFile: Map[File, Seq[VCInfo]]) {
    def check[T <: ast.Trees, M](vc: VC[T], vcStatus: VCStatus[M]): Either[CheckFailure, ExpectedVCInfos] = {
      val filename = vc.getPos.file
      val gotInfo = VCInfo.of(vc, vcStatus)
      infosByScalaFile.get(filename) match {
        case Some(infos) =>
          val nbMatches = infos.count(_ == gotInfo)
          if (nbMatches == 0) Left(CheckFailure.NoOccurrence(gotInfo))
          else {
            // Note: If newInfos comes to be empty, we do not remove it from the map
            // so that potential incorrectly occurring VCs are tagged as NoOccurrence and not UnknownOrigin
            val newInfos = infos.diff(Seq(gotInfo))
            Right(ExpectedVCInfos(infosByScalaFile + (filename -> newInfos)))
          }
        case None =>
          Left(CheckFailure.UnknownOrigin(gotInfo))
      }
    }

    def ++(other: ExpectedVCInfos): ExpectedVCInfos = {
      require((infosByScalaFile.keySet & other.infosByScalaFile.keySet).isEmpty)
      ExpectedVCInfos(infosByScalaFile ++ other.infosByScalaFile)
    }

    def projected(f: File): Option[ExpectedVCInfos] =
      infosByScalaFile.get(f).map(infos => ExpectedVCInfos(Map(f -> infos)))

    def isEffectivelyEmpty: Boolean = infosByScalaFile.forall(_._2.isEmpty)
  }

  case class VCInfo(pos: Option[SimplePosition], fn: String, vcKind: VCKind | ClassInvariant, vcStatus: VCStatus[Nothing] | InvalidVC.type) {
    private def vcKindStr: String = vcKind match {
      case ClassInvariant(clsName) => s"class invariant: $clsName"
      case other => other.asInstanceOf[VCKind].name
    }
    private def vcStatusStr: String = vcStatus match {
      case InvalidVC => "invalid"
      case other => other.asInstanceOf[VCStatus[Nothing]].name
    }

    def pretty: String = {
      val posStr = pos.map(p => s"${p.line}:${p.column}").getOrElse("?:?")
      s"VC @ $posStr in function $fn of kind $vcKindStr with status $vcStatusStr"
    }

    /** This VC information as a line of a check file, which [[parse]] reads back. */
    def checkLine: String = {
      val posStr = pos.map(p => s"${p.line}:${p.column}").getOrElse("")
      // The check files write the unknown status as in the verification reports
      val statusStr = if (vcStatus == VCStatus.Unknown) "inconclusive" else vcStatusStr
      s"$posStr;$fn;$vcKindStr;$statusStr"
    }
  }
  object VCInfo {
    /** The information about `vc` with status `vcStatus` that check files record. */
    def of[T <: ast.Trees, M](vc: VC[T], vcStatus: VCStatus[M]): VCInfo =
      VCInfo(toTestPos(vc.getPos), vc.fid.name, toTestVCKind(vc.kind), toTestVCStatus(vcStatus))
  }

  // VCKind.AdtInvariant expects an Identifier, which we do not have in a text file.
  // We hence use this special-case wrapper to denote an "AdtInvariant with a string ADT identifier".
  // When comparing the obtained VCKind against the expected one, we must make sure to convert the
  // expected AdtInvariant to a ClassInvariant.
  case class ClassInvariant(clsName: String)

  // VCStatus.Invalid contains a counterexample. We cannot have one and use this object to denote an invalid VC
  // When comparing the obtained result against the expected VC status, we must ensure we account for this case
  object InvalidVC

  // See parsePosition for explanation
  case class SimplePosition(line: Int, column: Int, file: File)

  enum CheckFailure {
    case UnknownOrigin(vc: VCInfo)
    case NoOccurrence(vc: VCInfo)

    def pretty: String = this match {
      case UnknownOrigin(vc) => s"${vc.pretty} is not contained in a check file"
      case NoOccurrence(vc) => s"${vc.pretty} has no occurrences in the corresponding check file"
    }
  }

  object CheckFileError {
    case class FileNotFound(scalaFile: File)
    enum ParsingError {
      case InvalidPosition(checkFile: File, lineNr: Int, pos: String)
      case InvalidEntry(checkFile: File, lineNr: Int, line: String)
      case UnknownVCKind(checkFile: File, lineNr: Int, vcKind: String)
      case UnknownVCStatus(checkFile: File, lineNr: Int, vcStatus: String)
    }
  }
  import CheckFileError.*

  // Note: Regarding expectedVCInfos, it is entirely possible to not have
  // all solvers in the Map which can happen if e.g. we have checkfile.z3
  // and checkfile.princess but with cvc5 missing.
  // This may happen for tests which ignore a solver.
  // At that point, we do not know what test are ignored
  case class LoadingResult(notFound: Seq[FileNotFound],
                           errs: Map[File, Seq[ParsingError]], // Per check file
                           expectedVCInfosBySolver: Map[Solver, ExpectedVCInfos])

  /** The check file of `scalaFile` for `solver`: `X.check.<solver>` if it exists, and otherwise `X.check` if it
    * exists, which is shared by the solvers that do not have their own check file. */
  def checkFileOf(scalaFile: File, solver: Solver): Option[File] = {
    val chkFileBaseStr = scalaFile.getPath.replace(".scala", ".check")
    Seq(File(s"${chkFileBaseStr}.${solver.fileExt}"), File(chkFileBaseStr)).find(_.exists())
  }

  def load(scalaFiles: Seq[File]): LoadingResult = {
    def checkFilesOf(scalaFile: File): Option[Map[Solver, File]] = {
      val combined = Solver.values.flatMap(s => checkFileOf(scalaFile, s).map(s -> _)).toMap
      // See comment on LoadingResult w.r.t. totality of combined
      if (combined.isEmpty) None
      else Some(combined)
    }
    def getLines(f: File): Seq[String] = {
      val src = scala.io.Source.fromFile(f)
      try {
        src.getLines().toSeq // This materializes the lines, so we are safe to close the source
      } finally {
        src.close()
      }
    }

    val (notFoundErrs, chkFiles0) = scalaFiles.partitionMap { scalaFile =>
      checkFilesOf(scalaFile) match {
        case Some(chkFileBySolver) => Right(scalaFile -> chkFileBySolver)
        case None => Left(CheckFileError.FileNotFound(scalaFile))
      }
    }
    // Scala file -> check file, per solver
    val chkFiles: Map[File, Map[Solver, File]] = chkFiles0.toMap

    // Note: this expects the ExpectedVCInfos from the two map to be disjoint in their keys (cf. ExpectedVCInfos#++)
    def merge(m1: Map[Solver, ExpectedVCInfos], m2: Map[Solver, ExpectedVCInfos]): Map[Solver, ExpectedVCInfos] = {
      (m1.keySet ++ m2.keySet).foldLeft(Map.empty[Solver, ExpectedVCInfos]) { case (acc, solver) =>
        (m1.get(solver), m2.get(solver)) match {
          case (Some(infos1), Some(infos2)) => acc + (solver -> (infos1 ++ infos2))
          case (Some(infos1), None) => acc + (solver -> infos1)
          case (None, Some(infos2)) => acc + (solver -> infos2)
          case (None, None) => acc // Impossible, but to make compiler happy
        }
      }
    }

    val (expectedVCInfos, parsingErrors) = chkFiles.foldLeft((Map.empty[Solver, ExpectedVCInfos], Map.empty[File, Seq[ParsingError]])) {
      case ((accVCInfos, accErrs), (scalaFile, chkFilesBySolver)) =>
        // Error per check file, VC infos per solver
        val (errs0, vcInfos0) = chkFilesBySolver.partitionMap { (solver, chkFile) =>
          parse(scalaFile, chkFile, getLines(chkFile))
            .map(solver -> _)
            .left.map(chkFile -> _)
        }
        val errs = errs0.toMap
        val vcInfos = vcInfos0.toMap
        (merge(accVCInfos, vcInfos), accErrs ++ errs)
    }

    LoadingResult(notFoundErrs, parsingErrors, expectedVCInfos)
  }

  def parse(scalaFile: File, checkFile: File, lines: Seq[String]): Either[Seq[ParsingError], ExpectedVCInfos] = {
    def parse(lineNr: Int, l: String): Either[ParsingError, VCInfo] = {
      val elems = l.split(";")
      if (elems.size != 4) {
        Left(ParsingError.InvalidEntry(checkFile, lineNr, l))
      } else {
        val Array(posStr, fn, vcKindStr, vcStatusStr) = elems
        for {
          pos <- parsePosition(lineNr, posStr)
          vcKind <- parseVCKind(lineNr, vcKindStr)
          vcStatus <- parseVCStatus(lineNr, vcStatusStr)
        } yield VCInfo(pos, fn, vcKind, vcStatus)
      }
    }

    // TODO: At the time of writing, we only print "line:column" even if we have a range.
    //  So we only parse for this case since the format for printing a range is not defined.
    //  We return a simpler Position class as a result
    def parsePosition(lineNr: Int, pos0: String): Either[ParsingError, Option[SimplePosition]] = {
      val pos = pos0.trim
      if (pos.isEmpty) Right(None)
      else {
        val elems = pos.split(":")
        if (elems.size != 2) {
          Left(ParsingError.InvalidPosition(checkFile, lineNr, pos))
        } else {
          val Array(lineStr, columnStr) = elems
          (lineStr.toIntOption, columnStr.toIntOption) match {
            // We use the position of the Scala file, that's what is mattering for checking VCs
            case (Some(line), Some(column)) => Right(Some(SimplePosition(line, column, scalaFile)))
            case _ => Left(ParsingError.InvalidPosition(checkFile, lineNr, pos))
          }
        }
      }
    }

    def parseVCKind(lineNr: Int, vc0: String): Either[ParsingError, VCKind | ClassInvariant] = {
      val bodyAssertion = "body assertion:"
      val err = "error:"
      val clsInv = "class invariant:"

      val vc = vc0.trim
      vc match {
        case "type-checking" => Right(VCKind.CheckType)
        case "precondition" => Right(VCKind.Precondition)
        case "postcondition" => Right(VCKind.Postcondition)
        case "body assertion" => Right(VCKind.Assert)
        case "match exhaustiveness" => Right(VCKind.ExhaustiveMatch)
        case "array index within bounds" => Right(VCKind.ArrayUsage)
        case "map index in keys" => Right(VCKind.MapUsage)
        case "integer overflow" => Right(VCKind.Overflow)
        case "strict arithmetic on shift" => Right(VCKind.Shift)
        case "division by zero" => Right(VCKind.DivisionByZero)
        case "modulo by zero" => Right(VCKind.ModuloByZero)
        case "measure decreases" => Right(VCKind.MeasureDecreases)
        case "non-negative measure" => Right(VCKind.MeasurePositive)
        case "measure missing" => Right(VCKind.MeasureMissing)
        case "strictly positive index for ADT selection" => Right(VCKind.UnfoldType)
        case "remainder by zero" => Right(VCKind.RemainderByZero)
        case "cast correctness" => Right(VCKind.CastError)
        case "postcondition tactic" => Right(VCKind.PostTactic)
        case "choose satisfiability" => Right(VCKind.Choose)
        case "law" => Right(VCKind.Law)
        case "invariant satisfiability" => Right(VCKind.InvariantSat)
        case "refinements checks for subtyping" => Right(VCKind.RefinementSubtype)
        case "recursive types indices checks for subtyping" => Right(VCKind.RecursiveSubtype)
        case "coq function" => Right(VCKind.CoqMethod)
        case "precondition satisfiability" => Right(VCKind.SATPrecondCheck)
        case _ =>
          if (vc.startsWith(bodyAssertion)) Right(VCKind.AssertErr(vc.drop(bodyAssertion.length).trim))
          else if (vc.startsWith(err)) Right(VCKind.Error(vc.drop(err.length).trim))
          else if (vc.startsWith(clsInv)) Right(ClassInvariant(vc.drop(clsInv.length).trim))
          else Left(ParsingError.UnknownVCKind(checkFile, lineNr, vc))
      }
    }

    def parseVCStatus(lineNr: Int, status0: String): Either[ParsingError, VCStatus[Nothing] | InvalidVC.type] = {
      val status = status0.trim
      status match {
        case "invalid" => Right(InvalidVC)
        // Unit tests have cache disabled, but if we happen to have a
        // "valid from cache" in the check file, we coerce it into Valid
        case "valid" | "valid from cache" => Right(VCStatus.Valid)
        case "admitted" => Right(VCStatus.Admitted)
        case "trivial" => Right(VCStatus.Trivial)
        case "unknown" | "inconclusive" => Right(VCStatus.Unknown)
        case "timeout" => Right(VCStatus.Timeout)
        case "cancelled" => Right(VCStatus.Cancelled) // Should not be there, in principle
        case "crashed" => Right(VCStatus.Crashed) // Ditto
        case "unsupported" => Right(VCStatus.Unsupported) // Ditto
        case "external bug" => Right(VCStatus.ExternalBug) // Ditto
        case _ => Left(ParsingError.UnknownVCStatus(checkFile, lineNr, status))
      }
    }

    val (errs, oks) = lines.zipWithIndex
      .filterNot { case (l, _) => l.isBlank || l.stripLeading().startsWith("#") }
      .partitionMap { case (l, ix) => parse(ix + 1, l) }
    // Note that ExpectedVCInfos works on .scala files, not .check files!
    if (errs.isEmpty) Right(ExpectedVCInfos(Map(scalaFile -> oks)))
    else Left(errs)
  }

  enum CheckVCFailure {
    // All VCs were correct but there are more missing
    // Note: remaining is non-empty
    case NotCovered(remaining: Map[File, Seq[VCInfo]])
    // Note: remaining may be empty
    case IncorrectVCs(incorrect: Seq[CheckFailure], remaining: Map[File, Seq[VCInfo]])

    def prettyLines(indent: Int, prefixFile: Option[File] = None): Seq[String] = {
      require(indent >= 0)
      this match {
        case NotCovered(remaining) => CheckVCFailure.prettyRemaining(remaining, indent, prefixFile)
        case IncorrectVCs(incorrect, remaining) =>
          val indentStr = " " * indent
          incorrect.map(f => s"$indentStr${f.pretty}") ++ CheckVCFailure.prettyRemaining(remaining, indent, prefixFile)
      }
    }
  }
  object CheckVCFailure {
    private def prettyRemaining(remaining: Map[File, Seq[VCInfo]], indent: Int, prefixFile: Option[File] = None): Seq[String] = {
      require(indent >= 0)
      val identStr = " " * indent
      def pp(file: File, remaining: Seq[VCInfo]): Seq[String] = {
        val unprefixed = prefixFile.map(_.toPath.relativize(file.toPath).toFile).getOrElse(file)
        Seq(s"${identStr * 2}For file ${unprefixed.getPath}:") ++
          remaining.map(vc => s"${identStr * 3}${vc.pretty}")
      }
      if (remaining.nonEmpty) {
        Seq(s"${identStr}The following expected VCs are not covered by the results:") ++
          remaining.flatMap(pp).toSeq
      } else Seq.empty
    }
  }

  // NOTE: A VC may occur multiple times (with different results), so we use a Seq of pairs and not a Map
  def checkVCResults[T <: ast.Trees, M](expected: ExpectedVCInfos, results: Seq[(VC[T], VCStatus[M])]): Either[CheckVCFailure, Unit] = {
    val (remainingInfos, errs) = results.foldLeft((expected, Seq.empty[CheckFailure])) {
      case ((expectedInfos, accErrs), (vc, vcStatus)) =>
        expectedInfos.check(vc, vcStatus) match {
          case Right(newExpectedInfos) => (newExpectedInfos, accErrs)
          case Left(err) => (expectedInfos, accErrs :+ err)
        }
    }

    // Note that remainingInfos keeps the Seq[VCInfo] even if it's empty, see its check method for more info
    val remaining = remainingInfos.infosByScalaFile.filter(_._2.nonEmpty)
    if (errs.nonEmpty) {
      Left(CheckVCFailure.IncorrectVCs(errs, remaining))
    } else {
      if (remaining.isEmpty) Right(())
      else Left(CheckVCFailure.NotCovered(remaining))
    }
  }

  /** The lines of a check file of `scalaFile` that expects the VC `results`, sorted by position, or the VCs that
    * such a file cannot represent: the ones outside of `scalaFile` (which [[checkVCResults]] does not expect in any
    * check file) and the ones that [[parse]] would not read back from their line. */
  def checkFileLines[T <: ast.Trees, M](scalaFile: File, results: Seq[(VC[T], VCStatus[M])]): Either[Seq[String], Seq[String]] = {
    val (inFile, outside) = results.partition(_._1.getPos.file == scalaFile)
    val infos = inFile.map((vc, status) => VCInfo.of(vc, status))
    val unparsable = infos.filter(info => parse(scalaFile, scalaFile, Seq(info.checkLine)) != Right(ExpectedVCInfos(Map(scalaFile -> Seq(info)))))
    val unrepresentable = outside.map((vc, status) => VCInfo.of(vc, status)) ++ unparsable
    if (unrepresentable.nonEmpty) Left(unrepresentable.map(_.pretty))
    else Right(infos.sortBy(info => (info.pos.get.line, info.pos.get.column, info.checkLine)).map(_.checkLine))
  }

  def toTestPos(pos: Position): Option[SimplePosition] =
    if (!pos.isDefined) None
    else Some(SimplePosition(pos.line, pos.col, pos.file))

  def toTestVCKind(vcKind: VCKind): VCKind | ClassInvariant =
    vcKind match {
      case VCKind.AdtInvariant(inv) => ClassInvariant(inv.name)
      case VCKind.Info(kind, _) => toTestVCKind(kind) // e.g. precond. call f(x).
      case _ => vcKind
    }

  def toTestVCStatus[M](vcStatus: VCStatus[M]): VCStatus[Nothing] | InvalidVC.type =
    vcStatus match {
      case VCStatus.Invalid(_) => InvalidVC
      // "Trivial" VCs depends on the simplifier which we do not want
      // "Valid from cache" depends on the order of VCs solving, and is usually disabled in integration tests
      case VCStatus.ValidFromCache | VCStatus.Trivial => VCStatus.Valid
      case other => other.asInstanceOf[VCStatus[Nothing]] // All other cases are case objects, so hammering with an asInstanceOf is fine
    }

  private def throwFailure(msg: String): Nothing = throw IllegalArgumentException(msg)

  extension (s: Solver) {
    private def fileExt: String = s match {
      case Solver.Z3 => "z3"
      case Solver.cvc5 => "cvc5"
      case Solver.Princess => "princess"
    }
  }
}
