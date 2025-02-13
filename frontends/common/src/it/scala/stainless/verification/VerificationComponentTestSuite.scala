package stainless
package verification

import stainless.ComponentTestSuite.{LoadedPrograms, LoadedProgramsWithResource}
import stainless.Utils.{Solver, prettyInvalidVCs}
import stainless.verification.VerificationComponentTestSuite.LoadedProgramsWithCheckFiles

import java.io.File

trait VerificationComponentTestSuite extends ComponentTestSuite { self =>

  // When set to true, Scala file with a missing corresponding check file will not be treated as an error
  val allowMissingCheckFile: Boolean = true

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      optFailInvalid(false),
      optFailEarly(false)
    ) ++ seq
  }

  def testPosAll(dir: String, lp: LoadedPrograms, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, lp, identifierFilter) { (analysis, reporter, _, _) =>
      assert(analysis.toReport.stats.validFromCache == 0, "no cache should be used for these tests")
      val errLines = prettyInvalidVCs(analysis)
      if (errLines.nonEmpty) {
        fail(errLines.mkString("\n"))
      }
      reporter.terminateIfError()
    }

  def testNegAll(dir: String, lp: LoadedPrograms, identifierFilter: Identifier => Boolean = _ => true): Unit = {
    testAll(dir, lp, identifierFilter) { (analysis, reporter, _, file) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
    }
  }

  def testNegAllWithCheckFiles(dir: String, lp: LoadedProgramsWithCheckFiles, identifierFilter: Identifier => Boolean = _ => true): Unit = {
    // Note that we don't do any work here  - appart from failing if something went wrong
    // All the work was done beforehand in a lazy val to ensure no duplication of work
    val benchFolder = File(getClass.getResource(s"/$dir").getPath)
    val expectedVCInfos = validateLoadedCheckFiles(benchFolder, lp.resource)

    testAll(dir, lp.lp, identifierFilter) { ctx ?=> (analysis, reporter, _, scalaFile) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
      validateWithCheckFiles(benchFolder, expectedVCInfos, scalaFile, analysis)
    }
  }

  def testUncheckedAll(dir: String, lp: LoadedPrograms, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, lp, identifierFilter) { (analysis, reporter, _, _) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0 || report.totalUnknown > 0,
        "There should be at least one invalid/unknown verification condition.")
    }

  //////////////////////////////////////////////////

  final def validateWithCheckFiles(benchFolder: File,
                                   expectedVCInfos: Map[Solver, CheckFilesUtils.ExpectedVCInfos],
                                   scalaFile: File,
                                   analysis: component.Analysis)(using ctx: inox.Context): Unit = {
    val solversStr = ctx.options.findOptionOrDefault(inox.optSelectedSolvers)
    assert(solversStr.size == 1)
    val solver = Solver.fromInoxName(solversStr.head).getOrElse(fail(s"Unknown solver: ${solversStr.head}"))

    expectedVCInfos.get(solver).flatMap(_.projected(scalaFile)) match {
      case Some(expectedVCInfos) =>
        val checkingResult = CheckFilesUtils.checkVCResults(expectedVCInfos, analysis.vrs.map { case (vc, vcRes) => (vc, vcRes.status) })
        checkingResult match {
          case Left(err) =>
            val prettyErrs = err.prettyLines(indent = 2, prefixFile = Some(benchFolder)).mkString("\n")
            fail(s"The results do not match their check files:\n$prettyErrs")
          case Right(()) => ()
        }

      case None =>
        // No check file for this test. If allowMissingCheckFile is set to false,
        // the earlier validation would have caught a missing .check file.
        // However, it cannot catch the case where there are no base .check file
        // but solver-specific files if e.g. we have checkfile.z3
        // and checkfile.princess but with cvc5 missing.
        val fileRel = benchFolder.toPath.relativize(scalaFile.toPath).toFile.getPath
        if (allowMissingCheckFile) {
          // We shouldn't be doing this here, that said, we shouldn't allow for missing check files either
          warnPrintln(Seq(s"The Scala file $fileRel did not have a check file for solver $solver (note: allowMissingCheckFile is set to true)"))
        } else {
          fail(s"The Scala file $fileRel did not have a check file for solver $solver")
        }
    }
  }

  final def validateLoadedCheckFiles(benchFolder: File,
                                     loadRes: CheckFilesUtils.LoadingResult): Map[Solver, CheckFilesUtils.ExpectedVCInfos] = {
    import CheckFilesUtils.CheckFileError.*
    val iden = 2
    val idenStr = " " * iden

    def prettyErr(e: ParsingError): String = e match {
      case ParsingError.InvalidEntry(_, lineNr, line) =>
        s"${idenStr * 2}Invalid line at $lineNr: $line. Expected is position;function name;VC kind;VC Status"
      case ParsingError.InvalidPosition(_, lineNr, pos) =>
        s"${idenStr * 2}Invalid position at line $lineNr: $pos. Expected is line:column"
      case ParsingError.UnknownVCKind(_, lineNr, vcKind) =>
        s"${idenStr * 2}Unknown VC kind at line $lineNr: $vcKind"
      case ParsingError.UnknownVCStatus(_, lineNr, vcStatus) =>
        s"${idenStr * 2}Unknown VC status at line $lineNr: $vcStatus"
    }

    def prettyLines(f: File, errs: Seq[ParsingError]): Seq[String] = {
      val fStr = benchFolder.toPath.relativize(f.toPath).toFile.getPath
      val header = s"${idenStr}The check file $fStr has the following errors:"
      header +: errs.map(prettyErr)
    }

    if (loadRes.notFound.nonEmpty) {
      val files = loadRes.notFound.map(f => benchFolder.toPath.relativize(f.scalaFile.toPath).toFile.getPath).sorted
        .map(f => s"$idenStr$f")
      if (!allowMissingCheckFile) {
        val header = "The following Scala files do not have a corresponding check file:"
        fail(header + "\n" + files.mkString("\n"))
      }
    }
    if (loadRes.errs.nonEmpty) {
      val header = "The following check files have parsing errors:"
      val errsStr = loadRes.errs.flatMap(prettyLines).toSeq
      val combined = header + "\n" + errsStr.mkString("\n")
      fail(combined)
    }

    loadRes.expectedVCInfosBySolver
  }

  final def warnPrintln(lines: Seq[String]): Unit = {
    lines.foreach { l =>
      val warn = s"${Console.BOLD}${Console.YELLOW}[warning]${Console.RESET}"
      val msg = s"${Console.YELLOW}$l${Console.RESET}"
      println(s"$warn $msg")
    }
  }
}
object VerificationComponentTestSuite {
  type LoadedProgramsWithCheckFiles = LoadedProgramsWithResource[CheckFilesUtils.LoadingResult]

  def loadProgramsWithCheckFiles(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true): LoadedProgramsWithCheckFiles =
    ComponentTestSuite.loadProgramsWithResource(dir, recursive, keepOnly) { lp =>
      // Note the units also contains the Stainless library in form of tasty files which we are not interested in
      CheckFilesUtils.load(lp.unitsWithFile.map(_._2).filter(_.getPath.endsWith(".scala")))
    }
}