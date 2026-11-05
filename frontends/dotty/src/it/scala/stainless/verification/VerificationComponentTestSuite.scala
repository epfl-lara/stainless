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

  def testNegAllWithCheckFiles(dir: String,
                               lp: LoadedProgramsWithCheckFiles,
                               identifierFilter: Identifier => Boolean = _ => true,
                               checkFileFilter: (File, Solver) => Boolean = (_, _) => true): Unit = {
    // Note that we don't do any work here  - appart from failing if something went wrong
    // All the work was done beforehand in a lazy val to ensure no duplication of work
    val benchFolder = File(getClass.getResource(s"/$dir").getPath)
    val expectedVCInfos = validateLoadedCheckFiles(benchFolder, lp.resource)

    testAll(dir, lp.lp, identifierFilter) { ctx ?=> (analysis, reporter, _, scalaFile) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
      validateWithCheckFiles(benchFolder, checkFileFilter, expectedVCInfos, scalaFile, analysis)
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
                                   checkFileFilter: (File, Solver) => Boolean,
                                   expectedVCInfos: Map[Solver, CheckFilesUtils.ExpectedVCInfos],
                                   scalaFile: File,
                                   analysis: component.Analysis)(using ctx: inox.Context): Unit = {
    val solversStr = ctx.options.findOptionOrDefault(inox.optSelectedSolvers)
    assert(solversStr.size == 1)
    val solver = Solver.fromInoxName(solversStr.head).getOrElse(fail(s"Unknown solver: ${solversStr.head}"))
    if (!checkFileFilter(scalaFile, solver)) {
      return
    }

    val results = analysis.vrs.map { case (vc, vcRes) => (vc, vcRes.status) }
    (CheckFilesUtils.checkFileOf(scalaFile, solver), expectedVCInfos.get(solver).flatMap(_.projected(scalaFile))) match {
      case (Some(checkFile), _) if ExpectedFiles.updateMode =>
        updateCheckFile(scalaFile, checkFile, results)

      case (_, Some(expectedVCInfos)) =>
        val checkingResult = CheckFilesUtils.checkVCResults(expectedVCInfos, results)
        checkingResult match {
          case Left(err) =>
            val prettyErrs = err.prettyLines(indent = 2, prefixFile = Some(benchFolder)).mkString("\n")
            fail(s"The results do not match their check files:\n$prettyErrs\n${ExpectedFiles.updateHint}")
          case Right(()) => ()
        }

      case _ =>
        // No check file for this test. If allowMissingCheckFile is set to false,
        // the earlier validation would have caught a missing .check file.
        // However, it cannot catch the case where there are no base .check file
        // but solver-specific files if e.g. we have checkfile.z3
        // and checkfile.princess but with cvc5 missing.
        val fileRel = benchFolder.toPath.relativize(scalaFile.toPath).toFile.getPath
        if (allowMissingCheckFile) {
          // We shouldn't be doing this here, that said, we shouldn't allow for missing check files either
          // Reported through the test instead of printed, so that it stays with the output of its suite
          // when the suites run in parallel.
          info(s"The Scala file $fileRel did not have a check file for solver $solver (note: allowMissingCheckFile is set to true)")
          info("To add one, create an empty check file and run with STAINLESS_UPDATE_EXPECTED=1 to fill it")
        } else {
          fail(s"The Scala file $fileRel did not have a check file for solver $solver")
        }
    }
  }

  /** In update mode, rewrites the check file `checkFile` of `scalaFile` with the VC `results` if they do not match.
    *
    * A check file without solver extension is shared by all the solvers that do not have their own: the first test
    * of the run that checks it updates it, and the next ones fail if they obtain different results. A solver-specific
    * check file `X.check.<solver>` can then be added for the solvers that disagree. Missing check files are not
    * created: to add one, create an empty file and run in update mode.
    */
  private def updateCheckFile[T <: ast.Trees, M](scalaFile: File, checkFile: File, results: Seq[(VC[T], VCStatus[M])]): Unit = {
    val lines = CheckFilesUtils.checkFileLines(scalaFile, results) match {
      case Right(lines) => lines
      case Left(unrepresentable) =>
        fail(s"The following VCs cannot be written to the check file $checkFile:\n" + unrepresentable.map("  " + _).mkString("\n"))
    }
    ExpectedFiles.updateLines(checkFile, lines) { expectedLines =>
      CheckFilesUtils.parse(scalaFile, checkFile, expectedLines) match {
        case Right(expected) => CheckFilesUtils.checkVCResults(expected, results).isRight
        case Left(_) => false
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
    // In update mode, the check files with parsing errors are rewritten by the tests
    if (loadRes.errs.nonEmpty && !ExpectedFiles.updateMode) {
      val header = "The following check files have parsing errors:"
      val errsStr = loadRes.errs.flatMap(prettyLines).toSeq
      val combined = header + "\n" + errsStr.mkString("\n")
      fail(combined)
    }

    loadRes.expectedVCInfosBySolver
  }

  final def checkFileMapIgnore2Filter(ignore: Map[Solver, Set[String]]): (File, Solver) => Boolean =
    (file, solver) => {
      // To be consistent with the verification `filter` method which does not expect to have a .scala file
      val fileNoExt = file.getPath.replace(".scala", "")
      ignore.get(solver).forall(ignoreFiles => !ignoreFiles.exists(fileNoExt.endsWith))
    }
}
object VerificationComponentTestSuite {
  type LoadedProgramsWithCheckFiles = LoadedProgramsWithResource[CheckFilesUtils.LoadingResult]

  def loadProgramsWithCheckFiles(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true,
                                 options: Seq[inox.OptionValue[?]] = ComponentTestSuite.defaultExtractionOptions): LoadedProgramsWithCheckFiles =
    ComponentTestSuite.loadProgramsWithResource(dir, recursive, keepOnly, options) { lp =>
      // Note the units also contains the Stainless library in form of tasty files which we are not interested in
      CheckFilesUtils.load(lp.unitsWithFile.map(_._2).filter(_.getPath.endsWith(".scala")))
    }
}