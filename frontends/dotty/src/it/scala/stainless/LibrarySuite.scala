/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import scala.concurrent.Await
import scala.concurrent.duration.*
import extraction.{ExtractionSummary, xlang}
import org.scalatest.funsuite.AnyFunSuite
import stainless.Utils.prettyInvalidVCs
import stainless.utils.YesNoOnly

import java.io.File
import java.nio.file.{Files, Paths}

abstract class AbstractLibrarySuite(opts: Seq[inox.OptionValue[?]]) extends AnyFunSuite with InputUtils {
  import ast.SymbolIdentifier

  protected val defaultOptions = Seq(inox.optSelectedSolvers(Set("smt-z3")))

  protected val options = inox.Options(opts ++ defaultOptions)

  protected def libraryFiles(): Seq[String] = Main.libraryFiles

  /* We need a solver with better floating-point performance than z3 for the math library, but want to keep z3 for the
   * rest of the library.  Running each solver on a different subset of the library source files does not work, since
   * other library files can import the math library.  Instead, we choose what functions to verify using what solver
   * based on the full name of the function. */
  protected final def isMathLibraryFunction(tr: ast.Trees)(fd: tr.FunDef): Boolean =
    fd.id.fullName.startsWith("stainless.math.")

  protected def symbolName(id: Identifier): String = id match {
    case si: SymbolIdentifier => si.symbol.name
    case id => id.name
  }

  protected def keep(tr: ast.Trees)(fd: tr.FunDef): Boolean = fd match {
    case fd if fd.flags.exists(f => f.name == "unchecked" || f.name == "synthetic") => false
    case fd => true
  }

  private val keepOnly: Option[Set[String]] = None
  /*
  // If you wish to debug part of the library, you may indicate the files you would like to keep here
  // Note that this does not take care of the interdependencies, you have to specify them manually.
  private val keepOnly: Option[Set[String]] = Some(Set(
    "stainless/annotation/annotations.scala",
    "stainless/lang/StaticChecks.scala",
    "stainless/lang/Option.scala",
  ))
  */

  test("Stainless library extraction and verification") {
    val ctx: inox.Context = stainless.TestContext(options)
    import ctx.{reporter, given}
    import verification.VerificationComponent
    val libProgram = loadLibrary()

    val run = VerificationComponent.run(extraction.pipeline)
    val exProgram = inox.Program(run.trees)(run.extract(libProgram.symbols)._1)
    // Note: if we have an error, an exception would have been thrown
    assert(reporter.errorCount == 0, "Verification extraction had errors")

    val funs = exProgram.symbols.functions.values.filter(keep(exProgram.trees)).map(_.id).toSeq
    val analysis = Await.result(run.execute(funs, exProgram.symbols, ExtractionSummary.NoSummary), Duration.Inf)
    val report = analysis.toReport
    val invalids = analysis.vrs.filter(_._2.isInvalid)
    val inconcls = analysis.vrs.filter(_._2.isInconclusive)
    lazy val errMsg = {
      val errs = prettyInvalidVCs(analysis)
      val header = s"Library verification failed. Only ${report.totalValid} valid out of ${report.totalConditions}"
      (header +: errs).mkString("\n")
    }
    assert(report.totalConditions == report.totalValid, errMsg)
  }

  final def loadLibrary()(using inox.Context): Program { val trees: xlang.trees.type } = {
    val libFiles = keepOnly match {
      case Some(keepRelative) =>
        libraryFiles().filter(lib => keepRelative.exists(lib.endsWith))
      case None => libraryFiles()
    }
    // This may throw an exception (e.g. if there are Extraction error),
    // which we let bubble up as it should give a detailed stacktrace
    loadFiles(libFiles)._2
  }
}

class LibrarySuite extends AbstractLibrarySuite(Seq(
  termination.optInferMeasures(true),
  termination.optCheckMeasures(YesNoOnly.Yes),
  inox.optTimeout(30.seconds),
)) {
  // keep everything except math library functions
  override protected def keep(tr: ast.Trees)(fd: tr.FunDef): Boolean =
    !isMathLibraryFunction(tr)(fd) && super.keep(tr)(fd)
}

class MathLibrarySuite extends AbstractLibrarySuite(Seq(
  termination.optInferMeasures(true),
  termination.optCheckMeasures(YesNoOnly.Yes),
  inox.optSelectedSolvers(Set("smt-cvc5")),
  inox.optTimeout(30.seconds),
)) {
  // only keep math library functions
  override protected def keep(tr: ast.Trees)(fd: tr.FunDef): Boolean =
    isMathLibraryFunction(tr)(fd) && super.keep(tr)(fd)

  /* Without this extra filtering, we will extract the full Stainless library for the math library suite.
   * Extracting the full library does not affect the result of `MathLibrarySuite`,
   * but seems to add ~45 seconds to the runtime (as of 2026-01-22). */
  override protected def libraryFiles(): Seq[String] = {
    val mathPrefix = Main.libraryFiles.find(_.endsWith(s"stainless${File.separator}math${File.separator}package.scala")) match {
      case Some(path) => path.stripSuffix("package.scala")
      case None => ""
    }
    super.libraryFiles().filter(_.startsWith(mathPrefix))
  }
}