/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils._

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.nio.file.{Paths, Files}
import java.nio.charset.StandardCharsets
import java.io.File
import java.io.PrintWriter

import Utils._

class GenCSuite extends AnyFunSuite with inox.ResourceUtils with InputUtils with Matchers {
  val validFiles = resourceFiles("genc/valid", _.endsWith(".scala"), false).map(_.getPath)
  val invalidFiles = resourceFiles("genc/invalid", _.endsWith(".scala"), false).map(_.getPath)
  val tailrecFiles = validFiles.filter(_.toLowerCase.contains("tailrec".toLowerCase)).map { path =>
    val checkFile = path.replace(".scala", ".check")
    path -> checkFile
  }
  val tailrecScalaFiles = tailrecFiles.map(_._1)
  // Every valid benchmark with a sibling `.check` file is also run end-to-end: the output
  // of the compiled binary (lines concatenated) must match the contents of the `.check` file.
  // In update mode (see ExpectedFiles), the `.check` files that do not match are rewritten.
  val checkFiles = validFiles.flatMap { path =>
    val checkFile = path.replace(".scala", ".check")
    if (Files.exists(Paths.get(checkFile))) Some(path -> checkFile) else None
  }
  val ctx = TestContext.empty

  for (file <- invalidFiles) {
    val cFile = file.replace(".scala", ".c")
    val outFile = file.replace(".scala", ".out")
    test(s"stainless --genc --genc-output=$cFile $file should fail") {
      // The program must be rejected, either by GenC (FatalError) or earlier by Stainless (MalformedStainlessCode)
      intercept[Exception] {
        runMainWithArgs(Array(file) :+ "--genc" :+ s"--genc-output=$cFile" :+ "--skip-verification")
      } match {
        case _: inox.FatalError | _: extraction.MalformedStainlessCode => ()
        case e => fail(s"Expected a FatalError or a MalformedStainlessCode, but got $e")
      }
    }
  }

  // GenC requires the programs to verify with `--strict-arithmetic` (the default), so that the generated C
  // code does not overflow, divide by zero, or shift by too many bits (which is undefined behavior in C).
  for (file <- validFiles) {
    val extraOpts = Seq("--batched", "--solvers=smt-z3", "--timeout=10")
    test(s"stainless ${extraOpts.mkString(" ")} $file") {
      val (localCtx, optReport) = runMainWithArgs(Array(file) ++ extraOpts)
      assert(localCtx.reporter.errorCount == 0, "No errors")
      assert(optReport.nonEmpty, "Valid report returned by Stainless")
      assert(optReport.get.isSuccess, "Only valid VCs")
    }
  }

  for (file <- validFiles) {
    val cFile = file.replace(".scala", ".c")
    val hFile = file.replace(".scala", ".h")
    val outFile = file.replace(".scala", ".out")
    test(s"stainless --genc --genc-output=$cFile $file") {
      val (localCtx, _) = runMainWithArgs(Array(file) :+ "--genc" :+ s"--genc-output=$cFile" :+ "--skip-verification")
      // A successful run must not report any error, not even one that GenC recovers from
      assert(localCtx.reporter.errorsOrNil.isEmpty, "No errors")
      assert(Files.exists(Paths.get(cFile)))
      assert(Files.exists(Paths.get(hFile)))
      // Snapshot the generated C and header against golden files so that unintended
      // changes to the emitted code (not just compilation/behaviour) are caught.
      checkGolden(cFile, file.replace(".scala", ".expected.c"))
      checkGolden(hFile, file.replace(".scala", ".expected.h"))
      // Every path of a C function that returns a value must return one, see ExhaustiveMatch.scala
      val gccCompile = s"$gccWithSanitizer -Werror=return-type $cFile -o $outFile"
      ctx.reporter.info(s"Running: $gccCompile")
      val (std, exitCode) = runCommand(gccCompile)
      assert(exitCode == 0, "gcc failed with output:\n" + std.mkString("\n"))
      // The header must also be usable on its own by C clients, which the compilation of the C
      // file does not check as its definitions come after the inclusion of the header.
      val gccHeader = s"gcc -fsyntax-only -x c $hFile"
      ctx.reporter.info(s"Running: $gccHeader")
      val (stdHeader, exitCodeHeader) = runCommand(gccHeader)
      assert(exitCodeHeader == 0, "gcc failed on the header alone with output:\n" + stdHeader.mkString("\n"))
    }
  }

  for (case (file, _) <- tailrecFiles) {
    test(s"Checking that ${file.split("/").last} has tail recursive function rewritten as loop") {
      val cFile = file.replace(".scala", ".c")
      val cCode = Files.readAllLines(Paths.get(cFile)).toArray.mkString
      assert(cCode.contains("goto"), "Should contain a goto statement")
    }
  }

  for (case (file, checkFile) <- checkFiles) {
    val name = file.split("/").last
    val checkValue = Files.readAllLines(Paths.get(checkFile)).toArray.mkString
    test(s"Checking that $name outputs $checkValue") {
      val output = runCHelper(file)
      if (ExpectedFiles.updateMode) {
        ExpectedFiles.updateLines(new File(checkFile), output)(_.mkString == output.mkString)
      } else {
        assert(output.mkString == checkValue, s"Output '${output.mkString}' should be $checkValue. ${ExpectedFiles.updateHint}")
      }
    }
  }

  /** Compare the contents of `generatedFile` against the golden file `expectedResource`.
    *
    * The golden file is read from the source tree rather than from the copied test resources,
    * see [[ExpectedFiles.sourceFile]]. In update mode (see [[ExpectedFiles]]), the golden file is
    * (over)written with the generated contents if they differ. Otherwise the generated contents
    * must match the golden file exactly, and a missing golden file is a failure.
    */
  def checkGolden(generatedFile: String, expectedResource: String): Unit = {
    val generated = new String(Files.readAllBytes(Paths.get(generatedFile)), StandardCharsets.UTF_8)
    if (ExpectedFiles.updateMode) {
      ExpectedFiles.update(new File(expectedResource), generated)(_ == generated)
    } else {
      val expectedFile = ExpectedFiles.sourceFile(new File(expectedResource)).getPath
      val expectedPath = Paths.get(expectedFile)
      assert(
        Files.exists(expectedPath),
        s"Golden file $expectedFile is missing. Re-run with STAINLESS_UPDATE_EXPECTED=1 to create it."
      )
      val expected = new String(Files.readAllBytes(expectedPath), StandardCharsets.UTF_8)
      if (generated != expected) {
        // Include a unified diff (expected vs generated) in the failure message so the
        // mismatch is actionable from CI logs alone, without local reproduction.
        val (diffOut, _) = runCommand(s"diff -u $expectedFile $generatedFile")
        fail(
          s"Generated output for $generatedFile does not match golden file $expectedFile. " +
            ExpectedFiles.updateHint + "\n" +
            s"--- diff (expected vs generated) ---\n" + diffOut.mkString("\n")
        )
      }
    }
  }

  /** The lines output by the compiled program of the benchmark `file`. They are compared
    * concatenated with the contents of the `.check` files, without newlines between them.
    */
  def runCHelper(file: String): Seq[String] = {
    val outFile = file.replace(".scala", ".out")
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    undefinedBehavior(std).foreach(ub => fail(s"$outFile has undefined behavior: $ub"))
    std
  }
}
