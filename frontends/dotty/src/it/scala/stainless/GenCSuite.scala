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
  // When STAINLESS_GENC_UPDATE_EXPECTED is set to "1" or "true", the golden `.expected.c`
  // and `.expected.h` files are (re)generated from the current output instead of being
  // compared against. Use this to bootstrap or intentionally update the snapshots.
  val updateExpected: Boolean =
    sys.env.get("STAINLESS_GENC_UPDATE_EXPECTED").exists(v => v == "1" || v.equalsIgnoreCase("true"))

  val validFiles = resourceFiles("genc/valid", _.endsWith(".scala"), false).map(_.getPath)
  val invalidFiles = resourceFiles("genc/invalid", _.endsWith(".scala"), false).map(_.getPath)
  val tailrecFiles = validFiles.filter(_.toLowerCase.contains("tailrec".toLowerCase)).map { path =>
    val checkFile = path.replace(".scala", ".check")
    path -> checkFile
  }
  val tailrecScalaFiles = tailrecFiles.map(_._1)
  val ctx = TestContext.empty

  for (file <- invalidFiles) {
    val cFile = file.replace(".scala", ".c")
    val outFile = file.replace(".scala", ".out")
    test(s"stainless --genc --genc-output=$cFile $file should fail") {
      an [inox.FatalError] should be thrownBy runMainWithArgs(Array(file) :+ "--genc" :+ s"--genc-output=$cFile")
    }
  }

  for (file <- validFiles) {
    val extraOpts = Seq("--batched", "--solvers=smt-z3", "--strict-arithmetic=false", "--timeout=10")
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
      runMainWithArgs(Array(file) :+ "--genc" :+ s"--genc-output=$cFile")
      assert(Files.exists(Paths.get(cFile)))
      assert(Files.exists(Paths.get(hFile)))
      // Snapshot the generated C and header against golden files so that unintended
      // changes to the emitted code (not just compilation/behaviour) are caught. The
      // golden files live in the source tree (not the copied test resources) so they
      // can be committed.
      checkGolden(cFile, sourceGoldenPath(file, ".expected.c"))
      checkGolden(hFile, sourceGoldenPath(file, ".expected.h"))
      val gccCompile = s"gcc $cFile -o $outFile"
      ctx.reporter.info(s"Running: $gccCompile")
      val (std, exitCode) = runCommand(gccCompile)
      assert(exitCode == 0, "gcc failed with output:\n" + std.mkString("\n"))
    }
  }

  test("Checking that ArgumentsEffects outputs 113") {
    val output = runCHelper("ArgumentsEffects.scala")
    assert(output == "113", s"Output '$output' should be '113'")
  }

  test("Checking that Global outputs 5710120") {
    val output = runCHelper("Global.scala")
    assert(output == "5710120", s"Output '$output' should be '5710120'")
  }

  test("Checking that GlobalUninitialized outputs 8410120") {
    val output = runCHelper("GlobalUninitialized.scala")
    assert(output == "8410120", s"Output '$output' should be '8410120'")
  }

  test("Checking that Pointer2 outputs 124443") {
    val output = runCHelper("Pointer2.scala")
    assert(output == "124443", s"Output '$output' should be '124443'")
  }

  for (case (file, _) <- tailrecFiles) {
    test(s"Checking that ${file.split("/").last} has tail recursive function rewritten as loop") {
      val cFile = file.replace(".scala", ".c")
      val cCode = Files.readAllLines(Paths.get(cFile)).toArray.mkString
      assert(cCode.contains("goto"), "Should contain a goto statement")
    }
  }

  for (case (file, checkFile) <- tailrecFiles) {
    val name = file.split("/").last
    val checkValue = Files.readAllLines(Paths.get(checkFile)).toArray.mkString
    test(s"Checking that $name outputs $checkValue") {
      val output = runCHelper(file)
      assert(output == checkValue, s"Output '$output' should be $checkValue")
    }
  }

  /** Map a benchmark resource path to the corresponding golden file in the source tree.
    *
    * The genc benchmarks are copied into the test class output directory, so `resourceFiles`
    * returns paths such as `<root>/frontends/dotty/target/.../it-classes/genc/valid/X.scala`.
    * Golden files must instead live under `<root>/frontends/benchmarks/genc/valid/` so they
    * are part of the repository and can be committed.
    */
  def sourceGoldenPath(scalaResourcePath: String, ext: String): String = {
    val marker = "/it-classes/"
    val i = scalaResourcePath.indexOf(marker)
    require(i >= 0, s"Unexpected benchmark resource path (no '$marker'): $scalaResourcePath")
    val root = scalaResourcePath.substring(0, scalaResourcePath.indexOf("/frontends/"))
    val rel = scalaResourcePath.substring(i + marker.length) // e.g. genc/valid/X.scala
    s"$root/frontends/benchmarks/${rel.stripSuffix(".scala") + ext}"
  }

  /** Compare the contents of `generatedFile` against the golden `expectedFile`.
    *
    * In update mode (STAINLESS_GENC_UPDATE_EXPECTED), the golden file is (over)written
    * with the freshly generated contents. Otherwise the generated contents must match the
    * golden file exactly, and a missing golden file is a failure pointing at the update flag.
    */
  def checkGolden(generatedFile: String, expectedFile: String): Unit = {
    val generated = new String(Files.readAllBytes(Paths.get(generatedFile)), StandardCharsets.UTF_8)
    val expectedPath = Paths.get(expectedFile)
    if (updateExpected) {
      Files.write(expectedPath, generated.getBytes(StandardCharsets.UTF_8))
      ctx.reporter.info(s"Updated golden file: $expectedFile")
    } else {
      assert(
        Files.exists(expectedPath),
        s"Golden file $expectedFile is missing. Re-run with STAINLESS_GENC_UPDATE_EXPECTED=1 to create it."
      )
      val expected = new String(Files.readAllBytes(expectedPath), StandardCharsets.UTF_8)
      if (generated != expected) {
        // Include a unified diff (expected vs generated) in the failure message so the
        // mismatch is actionable from CI logs alone, without local reproduction.
        val (diffOut, _) = runCommand(s"diff -u $expectedFile $generatedFile")
        fail(
          s"Generated output for $generatedFile does not match golden file $expectedFile. " +
            s"If this change is intended, re-run with STAINLESS_GENC_UPDATE_EXPECTED=1 to update it.\n" +
            s"--- diff (expected vs generated) ---\n" + diffOut.mkString("\n")
        )
      }
    }
  }

  def runCHelper(filename: String): String = {
    val file = validFiles.find(_.contains(filename)).get
    val outFile = file.replace(".scala", ".out")
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    // Note: lines are concatenated without adding newlines between them
    std.mkString
  }
}
