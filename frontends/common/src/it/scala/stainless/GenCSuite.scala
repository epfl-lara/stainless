/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils._

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.nio.file.{Paths, Files}
import java.io.File
import java.io.PrintWriter

import Utils._

class GenCSuite extends AnyFunSuite with inox.ResourceUtils with InputUtils with Matchers {
  val validFiles = resourceFiles("genc/valid", _.endsWith(".scala"), false).map(_.getPath)
  val invalidFiles = resourceFiles("genc/invalid", _.endsWith(".scala"), false).map(_.getPath)
  val tailrecFiles = validFiles.filter(_.toLowerCase.contains("tailrec")).map { path =>
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
    val outFile = file.replace(".scala", ".out")
    test(s"stainless --genc --genc-output=$cFile $file") {
      runMainWithArgs(Array(file) :+ "--genc" :+ s"--genc-output=$cFile")
      assert(Files.exists(Paths.get(cFile)))
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

  for (case (file, checkFile) <- tailrecFiles) {
    test(s"Checking that ${file.split("/").last} outputs ${Files.readAllLines(Paths.get(checkFile)).toArray.mkString}") {
      val output = runCHelper(file)
      val checkValue = Files.readAllLines(Paths.get(checkFile)).toArray.mkString
      assert(output == checkValue, s"Output '$output' should be $checkValue")
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
