/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils._

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers

import java.nio.file.{Paths, Files}
import java.io.File
import java.io.PrintWriter

import Utils._

class TailRecGenCSuite extends AnyFunSuite with inox.ResourceUtils with InputUtils with Matchers {
  val validFiles = resourceFiles("genc/valid", _.endsWith(".scala"), false).map(_.getPath)
  val tailrecFiles = validFiles.filter(_.toLowerCase.contains("tailrec".toLowerCase)).map { path =>
    val checkFile = path.replace(".scala", ".check")
    path -> checkFile
  }
  val tailrecScalaFiles = tailrecFiles.map(_._1)
  val ctx = TestContext.empty

  // for (file <- tailrecFiles) {
  //   val extraOpts = Seq("--batched", "--solvers=smt-z3", "--strict-arithmetic=false", "--timeout=10")
  //   test(s"stainless ${extraOpts.mkString(" ")} $file") {
  //     val (localCtx, optReport) = runMainWithArgs(Array(file) ++ extraOpts)
  //     assert(localCtx.reporter.errorCount == 0, "No errors")
  //     assert(optReport.nonEmpty, "Valid report returned by Stainless")
  //     assert(optReport.get.isSuccess, "Only valid VCs")
  //   }
  // }

  for (file <- tailrecScalaFiles) {
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

  for (case (file, _) <- tailrecFiles) {
    test(s"Checking that ${file.split("/").last} has tail recursive function rewritten as loop") {
      val cFile = file.replace(".scala", ".c")
      val cCode = Files.readAllLines(Paths.get(cFile)).toArray.mkString
      assert(cCode.contains("goto"), "Should contain a goto statement")
    }
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
