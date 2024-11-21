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
  val validFiles = resourceFiles("genc/valid", n => n.endsWith(".scala") & n.contains("tailrec"), false).map(_.getPath)
  val invalidFiles = resourceFiles("genc/invalid", _.endsWith(".scala"), false).map(_.getPath)
  val ctx = TestContext.empty

  // for (file <- validFiles) {
  //   val extraOpts = Seq("--batched", "--solvers=smt-z3", "--strict-arithmetic=false", "--timeout=10")
  //   test(s"stainless ${extraOpts.mkString(" ")} $file") {
  //     val (localCtx, optReport) = runMainWithArgs(Array(file) ++ extraOpts)
  //     assert(localCtx.reporter.errorCount == 0, "No errors")
  //     assert(optReport.nonEmpty, "Valid report returned by Stainless")
  //     assert(optReport.get.isSuccess, "Only valid VCs")
  //   }
  // }

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

  // test("Test tail rec") {
  //   val output = runCHelper("tailrec_test.scala")
  //   assert(false)
  // }

  def runCHelper(filename: String): String = {
    val file = validFiles.find(_.contains(filename)).get
    val outFile = file.replace(".scala", ".out")
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    // Note: lines are concatenated without adding newlines between them
    std.mkString
  }
}
