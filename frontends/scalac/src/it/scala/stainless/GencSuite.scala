/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils._

import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.{Paths, Files}
import java.io.File
import java.io.PrintWriter

import Utils._

class GenCSuite extends AnyFunSuite with inox.ResourceUtils with InputUtils {
  val files = resourceFiles("genc", _.endsWith(".scala"), false).map(_.getPath).toSeq
  val ctx = TestContext.empty

  // FIXME: fix verification for those files
  // https://github.com/epfl-lara/stainless/issues/926
  val ignoreVerification: Set[String] = Set(
    "LZWa.scala",
    "LZWb.scala",
    "ImageProcessing.scala",
    "Return.scala",
    "ArgumentsEffects.scala", // https://github.com/epfl-lara/stainless/issues/1068
  )

  for (file <- files if !ignoreVerification(new File(file).getName)) {
    test(s"stainless --batched $file") {
      val (localCtx, optReport) = runMainWithArgs(Array(file) :+ "--batched")
      assert(localCtx.reporter.errorCount == 0, "No errors")
      assert(optReport.nonEmpty, "Valid report returned by Stainless")
      assert(optReport.get.isSuccess, "Only valid VCs")
    }
  }

  for (file <- files) {
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
    val fileArgumentsEffects = files.find(_.toString.contains("ArgumentsEffects.scala")).get
    val outFile = fileArgumentsEffects.replace(".scala", ".out")
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    val output = std.mkString
    assert(output == "113", s"Output '$output' should be '113'")
  }

  test("Checking that Global outputs 5710120") {
    val fileGlobal = files.find(_.toString.contains("Global.scala")).get
    val outFile = fileGlobal.replace(".scala", ".out")
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    val output = std.mkString
    assert(output == "5710120", s"Output '$output' should be '5710120'")
  }

  test("Checking that GlobalUninitialized outputs 8410120") {
    val fileGlobalUninitialized = files.find(_.toString.contains("GlobalUninitialized.scala")).get
    val outFile = fileGlobalUninitialized.replace(".scala", ".out")
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    val output = std.mkString
    assert(output == "8410120", s"Output '$output' should be '8410120'")
  }

  test("Checking that LZWa can encode and decode") {
    val fileLZWa = files.find(_.toString.contains("LZWa.scala")).get
    val outFile = fileLZWa.replace(".scala", ".out")
    val randomString = scala.util.Random.alphanumeric.take(1000).mkString
    new PrintWriter("input.txt") { try write(randomString) finally close() }
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    val output = std.mkString
    assert(output == "success", s"Output '$output' should be 'success'")
    val decoded = scala.io.Source.fromFile("decoded.txt").mkString
    assert(decoded == randomString, s"Decoded ($decoded) should be equal to $randomString")
  }

  test("Checking that LZWb can encode and decode") {
    val fileLZWb = files.find(_.toString.contains("LZWb.scala")).get
    val outFile = fileLZWb.replace(".scala", ".out")
    val randomString = scala.util.Random.alphanumeric.take(1000).mkString
    new PrintWriter("input.txt") { try write(randomString) finally close() }
    ctx.reporter.info(s"Running: $outFile")
    val (std, _) = runCommand(outFile)
    val output = std.mkString
    assert(output == "success", s"Output '$output' should be 'success'")
    val decoded = scala.io.Source.fromFile("decoded.txt").mkString
    assert(decoded == randomString, s"Decoded ($decoded) should be equal to $randomString")
  }

}
