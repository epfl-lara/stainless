/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils._

import org.scalatest._

import java.nio.file.{Paths, Files}
import java.io.File

import Utils._

class GenCSuite extends FunSuite with inox.ResourceUtils with InputUtils {
  val files = resourceFiles("genc", _.endsWith(".scala"), false).map(_.getPath).toSeq

  val ctx = TestContext.debug()

  // FIXME: fix verification for those files
  // https://github.com/epfl-lara/stainless/issues/926
  val ignoreVerification: Set[String] = Set(
    "LZWa.scala",
    "LZWb.scala",
    "ImageProcessing.scala",
    "Return.scala",
  )

  for (file <- files if !ignoreVerification(new File(file).getName)) {
    test(s"stainless --batched $file") {
      runMainWithArgs(Array(file) :+ "--batched")
    }
  }

  for (file <- files) {
    val cFile = file.replace(".scala", ".c")
    test(s"stainless --genc --genc-ouptut=$cFile $file") {
      runMainWithArgs(Array(file) :+ "--genc" :+ s"--genc-output=$cFile")
      assert(Files.exists(Paths.get(cFile)))
      val gccCompile = s"gcc $cFile"
      ctx.reporter.info(s"Running: $gccCompile")
      val (std, exitCode) = runCommand(gccCompile)
      assert(exitCode == 0, "gcc failed with output:\n" + std.mkString("\n"))
    }
  }

}
