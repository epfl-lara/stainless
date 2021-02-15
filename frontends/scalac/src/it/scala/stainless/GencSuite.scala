/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import utils._

import org.scalatest._

import java.nio.file.{Paths, Files}

import Utils._

class GenCSuite extends FunSuite with inox.ResourceUtils with InputUtils {
  val files = resourceFiles("genc", _.endsWith(".scala"), false).map(_.getPath).toSeq

  val ctx = TestContext.debug()

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
