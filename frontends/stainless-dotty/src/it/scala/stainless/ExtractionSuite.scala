/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import org.scalatest._

class ExtractionSuite extends FunSuite with inox.ResourceUtils {

  def testAll(dir: String): Unit = {
    val reporter = new inox.TestSilentReporter
    val ctx = inox.Context(reporter, new inox.utils.InterruptManager(reporter))

    val fs = resourceFiles(dir, _.endsWith(".scala")).toList

    val tryProgram = scala.util.Try(Main.extractFromSource(ctx, Main.libraryFiles ++ fs.map(_.getPath))._2)
    assert(tryProgram.isSuccess, "Program extraction failed")
    val program = tryProgram.get

    test(s"Initial program type checks in $dir") {
      for (fd <- program.symbols.functions.values.toSeq) {
        import program.symbols._
        assert(isSubtypeOf(fd.fullBody.getType, fd.returnType))
      }
    }

    test(s"Transformed program type checks in $dir") {
      val exProgram = program.transform(extraction.extractor)
      assert(reporter.lastErrors.isEmpty)
      for (fd <- exProgram.symbols.functions.values.toSeq) {
        import exProgram.symbols._
        assert(isSubtypeOf(fd.fullBody.getType, fd.returnType))
      }
    }
  }

  //testAll("verification/valid")
  //testAll("verification/invalid")
  //testAll("verification/unchecked")
  //testAll("imperative/valid")
  testAll("imperative/invalid")
  //testAll("termination/valid")
  //testAll("termination/looping")
}
