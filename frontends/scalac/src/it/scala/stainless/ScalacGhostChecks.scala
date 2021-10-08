package stainless

import org.scalatest._

class ScalacGhostChecks extends ExtractionSuite {

  def testFilePos(fileName: String): Unit = {
    val ctx: inox.Context = stainless.TestContext.empty
    import ctx.{reporter, given}

    val tryProgram = scala.util.Try(loadFiles(Seq(fileName))._2)
    it(s"$fileName should be successful") {
      assert(tryProgram.isSuccess)
    }
  }

  def testFileNeg(fileName: String, failures: Int): Unit = {
    val ctx: inox.Context = stainless.TestContext.empty
    import ctx.{reporter, given}

    it(s"$fileName should fail") {
      val tryProgram = scala.util.Try(loadFiles(Seq(fileName))._2)
      extraction.pipeline extract tryProgram.get.symbols
      assert(ctx.reporter.errorCount == failures, "wrong failure number")
    }
  }

  val baseDir = "frontends/benchmarks/extraction"

  describe(s"Ghost checks should succeed:") {
    testFilePos(s"$baseDir/valid/GhostMethods.scala")
  }

  describe(s"Ghost checks should fail:") {
    testFileNeg(s"$baseDir/invalid/GhostDafny.scala", 9)
    testFileNeg(s"$baseDir/invalid/GhostPatmat.scala", 2)
  }

}
