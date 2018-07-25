package stainless

import org.scalatest._

class ScalacGhostChecks extends ExtractionSuite {

  def testFilePos(fileName: String): Unit = {
    val ctx = stainless.TestContext.empty
    import ctx.reporter

    val tryProgram = scala.util.Try(loadFiles(ctx, Seq(fileName))._2)
    it(s"$fileName should be successful") {
      assert(tryProgram.isSuccess)
    }
  }

  def testFileNeg(fileName: String, failures: Int): Unit = {
    val ctx = stainless.TestContext.empty
    import ctx.reporter


    it(s"$fileName should fail") {
      val tryProgram = scala.util.Try(loadFiles(ctx, Seq(fileName))._2)
      extraction.extract(tryProgram.get, ctx)
      assert(ctx.reporter.errorCount == failures, "wrong failure number")
    }
  }

  val baseDir = "frontends/benchmarks/extraction"

  describe(s"Ghost checks should succeed:") {
    testFilePos(s"$baseDir/valid/ghost-methods.scala")
  }

  describe(s"Ghost checks should fail:") {
    testFileNeg(s"$baseDir/invalid/ghost-dafny.scala", 9)
    testFileNeg(s"$baseDir/invalid/ghost-patmat.scala", 2)
  }

}
