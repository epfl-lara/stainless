/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import scala.util.{Success, Failure, Try}

import org.scalatest._

/** Subclass are only meant to call [[testExtractAll]] and [[testRejectAll]] on
 *  the relevant directories. */
abstract class ExtractionSuite extends FunSpec with inox.ResourceUtils with InputUtils {

  private def testSetUp(dir: String): (inox.Context, List[String]) = {
    val ctx = stainless.TestContext.empty
    val fs = resourceFiles(dir, _.endsWith(".scala")).toList map { _.getPath }
    (ctx, fs)
  }

  def testExtractAll(dir: String, excludes: String*): Unit = {
    implicit val (ctx, allFiles) = testSetUp(dir)
    val files = allFiles.filter(f => !excludes.exists(f.endsWith))
    import ctx.reporter

    describe(s"Program extraction in $dir") {
      val tryProgram = scala.util.Try(loadFiles(files)._2)
      it("should be successful") { assert(tryProgram.isSuccess) }

      if (tryProgram.isSuccess) {
        val program = tryProgram.get

        it("should typecheck") {
          program.symbols.ensureWellFormed
          for (fd <- program.symbols.functions.values.toSeq) {
            import program.symbols._
            assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
          }
        }

        val tryExSymbols: Try[extraction.trees.Symbols] = Try(extraction.pipeline extract program.symbols)
        describe("and transformation") {
          it("should be successful") { tryExSymbols.get }

          if (tryExSymbols.isSuccess) {
            val exSymbols = tryExSymbols.get
            it("should produce no errors") { assert(reporter.errorCount == 0) }

            it("should typecheck") {
              exSymbols.ensureWellFormed
              for (fd <- exSymbols.functions.values.toSeq) {
                import exSymbols._
                assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
              }
            }

            it("should typecheck without matches") {
              for (fd <- exSymbols.functions.values.toSeq) {
                import exSymbols._
                assert(isSubtypeOf(matchToIfThenElse(fd.fullBody).getType, fd.getType))
              }
            }
          }
        }
      }
    }
  }

  // Tests that programs are rejected either through the extractor or through
  // the TreeSanitizer.
  def testRejectAll(dir: String, excludes: String*): Unit = {
    val (ctx, allfiles) = testSetUp(dir)
    val files = allfiles.filter(f => !excludes.exists(f.endsWith))
    import ctx.reporter

    describe(s"Programs extraction in $dir") {
      val tryPrograms = files map { f =>
        f -> Try {
          implicit val testCtx = TestContext.empty
          val program = loadFiles(List(f))._2
          extraction.pipeline extract program.symbols
          testCtx.reporter.errorCount
        }
      }

      it("should fail") {
        tryPrograms foreach { case (f, tp) => tp match {
          // we expect a specific kind of exception:
          case Failure(e: stainless.frontend.UnsupportedCodeException) => assert(true)
          case Failure(e: stainless.extraction.MissformedStainlessCode) => assert(true)
          case Failure(e) => assert(false, s"$f was rejected with $e:\nStack trace:\n${e.getStackTrace().map(_.toString).mkString("\n")}")
          case Success(n) => assert(n > 0, s"$f was successfully extracted")
        }}
      }
    }
  }

}


