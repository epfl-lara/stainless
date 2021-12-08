/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.extraction.xlang.{ trees => xt }
import stainless.extraction.utils.DebugSymbols

import org.scalatest.funspec.AnyFunSpec
import scala.util.{Success, Failure, Try}

/** Subclass are only meant to call [[testExtractAll]] and [[testRejectAll]] on
 *  the relevant directories. */
abstract class ExtractionSuite extends AnyFunSpec with inox.ResourceUtils with InputUtils {

  def options: Seq[inox.OptionValue[_]] = Seq()

  final def createContext(options: inox.Options) = stainless.TestContext(options)

  private def testSetUp(dir: String): (inox.Context, List[String]) = {
    val ctx = createContext(inox.Options(options))
    val fs = resourceFiles(dir, _.endsWith(".scala")).toList map { _.getPath }
    (ctx, fs)
  }

  def testExtractAll(dir: String, excludes: String*): Unit = {
    val (ctx, allFiles) = testSetUp(dir)
    val files = allFiles.filter(f => !excludes.exists(f.endsWith))
    import ctx.{reporter, given}

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = ctx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    describe(s"Program extraction in $dir") {
      val tryProgram = scala.util.Try(loadFiles(files)._2)

      it("should be successful") { assert(tryProgram.isSuccess) }

      if (tryProgram.isSuccess) {
        val program = tryProgram.get
        val programSymbols: program.trees.Symbols =
          userFiltering.debug(frontend.UserFiltering().transform)(program.symbols)

        it("should typecheck") {
          programSymbols.ensureWellFormed
          for (fd <- programSymbols.functions.values.toSeq) {
            import programSymbols.{given, _}
            assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
          }
        }

        val tryExSymbols: Try[extraction.trees.Symbols] = Try(extraction.pipeline extract programSymbols)
        describe("and transformation") {
          it("should be successful") { tryExSymbols.get }

          if (tryExSymbols.isSuccess) {
            val exSymbols = tryExSymbols.get
            it("should produce no errors") { assert(reporter.errorCount == 0) }

            it("should typecheck") {
              exSymbols.ensureWellFormed
              for (fd <- exSymbols.functions.values.toSeq) {
                import exSymbols.{given, _}
                assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
              }
            }

            it("should typecheck without matches") {
              for (fd <- exSymbols.functions.values.toSeq) {
                import exSymbols.{given, _}
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

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = ctx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    describe(s"Programs extraction in $dir") {
      val tryPrograms = files map { f =>
        f -> Try {
          given testCtx: inox.Context = TestContext.empty
          val program = loadFiles(List(f))._2
          val programSymbols = userFiltering.debug(frontend.UserFiltering().transform)(program.symbols)
          extraction.pipeline extract programSymbols
          testCtx.reporter.errorCount
        }
      }

      it("should fail") {
        tryPrograms foreach { case (f, tp) => tp match {
          case Failure(e) => assert(true)
          case Success(n) => assert(n > 0, s"$f was successfully extracted")
        }}
      }
    }
  }
}

