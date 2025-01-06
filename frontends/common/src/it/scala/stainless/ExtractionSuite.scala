/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.utils.{Position, NoPosition}
import stainless.extraction.xlang.trees as xt
import stainless.extraction.utils.DebugSymbols
import org.scalatest.funspec.AnyFunSpec

import scala.util.{Failure, Success, Try}

/** Subclass are only meant to call [[testExtractAll]] and [[testRejectAll]] on
  *  the relevant directories. */
abstract class ExtractionSuite extends AnyFunSpec with inox.ResourceUtils with InputUtils {

  def options: Seq[inox.OptionValue[?]] = Seq()

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

      it("should be successful") {
        tryProgram match {
          case Failure(exception) => fail(exception)
          case Success(_) => ()
        }
      }

      if (tryProgram.isSuccess) {
        val program = tryProgram.get
        val programSymbols: program.trees.Symbols =
          userFiltering.debugWithoutSummary(frontend.UserFiltering().transform)(program.symbols)._1

        it("should typecheck") {
          programSymbols.ensureWellFormed
          for (fd <- programSymbols.functions.values.toSeq) {
            import programSymbols.{given, _}
            assert(isSubtypeOf(fd.fullBody.getType, fd.getType))
          }
        }

        val tryExSymbols: Try[extraction.trees.Symbols] = Try(extraction.pipeline.extract(programSymbols)._1)
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
    val (baseCtx, allfiles) = testSetUp(dir)
    val files = allfiles.filter(f => !excludes.exists(f.endsWith)).sortBy(_.toLowerCase)

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = baseCtx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    val checkFiles = files.map { f =>
      f -> Try(scala.io.Source.fromFile(f.replace(".scala", ".check")))
        .toOption
        .getOrElse(fail(s"Could not find check file for negative test $f"))
        .getLines().map(_.stripTrailing()).toSeq
    }.toMap

    val tryPrograms = files.map { f =>
      val reporter = new NegativeTestReporter(dir)
      def extract = Try {
        given testCtx: inox.Context = baseCtx.copy(reporter = reporter)
        val program = loadFiles(List(f))._2
        val programSymbols = userFiltering.debugWithoutSummary(frontend.UserFiltering().transform)(program.symbols)._1
        val exSyms = extraction.pipeline.extract(programSymbols)._1
        if (reporter.errorCount == 0) {
          try {
            exSyms.ensureWellFormed
          } catch {
            case e: exSyms.trees.NotWellFormedException =>
              reporter.error(e.getMessage)
          }
        }
      }
      f -> inox.utils.Lazy {
        val errs = extract match {
          case Success(()) =>
            reporter.allErrors
          case Failure(e: (ExtractionError | SanitizationError)) =>
            reporter.allErrors
          case Failure(e: extraction.MalformedStainlessCode) =>
            reporter.error(e.tree.getPos, e.msg)
            reporter.allErrors
          case Failure(inox.FatalError(_)) =>
            // The fatal error has been informed to the reporter, so we should not report it again.
            reporter.allErrors
          case Failure(e) =>
            throw new Exception(s"Unexpected exception for $f: \n$e")
        }
        errs.map(_.stripTrailing()).toSeq
      }
    }

    describe(s"Programs extraction in $dir") {
      for ((f, gotErrorsLzy) <- tryPrograms) {
        val fname = java.io.File(f).getName
        it(s"should fail for $fname") {
          val gotErrors = gotErrorsLzy.get
          val expected = checkFiles(f)
          if (gotErrors.isEmpty) {
            fail(s"No errors found for negative test $fname")
          } else {
            assert(gotErrors == expected, s"Incorrect reported errors for negative test $fname")
          }
        }
      }
    }
  }

  // A simple reporter that collect all errors.
  // Contrarily to TestSilentReporter, this report also extract the line referenced by the error message.
  class NegativeTestReporter(dir: String) extends DefaultReporter(Set.empty) {
    val allErrors = scala.collection.mutable.ArrayBuffer.empty[String]

    override def clearProgress(): Unit = ()

    override def doEmit(msg: Message): Unit = msg match {
      case Message(severity@(ERROR | FATAL), pos, msg) =>
        val errMsg = reline(severityToPrefix(severity), smartPos(pos) + msg.toString) + "\n" + getLineContent(pos, asciiOnly = true).getOrElse("")
        allErrors ++= errMsg.split("\n")
      case _ =>
    }

    override def doEmit(msg: ProgressMessage, prevLength: Int): String = msg.msg.toString

    def smartPos(p: Position): String = {
      if (p == NoPosition) {
        ""
      } else {
        val target = p.file.getAbsolutePath()
        val here = getClass.getResource(s"/$dir").getPath
        val diff = target.stripPrefix(here).stripPrefix("/")

        val filePos = diff + ":"

        filePos + p + ": "
      }
    }

    override protected def severityToPrefix(sev: Severity): String = sev match {
      case ERROR    => "[ Error  ]"
      case WARNING  => "[Warning ]"
      case INFO     => "[  Info  ]"
      case FATAL    => "[ Fatal  ]"
      case INTERNAL => "[Internal]"
      case DEBUG(_) => "[ Debug  ]"
    }
  }
}
