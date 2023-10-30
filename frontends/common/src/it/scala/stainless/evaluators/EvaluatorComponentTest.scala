package stainless
package evaluators

import _root_.io.circe.JsonObject
import inox.{OptionValue, TestSilentReporter}
import org.scalatest.funsuite.AnyFunSuite
import stainless.equivchk.EquivalenceCheckingReport.Status
import stainless.extraction.utils.DebugSymbols
import stainless.extraction.xlang.{TreeSanitizer, extractor, trees as xt}
import stainless.extraction.{ExtractionSummary, extractionSemantics}
import stainless.utils.JsonUtils
import stainless.verification.*

import java.io.File
import scala.concurrent.Await
import scala.concurrent.duration.*

class EvaluatorComponentTest extends ComponentTestSuite {
  override val component: EvaluatorComponent.type = EvaluatorComponent

  override protected def optionsString(options: inox.Options): String = ""

  import EvaluatorComponentTest._

  for ((benchmarkDir, (testConf, programSymbols)) <- evalBenchmarkData) {
    for (evaluator <- testConf.evaluators) {
      test(s"$benchmarkDir ($evaluator)") { ctx0 ?=>
        val opt = evaluator match {
          case Evaluator.Recursive => optCodeGen(false)
          case Evaluator.Codegen => optCodeGen(true)
        }

        given ctx: inox.Context = ctx0.withOpts(opt)

        // Note that `run` must be defined here to pick the `ctx` with updated evaluator option.
        val run = component.run(extraction.pipeline)
        val exSymbols = run.extract(programSymbols)._1
        exSymbols.ensureWellFormed
        assert(ctx.reporter.errorCount == 0, "There were errors during pipeline extraction")

        val fnsToEval = exSymbols.functions.keys.filter(testConf.needsEvaluation).toSeq

        val groundValues = testConf.expected.collect {
          case EvalResult.SuccessfulEval(tested, ground) =>
            val groundFd = exSymbols.functions.find(_._1.name == ground)
              .getOrElse(fail(s"Function for ground result $ground not found"))
              ._2.fullBody
            tested -> groundFd
        }.toMap

        val report = Await.result(run.execute(fnsToEval, exSymbols, ExtractionSummary.NoSummary), Duration.Inf)
        for {
          res <- report.results
          exp <- testConf.expected.find(_.testedFn == res.fd.id.name)
        } {
          exp match {
            case EvalResult.SuccessfulEval(tested, _) =>
              res.status match {
                case EvaluatorRun.NoPost(bodyValue) =>
                  bodyValue shouldEqual groundValues(tested)
                case EvaluatorRun.PostHeld(bodyValue) =>
                  bodyValue shouldEqual groundValues(tested)
                case _ => fail(s"Evaluation of ${res.fd.id} did not succeed: got ${res.status}")
              }
            case EvalResult.FailedEval(_) =>
              res.status match {
                case EvaluatorRun.NoPost(_) | EvaluatorRun.PostHeld(_) =>
                  fail(s"Evaluation of ${res.fd.id} should have failed, but has succeeded")
                case _ => ()
              }
          }
        }
      }
    }
  }
}
object EvaluatorComponentTest extends inox.ResourceUtils with InputUtils {

  private lazy val evalBenchmarkData = getFolders("evaluators").flatMap(benchmark => loadEvalBenchmark(s"evaluators/$benchmark").map(benchmark -> _))

  private val testConfName = "test_conf.json"

  private case class TestConf(evaluators: Seq[Evaluator],
                              expected: Seq[EvalResult]) {
    def needsEvaluation(fn: Identifier): Boolean = expected.exists(_.testedFn == fn.name)
  }

  private enum Evaluator {
    case Recursive
    case Codegen
  }

  private enum EvalResult {
    case SuccessfulEval(fn: String, ground: String)
    case FailedEval(fn: String)

    def testedFn: String = this match {
      case SuccessfulEval(fn, _) => fn
      case FailedEval(fn) => fn
    }
  }

  private def getFolders(dir: String): Seq[String] = {
    Option(getClass.getResource(s"/$dir")).toSeq.flatMap { dirUrl =>
      val dirFile = new File(dirUrl.getPath)
      Option(dirFile.listFiles().toSeq).getOrElse(Seq.empty).filter(_.isDirectory)
        .map(_.getName)
    }.sorted
  }

  private def loadEvalBenchmark(benchmarkDir: String): Option[(TestConf, xt.Symbols)] = {
    val files = resourceFiles(benchmarkDir, f => f.endsWith(".scala") || f.endsWith(".json")).sorted
    if (files.isEmpty) return None // Empty folder -- skip

    val scalaFiles = files.filter(_.getName.endsWith(".scala"))
    val testConfFile = files.find(_.getName == testConfName)
      .getOrElse(sys.error(s"Test configuration file $testConfName not found in $benchmarkDir"))
    val testConf = parseTestConf(testConfFile)

    /////////////////////////////////////

    val dummyCtx: inox.Context = inox.TestContext.empty
    import dummyCtx.given
    val (_, program) = loadFiles(scalaFiles.map(_.getPath))
    assert(dummyCtx.reporter.errorCount == 0, "There should be no error while loading the files")

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = dummyCtx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    val programSymbols = userFiltering.debugWithoutSummary(frontend.UserFiltering().transform)(program.symbols)._1
    programSymbols.ensureWellFormed
    Some((testConf, programSymbols))
  }

  private def parseTestConf(f: File): TestConf = {
    val json = JsonUtils.parseFile(f)
    val jsonObj = json.asObject.getOrCry("Expected top-level json to be an object")
    val recEval = jsonObj("recursive").exists(_.asBoolean.getOrCry("Expected 'recursive' to be a boolean"))
    val codegenEval = jsonObj("codegen").exists(_.asBoolean.getOrCry("Expected 'codegen' to be a boolean"))
    if (!recEval && !codegenEval) {
      sys.error("At least one of 'recursive' or 'codegen' evaluator option must be set to true")
    }
    val evaluators = (if (recEval) Seq(Evaluator.Recursive) else Seq.empty) ++ (if (codegenEval) Seq(Evaluator.Codegen) else Seq.empty)

    val successful = jsonObj("successful").map { succ =>
      val elems = succ.asArray.getOrCry("Expected 'successful' to be an array")
      elems.map(_.asObject.getOrCry("Expected elements of 'successful' to be objects")).map { elem =>
        val fn = elem.getStringOrCry("function")
        val exp = elem.getStringOrCry("expected")
        EvalResult.SuccessfulEval(fn, exp)
      }
    }.getOrElse(Vector.empty)
    val failures = jsonObj("failure").map { succ =>
      val elems = succ.asArray.getOrCry("Expected 'failure' to be an array")
      elems.map(_.asObject.getOrCry("Expected elements of 'failure' to be objects")).map { elem =>
        val fn = elem.getStringOrCry("function")
        EvalResult.FailedEval(fn)
      }
    }.getOrElse(Vector.empty)
    TestConf(evaluators, successful ++ failures)
  }

  extension[T] (o: Option[T]) {
    private def getOrCry(msg: String): T = o.getOrElse(sys.error(msg))
  }

  extension (jsonObj: JsonObject) {
    private def getStringOrCry(field: String): String =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asString.getOrCry(s"Expected '$field' to a string")
  }
}