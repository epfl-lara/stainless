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

  import EvaluatorComponentTest.*

  for (Benchmark(benchmarkDir, testConfs, programSymbols) <- benchmarkData) {
    for (Run(variant, testConf) <- testConfs) {
      for (evaluator <- testConf.evaluators) {
        val testName = s"$benchmarkDir ($evaluator)${variant.map(v => s" (variant $v)").getOrElse("")}"
        test(testName) { ctx0 ?=>
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
}
object EvaluatorComponentTest extends ConfigurableTests {
  override val baseFolder: String = "evaluators"

  case class TestConf(evaluators: Seq[Evaluator],
                      expected: Seq[EvalResult]) {
    def needsEvaluation(fn: Identifier): Boolean = expected.exists(_.testedFn == fn.name)
  }

  enum Evaluator {
    case Recursive
    case Codegen
  }

  enum EvalResult {
    case SuccessfulEval(fn: String, ground: String)
    case FailedEval(fn: String)

    def testedFn: String = this match {
      case SuccessfulEval(fn, _) => fn
      case FailedEval(fn) => fn
    }
  }

  override def parseTestConf(f: File): TestConf = {
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
}