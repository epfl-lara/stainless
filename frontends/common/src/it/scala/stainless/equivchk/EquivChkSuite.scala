package stainless
package equivchk

import org.scalatest.funsuite.AnyFunSuite
import stainless.utils.{CheckFilter, JsonUtils, YesNoOnly}
import stainless.verification.*
import extraction.xlang.{TreeSanitizer, trees as xt}
import inox.{OptionValue, TestSilentReporter}
import stainless.equivchk.EquivalenceCheckingReport.Status
import stainless.extraction.utils.DebugSymbols

import java.io.File
import scala.concurrent.Await
import scala.concurrent.duration.*
import scala.util.{Failure, Success, Try}
import _root_.io.circe.JsonObject

class EquivChkSuite extends ComponentTestSuite {
  override val component: EquivalenceCheckingComponent.type = EquivalenceCheckingComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      inox.optTimeout(4.seconds),
      termination.optInferMeasures(true),
      termination.optCheckMeasures(YesNoOnly.Yes),
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  import EquivChkSuite._

  for (Benchmark(benchmarkDir, runs, programSymbols) <- benchmarkData) {
    for (Run(num, conf) <- runs) {
      val testName = s"$benchmarkDir${num.map(n => s" (variant $n)").getOrElse("")}"
      test(testName, ctx => filter(ctx, benchmarkDir)) { ctx0 ?=>
        val opts = Seq(
          optModels(conf.models.toSeq.sorted),
          optCompareFuns(conf.candidates.toSeq.sorted),
          optSilent(true)) ++
          conf.timeout.map(inox.optTimeout.apply) ++
          conf.norm.map(optNorm.apply).toSeq ++
          conf.n.map(optN.apply).toSeq ++
          conf.initScore.map(optInitScore.apply).toSeq ++
          conf.maxPerm.map(optMaxPerm.apply).toSeq
        val ids = programSymbols.functions.keySet.toSeq
        val programSymbols2 = {
          if (conf.tests.isEmpty) programSymbols
          else {
            val annotated = programSymbols.functions.view.filter { case (fn, _) => conf.tests(fn.fullName) }
              .mapValues(fd => fd.copy(flags = fd.flags :+ xt.Annotation("mkTest", Seq.empty)))
            programSymbols.copy(functions = programSymbols.functions ++ annotated)
          }
        }
        // Uncomment the `.copy(...)` to print equiv. chk. output
        val ctx = ctx0.withOpts(opts: _*)//.copy(reporter = new inox.DefaultReporter(Set(DebugSectionEquivChk)))
        given inox.Context = ctx
        val report = Await.result(component.run(extraction.pipeline).apply(ids, programSymbols2), Duration.Inf)
        val got = extractResults(conf.candidates, report)
        got shouldEqual conf.results
      }
    }
  }

  private def extractResults(candidates: Set[String], analysis: component.Analysis): Results = {
    import EquivalenceCheckingReport._
    analysis.records.foldLeft(Results.empty) {
      case (acc, record) =>
        val fn = record.id.fullName
        if (candidates(fn)) {
          record.status match {
            case Status.Equivalence(EquivalenceStatus.Valid(mod, _, _)) =>
              val currCluster = acc.equiv.getOrElse(mod.fullName, Set.empty)
              acc.copy(equiv = acc.equiv + (mod.fullName -> (currCluster + fn)))
            case Status.Equivalence(EquivalenceStatus.Unequivalent) => acc.copy(unequivalent = acc.unequivalent + fn)
            case Status.Equivalence(EquivalenceStatus.Unsafe) => acc.copy(unsafe = acc.unsafe + fn)
            case Status.Equivalence(EquivalenceStatus.Unknown) => acc.copy(timeout = acc.timeout + fn)
            case Status.Equivalence(EquivalenceStatus.Wrong) => acc.copy(wrong = acc.wrong + fn)
            case Status.Verification(_) => acc
          }
        } else acc
    }
  }
}
object EquivChkSuite extends ConfigurableTests {
  override val baseFolder: String = "equivalence"

  case class Results(equiv: Map[String, Set[String]],
                     unequivalent: Set[String],
                     unsafe: Set[String],
                     timeout: Set[String],
                     wrong: Set[String])

  object Results {
    def empty: Results =
      Results(Map.empty, Set.empty, Set.empty, Set.empty, Set.empty)
  }

  case class TestConf(models: Set[String],
                      candidates: Set[String],
                      tests: Set[String],
                      norm: Option[String],
                      n: Option[Int],
                      initScore: Option[Int],
                      maxPerm: Option[Int],
                      timeout: Option[Duration],
                      results: Results)

  override def parseTestConf(f: File): TestConf = {
    val json = JsonUtils.parseFile(f)
    val jsonObj = json.asObject.getOrCry("Expected top-level json to be an object")
    val models = jsonObj.getStringArrayOrCry("models")
    val candidates = jsonObj.getStringArrayOrCry("comparefuns")
    val tests = if (jsonObj.contains("tests")) jsonObj.getStringArrayOrCry("tests") else Seq.empty
    val norm = jsonObj("norm").map(_.asString.getOrCry("Expected 'norm' to be a string"))
    val n = jsonObj("n").map(_.asNumber.getOrCry("Expected 'n' to be an int").toInt.getOrCry("'n' is too large"))
    val initScore = jsonObj("init-score").map(_.asNumber.getOrCry("Expected 'init-score' to be an int").toInt.getOrCry("'init-score' is too large"))
    val maxPerm = jsonObj("max-perm").map(_.asNumber.getOrCry("Expected 'max-perm' to be an int").toInt.getOrCry("'max-perm' is too large"))
    val timeout = jsonObj("timeout").map(_.asNumber.getOrCry("Expected 'timeout' to be an double").toDouble)
    assert(models.nonEmpty, "At least one model must be specified")
    assert(candidates.nonEmpty, "At least one candidate must be specified")
    val res = parseExpectedOutcome(jsonObj.getObjectOrCry("outcome"))
    TestConf(models.toSet, candidates.toSet, tests.toSet, norm, n, initScore, maxPerm, timeout.map(_.seconds), res)
  }

  private def parseExpectedOutcome(jsonObj: JsonObject): Results = {
    val equivObj = jsonObj("equivalent").getOrCry("Expected 'equivalent' field")
      .asArray.getOrCry("Expected 'equivalent' to be an array")
    val equiv = equivObj.map { elem =>
      val elemObj = elem.asObject.getOrCry("Expected elements in 'equivalent' to be objects")
      val model = elemObj("model").getOrCry("Expected a 'model' field in 'equivalent'")
        .asString.getOrCry("Expected 'model' to be a string")
      val fns = elemObj.getStringArrayOrCry("functions").toSet
      model -> fns
    }.toMap
    val unequivalent = jsonObj.getStringArrayOrCry("unequivalent").toSet
    val unsafe = jsonObj.getStringArrayOrCry("unsafe").toSet
    val timeout = jsonObj.getStringArrayOrCry("timeout").toSet
    val wrong = jsonObj.getStringArrayOrCry("wrong").toSet
    Results(equiv, unequivalent, unsafe, timeout, wrong)
  }
}
