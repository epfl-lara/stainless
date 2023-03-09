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

  private val testConfPattern = "test_conf(_(\\d+))?.json".r
  private val expectedOutcomePattern = "expected_outcome(_(\\d+))?.json".r

  override protected def optionsString(options: inox.Options): String = ""

  ///////////////////////////////////////////////

  for (benchmark <- getFolders("equivalence")) {
    testEquiv(s"equivalence/$benchmark")
  }

  ///////////////////////////////////////////////

  private def getFolders(dir: String): Seq[String] = {
    Option(getClass.getResource(s"/$dir")).toSeq.flatMap { dirUrl =>
      val dirFile = new File(dirUrl.getPath)
      Option(dirFile.listFiles().toSeq).getOrElse(Seq.empty).filter(_.isDirectory)
        .map(_.getName)
    }.sorted
  }

  private def testEquiv(benchmarkDir: String): Unit = {
    val files = resourceFiles(benchmarkDir, f => f.endsWith(".scala") || f.endsWith(".conf") || f.endsWith(".json")).sorted
    if (files.isEmpty) return // Empty folder -- skip

    val scalaFiles = files.filter(_.getName.endsWith(".scala"))

    val confs = files.flatMap(f => f.getName match {
      case testConfPattern(_, num) => Some(Option(num).map(_.toInt) -> f)
      case _ => None
    }).toMap
    assert(confs.nonEmpty, s"No test_conf.json found in $benchmarkDir")

    val expectedOutcomes = files.flatMap(f => f.getName match {
      case expectedOutcomePattern(_, num) => Some(Option(num).map(_.toInt) -> f)
      case _ => None
    }).toMap
    assert(expectedOutcomes.nonEmpty, s"No expected_outcome.json found in $benchmarkDir")
    assert(confs.keySet == expectedOutcomes.keySet, "Test configuration and expected outcome files do not match")

    val runs = confs.keySet.toSeq.sorted.map { num =>
      (num, confs(num), expectedOutcomes(num))
    }

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

    /////////////////////////////////////

    for ((num, confFile, expectedOutomeFile) <- runs) {
      val conf = parseTestConf(confFile)
      val expected = parseExpectedOutcome(expectedOutomeFile)

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
        got shouldEqual expected
      }
    }
  }

  private case class EquivResults(equiv: Map[String, Set[String]],
                                  erroneous: Set[String],
                                  timeout: Set[String],
                                  wrong: Set[String])
  private object EquivResults {
    def empty: EquivResults =
      EquivResults(Map.empty[String, Set[String]], Set.empty[String], Set.empty[String], Set.empty[String])
  }

  private case class TestConf(models: Set[String],
                              candidates: Set[String],
                              tests: Set[String],
                              norm: Option[String],
                              n: Option[Int],
                              initScore: Option[Int],
                              maxPerm: Option[Int],
                              timeout: Option[Duration])

  private def extractResults(candidates: Set[String], analysis: component.Analysis): EquivResults = {
    import EquivalenceCheckingReport._
    analysis.records.foldLeft(EquivResults.empty) {
      case (acc, record) =>
        val fn = record.id.fullName
        if (candidates(fn)) {
          record.status match {
            case Status.Equivalence(EquivalenceStatus.Valid(mod, _, _)) =>
              val currCluster = acc.equiv.getOrElse(mod.fullName, Set.empty)
              acc.copy(equiv = acc.equiv + (mod.fullName -> (currCluster + fn)))
            case Status.Equivalence(EquivalenceStatus.Erroneous) => acc.copy(erroneous = acc.erroneous + fn)
            case Status.Equivalence(EquivalenceStatus.Unknown) => acc.copy(timeout = acc.timeout + fn)
            case Status.Equivalence(EquivalenceStatus.Wrong) => acc.copy(wrong = acc.wrong + fn)
            case Status.Verification(_) => acc
          }
        } else acc
    }
  }

  private def parseExpectedOutcome(f: File): EquivResults = {
    val json = JsonUtils.parseFile(f)
    val jsonObj = json.asObject.getOrCry("Expected top-level json to be an object")

    val equivObj = jsonObj("equivalent").getOrCry("Expected 'equivalent' field")
      .asArray.getOrCry("Expected 'equivalent' to be an array")
    val equiv = equivObj.map { elem =>
      val elemObj = elem.asObject.getOrCry("Expected elements in 'equivalent' to be objects")
      val model = elemObj("model").getOrCry("Expected a 'model' field in 'equivalent'")
        .asString.getOrCry("Expected 'model' to be a string")
      val fns = elemObj.getStringArrayOrCry("functions").toSet
      model -> fns
    }.toMap
    val erroneous = jsonObj.getStringArrayOrCry("erroneous").toSet
    val timeout = jsonObj.getStringArrayOrCry("timeout").toSet
    val wrong = jsonObj.getStringArrayOrCry("wrong").toSet
    EquivResults(equiv, erroneous, timeout, wrong)
  }

  private def parseTestConf(f: File): TestConf = {
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
    TestConf(models.toSet, candidates.toSet, tests.toSet, norm, n, initScore, maxPerm, timeout.map(_.seconds))
  }

  extension[T] (o: Option[T]) {
    private def getOrCry(msg: String): T = o.getOrElse(throw AssertionError(msg))
  }
  extension (id: Identifier) {
    private def fullName: String = CheckFilter.fixedFullName(id)
  }
  extension (jsonObj: JsonObject) {
    private def getStringArrayOrCry(field: String): Seq[String] =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
      .asArray.getOrCry(s"Expected '$field' to be an array of strings")
      .map(_.asString.getOrCry(s"Expected '$field' array elements to be strings"))
  }
}
