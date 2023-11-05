package stainless

import _root_.io.circe.JsonObject
import org.scalatest.concurrent.*
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.{CancelAfterFailure, Tag, exceptions}
import stainless.extraction.xlang.{TreeSanitizer, trees as xt}
import stainless.utils.{CheckFilter, JsonUtils}
import stainless.verification.VerificationComponent

import java.io.File

class FilteringTestSuite extends AnyFunSuite with Matchers with TimeLimits {
  import FilteringTestSuite.*
  for (Benchmark(benchmarkDir, testConfs, programSymbols) <- benchmarkData) {
    given context: inox.Context = inox.TestContext.empty
    for (Run(variant, testConf) <- testConfs) {
      val testName = s"$benchmarkDir ${variant.map(v => s" (variant $v)").getOrElse("")}"
      test(testName) {
        val (exSymbols, exSummary) = stainless.extraction.pipeline.extract(programSymbols)
        val extractionFilter = CheckFilter(exSymbols.trees, context)
        val ids = exSymbols.functions.values.filter(id => testConf.toKeep(id.id.name)).map(_.id).toSeq
        // Note: passing a dummy VerificationComponent
        val toProcess = extractionFilter.filter(ids, exSymbols, VerificationComponent)
        val got = toProcess.groupMapReduce(_.name)(_ => 1)(_ + _).map(Results.apply).toSet
        got shouldEqual testConf.expected
      }
    }
  }
}
object FilteringTestSuite extends ConfigurableTests {
  case class TestConf(toKeep: Set[String], expected: Set[Results])
  case class Results(fn: String, occurrences: Int)

  override val baseFolder: String = "filtering"

  override def parseTestConf(f: File): TestConf = {
    val json = JsonUtils.parseFile(f)
    val jsonObj = json.asObject.getOrCry("Expected top-level json to be an object")
    val toKeep = jsonObj.getStringArrayOrCry("toKeep").toSet
    val expected = jsonObj.getArrayOrCry("expected")
      .map { objOrStr =>
        objOrStr.asString.map(Results(_, 1))
          .getOrElse {
            val obj = objOrStr.asObject.getOrCry("Expected 'expected' elements to be a string or an object")
            Results(obj.getStringOrCry("fn"), obj.getIntOrCry("occurrences"))
          }
      }.toSet
    TestConf(toKeep, expected)
  }
}