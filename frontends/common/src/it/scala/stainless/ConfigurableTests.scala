package stainless

import _root_.io.circe.{Json, JsonObject}
import stainless.extraction.utils.DebugSymbols
import stainless.extraction.xlang.trees as xt
import stainless.utils.CheckFilter

import java.io.File
import scala.util.matching.Regex

trait ConfigurableTests extends inox.ResourceUtils with InputUtils {
  type TestConf

  case class Benchmark(dir: String, runs: Seq[Run], syms: xt.Symbols)
  case class Run(variant: Option[Int], testConf: TestConf)

  val baseFolder: String

  lazy val benchmarkData: Seq[Benchmark] = Utils.getFolders(baseFolder)
    .flatMap(benchmark => loadBenchmark(s"$baseFolder/$benchmark").map { case (runs, syms) => Benchmark(benchmark, runs, syms) })

  val testConfPattern: Regex = "test_conf(_(\\d+))?.json".r
  val expectedOutcomePattern: Regex = "expected_outcome(_(\\d+))?.json".r

  def parseTestConf(f: File): TestConf

  def loadBenchmark(benchmarkDir: String): Option[(Seq[Run], xt.Symbols)] = {
    val files = resourceFiles(benchmarkDir, f => f.endsWith(".scala") || f.endsWith(".conf") || f.endsWith(".json")).sorted
    if (files.isEmpty) return None // Empty folder -- skip

    val scalaFiles = files.filter(_.getName.endsWith(".scala"))

    val confs = files.flatMap(f => f.getName match {
      case testConfPattern(_, num) =>
        val conf = parseTestConf(f)
        Some(Option(num).map(_.toInt) -> conf)
      case _ => None
    }).toMap
    assert(confs.nonEmpty, s"No test_conf.json found in $benchmarkDir")

    val runs = confs.keySet.toSeq.sorted.map(num => Run(num, confs(num)))

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

    Some((runs, programSymbols))
  }

  extension[T] (o: Option[T]) {
    def getOrCry(msg: String): T = o.getOrElse(throw AssertionError(msg))
  }
  extension (id: Identifier) {
    def fullName: String = CheckFilter.fixedFullName(id)
  }
  extension (jsonObj: JsonObject) {
    def getStringOrCry(field: String): String =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asString.getOrCry(s"Expected '$field' to be a string")

    def getIntOrCry(field: String): Int =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asNumber.getOrCry(s"Expected '$field' to be a number")
        .toInt.getOrCry(s"Expected '$field' to fit into an Int")

    def getObjectOrCry(field: String): JsonObject =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asObject.getOrCry(s"Expected '$field' to be an object")

    def getStringArrayOrCry(field: String): Seq[String] =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asArray.getOrCry(s"Expected '$field' to be an array of strings")
        .map(_.asString.getOrCry(s"Expected '$field' array elements to be strings"))

    def getArrayOrCry(field: String): Seq[Json] =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asArray.getOrCry(s"Expected '$field' to be an array")

    def getObjectArrayOrCry(field: String): Seq[JsonObject] =
      jsonObj(field).getOrCry(s"Expected a '$field' field")
        .asArray.getOrCry(s"Expected '$field' to be an array of object")
        .map(_.asObject.getOrCry(s"Expected '$field' array elements to be objects"))
  }
}
