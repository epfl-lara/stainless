/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import scala.language.existentials

import extraction.xlang.{ trees => xt }
import frontend.{ Frontend, CallBack }
import utils.CheckFilter

import inox.utils.ASCIIHelpers.Row

import java.io.{ File, BufferedWriter, FileWriter }
import java.nio.file.Files

import scala.collection.mutable.ListBuffer
import scala.concurrent.Future

import _root_.io.circe.Json

import org.scalatest._

/**
 * Test suite for [[Registry]]. This suite used the specific [[Main]]
 * implementations. This therefore also tests the extraction from the underlying
 * Scala compiler, making sure symbols are properly mapped to stainless/inox
 * identifiers.
 *
 * See [[testScenario]] for the details of this suite.
 */
class RegistryTestSuite extends FunSuite {

  type Content = String
  type FileName = String
  type ClassName = String
  type FunctionName = String

  private val DEBUG = false
  private val testSuiteContext =
    if (DEBUG) stainless.TestContext.debug(utils.DebugSectionRegistry)
    else stainless.TestContext.empty

  /** Expectation on classes and functions identifier name (ignoring ids). */
  case class Expectation(classes: Set[ClassName], functions: Set[FunctionName], strict: Boolean = true)

  /** Modification events: update the given set of files with their new content & the expected symbols. */
  case class UpdateEvent(contents: Map[FileName, Content], expected: Expectation)

  protected def testExtractionFailure(name: String, contents: Map[FileName, Content]): Unit = {
    common(name, contents.keySet) { case (fileMapping, compiler, _) =>
      writeContents(fileMapping, contents)
      intercept[inox.FatalError] {
        compiler.run()
        compiler.join()
      }
    }
  }

  /**
   * Test a scenario.
   *
   *  - [[name]]:         The scenario's name.
   *  - [[initialState]]: The initial state: should contain the content of every file
   *                      used in this scenario.
   *  - [[events]]:       A sequence of updates with the expected classes and
   *                      functions that should be re-processed.
   */
  protected def testScenario(name: String, initialState: UpdateEvent, events: Seq[UpdateEvent]): Unit = {
    common(name, initialState.contents.keySet) { case (fileMapping, compiler, run) =>
      // Process all events
      val allEvents = initialState +: events
      allEvents.zipWithIndex foreach { case (event, i) =>
        info(s"Event ${i + 1}/${allEvents.size}")

        writeContents(fileMapping, event.contents)
        compiler.run()
        compiler.join()
        val report = run.popReport()

        if (event.expected.strict) {
          assert(report.functions === event.expected.functions, "Collected functions mismatch expectation (strict)")
          assert(report.classes === event.expected.classes, "Collected classes mismatch expectation (strict)")
        } else {
          assert((report.functions & event.expected.functions) === event.expected.functions,
                 "Collected functions mismatch expectation")
          assert((report.classes & event.expected.classes) === event.expected.classes,
                 "Collected classes mismatch expectation")
        }
      }
    }
  }

  private class MockCallBack(run: ComponentRun)(implicit ctx: inox.Context) extends frontend.StainlessCallBack(Seq(MockComponent))

  private def common(name: String, filenames: Set[FileName])
                    (body: (Map[FileName, File], Frontend, MockComponentRun) => Unit): Unit = test(name) {
    val basedir = Files.createTempDirectory("RegistryTestSuite").toFile
    basedir.deleteOnExit()

    // Create a mapping from filename to temporary File objects.
    val fileMapping = (filenames map { fn =>
      // NOTE filename must be at least three character long.
      val file = File.createTempFile(fn, ".scala", basedir)
      file.deleteOnExit()
      fn -> file
    }).toMap

    // Create our frontend with a mock component
    val filePaths = fileMapping.values.toSeq map { _.getAbsolutePath }
    val run = MockComponent.run(extraction.pipeline(testSuiteContext))(testSuiteContext)
    val compiler = Main.factory(testSuiteContext, filePaths, new MockCallBack(run)(testSuiteContext))

    body(fileMapping, compiler, run)
  }

  private def writeContents(fileMapping: Map[FileName, File], contents: Map[FileName, Content]): Unit = {
    contents foreach { case (fn, content) =>
      val file = fileMapping(fn)
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
    }
  }

  private case class MockReport(functions: Set[FunctionName], classes: Set[ClassName]) extends AbstractReport[MockReport] {
    override val name = "dummy"

    override def emitJson = ???
    override def annotatedRows = ???
    override def stats = ???

    override def filter(ids: Set[Identifier]) = this // intentionally not filtering a thing!
    // here we don't test the reports themselves, but the registry.

    override def ~(other: MockReport): MockReport =
      MockReport(functions ++ other.functions, classes ++ other.classes)
  }

  /** A simply dummy analysis that wraps our [[MockReport]]. */
  private case class MockAnalysis(report: MockReport) extends AbstractAnalysis {
    override val name = "dummy"
    override type Report = MockReport
    override def toReport = report
  }

  /**
   * Mock component for the purpose of testing the [[Registry]].
   *
   * [[filter]] needs to be set/updated before every frontend run.
   * It also provides a way to clear previously generated reports with [[popReports]].
   *
   * NOTE here we don't use the report from [[StainlessCallBack]] because it
   *      is not cleared upon new compilation.
   */
  private object MockComponent extends Component {
    val name = "mockcomponent"
    val description = "componing for testing stainless callback"

    type Report = MockReport
    type Analysis = MockAnalysis

    val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
      override val s: extraction.trees.type = extraction.trees
      override val t: extraction.trees.type = extraction.trees
    })

    private[this] val runCache = scala.collection.mutable.Map.empty[inox.Context, MockComponentRun]

    override def run(pipeline: extraction.StainlessPipeline)(implicit context: inox.Context) =
      runCache.getOrElseUpdate(context, new MockComponentRun(pipeline))
  }

  /** Mock component run associated to [[MockComponent]]. */
  private class MockComponentRun(override val pipeline: extraction.StainlessPipeline)
                                (override implicit val context: inox.Context)
  extends {
    val component = MockComponent
    val trees: extraction.xlang.trees.type = extraction.xlang.trees
  } with ComponentRun {
    import component.{Report, Analysis}

    def parse(json: Json): Report = ???

    override def extract(symbols: extraction.xlang.trees.Symbols): trees.Symbols = {
      val fns = symbols.functions.keySet map { _.name }
      val cls = symbols.classes.keySet map { _.name }

      implicit val debugSection = frontend.DebugSectionFrontend
      implicit val printOpts = trees.PrinterOptions.fromContext(context)
      import context.reporter
      reporter.debug(s"MockCallBack got the following to solve:")
      reporter.debug(s"\tfunctions: " + (symbols.functions.keySet map { _.asString } mkString ", "))
      reporter.debug(s"\tclasses:   " + (symbols.classes.keySet map { _.asString } mkString ", "))

      val report = MockReport(fns, cls)
      val analysis = MockAnalysis(report)

      reports += report

      super.extract(symbols)
    }

    override def apply(functions: Seq[Identifier], symbols: trees.Symbols): Future[Analysis] = {
      val report = MockReport(Set.empty, Set.empty)
      val analysis = MockAnalysis(report)
      Future.successful(analysis)
    }

    private val reports = ListBuffer[Report]()

    def popReport(): Report = {
      val res = reports.toSeq
      reports.clear()
      if (res.isEmpty) MockReport(Set.empty, Set.empty) else res reduce { _ ~ _ }
    }
  }

  // NOTE The tests are placed in a subpackage of `stainless` to get access to
  //      the @ignore annotation.

  val sourceOptions =
    """|package stainless.test
       |object Options {
       |  sealed abstract class MyOption[T]
       |  case class MyNone[T]() extends MyOption[T]
       |  case class MySome[T](x: T) extends MyOption[T]
       |}
       |""".stripMargin

  val sourceAv0 =
    """|package stainless.test
       |import stainless.lang._
       |object A {
       |  abstract class Top {
       |    require(prop)
       |    def prop: Boolean
       |  }
       |  def foo: Boolean = { B.bar }.holds
       |  def foobar(f: Int => Boolean, x: Int): Boolean = f(x)
       |}
       |""".stripMargin

  val sourceBv0 =
    """|package stainless.test
       |import stainless.lang._
       |import stainless.annotation._
       |import Options._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { true }.holds
       |  def fun(o: MyOption[Int]): Boolean = { o match {
       |    case MyNone() => false
       |    case MySome(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { t.prop }.holds
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = true
       |}
       |""".stripMargin

  val sourceBv1 =
    """|package stainless.test
       |import stainless.lang._
       |import stainless.annotation._
       |import Options._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { false }.holds // HERE
       |  def fun(o: MyOption[Int]): Boolean = { o match {
       |    case MyNone() => false
       |    case MySome(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { t.prop }.holds
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = true
       |}
       |""".stripMargin

  val sourceBv2 =
    """|package stainless.test
       |import stainless.lang._
       |import stainless.annotation._
       |import Options._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { false }.holds
       |  def fun(o: MyOption[Int]): Boolean = { o match {
       |    case MyNone() => false
       |    case MySome(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { t.prop }.holds
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = false // HERE
       |}
       |""".stripMargin

  val sourceBv3 =
    """|package stainless.test
       |import stainless.lang._
       |import stainless.annotation._
       |import Options._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { false }.holds
       |  def fun(o: MyOption[Int]): Boolean = { o match {
       |    case MyNone() => false
       |    case MySome(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { !t.prop }.holds // HERE
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = false
       |}
       |""".stripMargin

  testScenario("one run",
    UpdateEvent(
      Map("Options" -> sourceOptions, "AAA" -> sourceAv0, "BBB" -> sourceBv0),
      Expectation(
        classes = Set("Top", "Bottom", "MyOption", "MySome", "MyNone"),
        functions = Set(
          "foo", "foobar", "bar", "fun", "gun", "hun", "iun", "prop", "inv", // functions
          "x", "p" // accessors
        )
      )
    ),
    Seq.empty
  )

  testScenario("two identical runs",
    UpdateEvent(
      Map("Options" -> sourceOptions, "AAA" -> sourceAv0, "BBB" -> sourceBv0),
      Expectation(
        classes = Set("Top", "Bottom", "MyOption", "MySome", "MyNone"),
        functions = Set(
          "foo", "foobar", "bar", "fun", "gun", "hun", "iun", "prop", "inv", // functions
          "x", "p" // accessors
        )
      )
    ),
    Seq(
      UpdateEvent(Map.empty, Expectation(Set.empty, Set.empty))
    )
  )

  testScenario("watch",
    UpdateEvent(
      Map("Options" -> sourceOptions, "AAA" -> sourceAv0, "BBB" -> sourceBv0),
      Expectation(
        classes = Set("Top", "Bottom", "MyOption", "MySome", "MyNone"),
        functions = Set(
          "foo", "foobar", "bar", "fun", "gun", "hun", "iun", "prop", "inv", // functions
          "x", "p" // accessors
        )
      )
    ),
    Seq(
      UpdateEvent(
        Map("BBB" -> sourceBv1),
        Expectation(
          classes = Set.empty,
          functions = Set("bar", "foo")
        )
      ),
      UpdateEvent(
        Map("BBB" -> sourceBv2),
        Expectation(
          classes = Set.empty,
          functions = Set.empty
        )
      ),
      UpdateEvent(
        Map("BBB" -> sourceBv3),
        Expectation(
          classes = Set("Top", "Bottom"),
          functions = Set("p", "hun", "prop", "inv")
        )
      )
    )
  )

  val arraySeq =
    """|import scala.collection.mutable.ArraySeq
       |object Unsupported {
       |  def foo[T](a: Array[T], i: Int, t: T): ArraySeq[T] = {
       |    require(i >= 0 && i < a.length)
       |    a.updated(i, t)
       |  }
       |}""".stripMargin

  val classTag =
    """|import scala.reflect.ClassTag
       |object Unsupported {
       |  def foo[T](a: Array[T], i: Int, t: T)(implicit m: ClassTag[T]): Array[T] = {
       |    require(i >= 0 && i < a.length)
       |    a.updated(i, t)
       |  }
       |}""".stripMargin

  // Those tests make sure missing features are reported as errors when running stainless the usual way.
  testExtractionFailure("ArraySeq not supported", Map("Unsupported" -> arraySeq))
  testExtractionFailure("ClassTag not supported", Map("Unsupported" -> classTag))

}

