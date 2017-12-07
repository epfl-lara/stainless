/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{ trees => xt }
import frontend.{ CallBackWithRegistry, Frontend, MasterCallBack }
import utils.CheckFilter

import inox.utils.ASCIIHelpers.Row

import java.io.{ File, BufferedWriter, FileWriter }
import java.nio.file.Files

import scala.collection.mutable.ListBuffer

import _root_.io.circe.Json

import org.scalatest._

/**
 * Test suite for [[Registry]]. This suite used the specific [[Main]]
 * implementations. This therefore also test the extraction from the underlying
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
  private val testSuiteContext = if (DEBUG) {
    val reporter = new inox.DefaultReporter(Set(frontend.DebugSectionFrontend))
    val intrMan = inox.TestContext.empty.interruptManager
    inox.Context(reporter, intrMan)
  } else inox.TestContext.empty

  /** Filter functions and classes. */
  trait Filter {
    def shouldBeChecked(fd: xt.FunDef): Boolean
    def shouldBeChecked(cd: xt.ClassDef): Boolean
  }

  final object DefaultFilter extends Filter with CheckFilter {
    override val context = testSuiteContext
  }

  /** Expectation on classes and functions identifier name (ignoring ids). */
  case class Expectation(classes: Set[ClassName], functions: Set[FunctionName], strict: Boolean = true)

  /** Modification events: update the given set of files with their new content & the expected symbols. */
  case class UpdateEvent(contents: Map[FileName, Content], expected: Expectation)

  protected def testExtractionFailure(name: String, contents: Map[FileName, Content]): Unit = {
    common(name, DefaultFilter, contents.keySet) { case (fileMapping, compiler, _) =>
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
   *  - [[filter]]:       Symbol filter.
   *  - [[initialState]]: The initial state: should contain the content of every file
   *                      used in this scenario.
   *  - [[events]]:       A sequence of updates with the expected classes and
   *                      functions that should be re-processed.
   */
  protected def testScenario(name: String, filter: Filter,
                             initialState: UpdateEvent, events: Seq[UpdateEvent]): Unit = {
    common(name, filter, initialState.contents.keySet) { case (fileMapping, compiler, callback) =>
      // Process all events
      val allEvents = initialState +: events
      allEvents.zipWithIndex foreach { case (event, i) =>
        info(s"Event ${i + 1}/${allEvents.size}")

        writeContents(fileMapping, event.contents)
        compiler.run()
        compiler.join()
        val report = callback.popReport

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

  private def common(name: String, filter: Filter, filenames: Set[FileName])
                    (body: (Map[FileName, File], Frontend, MockCallBack) => Unit): Unit = test(name) {
    val basedir = Files.createTempDirectory("RegistryTestSuite").toFile
    basedir.deleteOnExit()

    // Create a mapping from filename to temporary File objects.
    val fileMapping = (filenames map { fn =>
      // NOTE filename must be at least three character long.
      val file = File.createTempFile(fn, ".scala", basedir)
      file.deleteOnExit()
      fn -> file
    }).toMap

    // Create our frontend with a mock callback
    val callback = new MockCallBack(testSuiteContext, filter)
    val master = new MasterCallBack(Seq(callback))
    val filePaths = fileMapping.values.toSeq map { _.getAbsolutePath }
    val compiler = Main.factory(testSuiteContext, filePaths, master)

    body(fileMapping, compiler, callback)
  }

  private def writeContents(fileMapping: Map[FileName, File], contents: Map[FileName, Content]): Unit = {
    contents foreach { case (fn, content) =>
      val file = fileMapping(fn)
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
    }
  }

  /** A simply dummy report for our [[MockCallBack]]. */
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

  /**
   * Mock callback for the purpose of testing the [[Registry]].
   *
   * [[filter]] needs to be set/updated before every frontend run.
   * It also provides a way to clear previously generated reports with [[popReports]].
   *
   * NOTE here we don't use the report from [[CallBackWithRegistry]] because it
   *      is not cleared upon new compilation.
   */
  private class MockCallBack(override val context: inox.Context, filter: Filter) extends CallBackWithRegistry {

    override val cacheSubDirectory = "mockcallback" // shouldn't be used here...
    override def parseReportCache(json: Json) = ??? // unused
    assert(context.options.findOption(frontend.optPersistentCache).isEmpty)

    override def shouldBeChecked(fd: xt.FunDef): Boolean = filter.shouldBeChecked(fd)
    override def shouldBeChecked(cd: xt.ClassDef): Boolean = filter.shouldBeChecked(cd)

    override type Report = MockReport

    override def onCycleBegin() = ()

    override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
      val fns = program.symbols.functions.keySet map { _.name }
      val cls = program.symbols.classes.keySet map { _.name }

      implicit val debugSection = frontend.DebugSectionFrontend
      context.reporter.debug(s"MockCallBack got the following to solve:")
      context.reporter.debug(s"\tfunctions: " + (fns mkString ", "))
      context.reporter.debug(s"\tclasses:   " + (cls mkString ", "))

      val report = MockReport(fns, cls)
      reports += report
      report
    }

    private val reports = ListBuffer[Report]()

    def popReport(): Report = {
      val res = reports.toSeq
      reports.clear()
      if (res.isEmpty) MockReport(Set.empty, Set.empty) else res reduce { _ ~ _ }
    }
  }

  val sourceAv0 =
    """|import stainless.lang._
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
    """|import stainless.lang._
       |import stainless.annotation._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { true }.holds
       |  def fun(o: Option[Int]): Boolean = { o match {
       |    case None() => false
       |    case Some(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { t.prop }.holds
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = true
       |}
       |""".stripMargin

  val sourceBv1 =
    """|import stainless.lang._
       |import stainless.annotation._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { false }.holds // HERE
       |  def fun(o: Option[Int]): Boolean = { o match {
       |    case None() => false
       |    case Some(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { t.prop }.holds
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = true
       |}
       |""".stripMargin

  val sourceBv2 =
    """|import stainless.lang._
       |import stainless.annotation._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { false }.holds
       |  def fun(o: Option[Int]): Boolean = { o match {
       |    case None() => false
       |    case Some(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { t.prop }.holds
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = false // HERE
       |}
       |""".stripMargin

  val sourceBv3 =
    """|import stainless.lang._
       |import stainless.annotation._
       |object B {
       |  case class Bottom(p: Boolean) extends A.Top {
       |    override def prop = p
       |  }
       |  def bar: Boolean = { false }.holds
       |  def fun(o: Option[Int]): Boolean = { o match {
       |    case None() => false
       |    case Some(x) => A.foobar(gun, x)
       |  } }.holds
       |  def gun(x: Int) = x >= 0
       |  def hun(t: A.Top): Boolean = { !t.prop }.holds // HERE
       |  def iun(b: Boolean) = Bottom(b)
       |  @ignore def unused = false
       |}
       |""".stripMargin

  testScenario("one run",
    DefaultFilter,
    UpdateEvent(
      Map("AAA" -> sourceAv0, "BBB" -> sourceBv0),
      Expectation(
        classes = Set("Top", "Bottom", "Option", "Some", "None"),
        functions = Set("foo", "foobar", "bar", "fun", "gun", "hun", "iun", "prop", "inv")
      )
    ),
    Seq.empty
  )

  testScenario("two identical runs",
    DefaultFilter,
    UpdateEvent(
      Map("AAA" -> sourceAv0, "BBB" -> sourceBv0),
      Expectation(
        classes = Set("Top", "Bottom", "Option", "Some", "None"),
        functions = Set("foo", "foobar", "bar", "fun", "gun", "hun", "iun", "prop", "inv")
      )
    ),
    Seq(
      UpdateEvent(Map.empty, Expectation(Set.empty, Set.empty))
    )
  )

  testScenario("watch",
    DefaultFilter,
    UpdateEvent(
      Map("AAA" -> sourceAv0, "BBB" -> sourceBv0),
      Expectation(
        classes = Set("Top", "Bottom", "Option", "Some", "None"),
        functions = Set("foo", "foobar", "bar", "fun", "gun", "hun", "iun", "prop", "inv")
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
          // functions = Set("hun", "prop", "inv")
          functions = Set("hun", "prop")
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

