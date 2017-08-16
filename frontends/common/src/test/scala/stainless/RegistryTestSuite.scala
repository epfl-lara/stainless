/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{ trees => xt }
import frontend.{ CallBackWithRegistry, Frontend }
import utils.CheckFilter

import inox.utils.ASCIIHelpers._

import java.io.{ File, BufferedWriter, FileWriter }
import java.nio.file.Files

import scala.collection.mutable.ListBuffer

import org.json4s.JsonAST.JArray

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
  private val ctx = if (DEBUG) {
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
    override val ctx = RegistryTestSuite.this.ctx
  }

  /** Expectation on classes and functions identifier name (ignoring ids). */
  case class Expectation(classes: Set[ClassName], functions: Set[FunctionName], strict: Boolean = true)

  /** Modification events: update the given set of files with their new content & the expected symbols. */
  case class UpdateEvent(contents: Map[FileName, Content], expected: Expectation)

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
                             initialState: UpdateEvent, events: Seq[UpdateEvent]): Unit = test(name) {
    val basedir = Files.createTempDirectory("RegistryTestSuite").toFile
    basedir.deleteOnExit()

    // Create a mapping from filename to temporary File objects.
    val filenames = initialState.contents.keySet
    val fileMapping = (filenames map { fn =>
      // NOTE filename must be at least three character long.
      val file = File.createTempFile(fn, ".scala", basedir)
      file.deleteOnExit()
      fn -> file
    }).toMap

    // Create our frontend with a mock callback
    val callback = new MockCallBack(ctx, filter)
    val filePaths = fileMapping.values.toSeq map { _.getAbsolutePath }
    val compiler = Main.factory(ctx, filePaths, callback)

    // Process all events
    val allEvents = initialState +: events
    allEvents.zipWithIndex foreach { case (event, i) =>
      info(s"Event ${i + 1}/${allEvents.size}")

      writeContents(fileMapping, event.contents)
      compiler.run()
      compiler.join()
      val report = reduce(callback.popReports)

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

  private def writeContents(fileMapping: Map[FileName, File], contents: Map[FileName, Content]): Unit = {
    contents foreach { case (fn, content) =>
      val file = fileMapping(fn)
      val out = new BufferedWriter(new FileWriter(file))
      out.write(content)
      out.close()
    }
  }

  private def reduce(reports: Seq[MockReport]): MockReport = {
    if (reports.isEmpty) MockReport(Set.empty, Set.empty)
    else reports reduce { _ ~ _ }
  }

  /** A simply dummy report for our [[MockCallBack]]. */
  private case class MockReport(functions: Set[FunctionName], classes: Set[ClassName]) extends AbstractReport {
    override val name = "dummy"
    override def emitJson = JArray(Nil)
    override val width = 0
    override def emitRowsAndStats: Option[(Seq[Row], ReportStats)] = None

    override def ~(other: AbstractReport): MockReport = other match {
      case MockReport(fns, cls) => MockReport(functions ++ fns, classes ++ cls)
      case _ => throw new RuntimeException("Unexpected report of type ${other.getClass}")
    }
  }

  /**
   * Mock callback for the purpose of testing the [[Registry]].
   *
   * [[filter]] needs to be set/updated before every frontend run.
   * It also provides a way to clear previously generated reports with [[popReports]].
   */
  private class MockCallBack(override val ctx: inox.Context, filter: Filter) extends CallBackWithRegistry {

    override def shouldBeChecked(fd: xt.FunDef): Boolean = filter.shouldBeChecked(fd)
    override def shouldBeChecked(cd: xt.ClassDef): Boolean = filter.shouldBeChecked(cd)

    override type Report = MockReport
    override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
      val fns = program.symbols.functions.keySet map { _.name }
      val cls = program.symbols.classes.keySet map { _.name }

      implicit val debugSection = frontend.DebugSectionFrontend
      ctx.reporter.debug(s"MockCallBack got the following to solve:")
      ctx.reporter.debug(s"\tfunctions: " + (fns mkString ", "))
      ctx.reporter.debug(s"\tclasses:   " + (cls mkString ", "))

      val report = MockReport(fns, cls)
      reports += report
      report
    }

    private val reports = ListBuffer[Report]()

    def popReports(): Seq[Report] = {
      val res = reports.toSeq
      reports.clear()
      res
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

}

