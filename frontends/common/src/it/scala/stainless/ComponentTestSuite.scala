/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import scala.concurrent.Await
import scala.concurrent.duration.*
import org.scalatest.time.Span
import org.scalatest.FixedThreadPoolParallelExecution
import stainless.utils.YesNoOnly
import extraction.ExtractionSummary
import extraction.xlang.{trees as xt}
import extraction.utils.DebugSymbols
import stainless.ComponentTestSuite.LoadedPrograms

import java.io.File

// Note: this class extends FixedThreadPoolParallelExecution which extends ParallelTestExecution.
// When extending ParallelTestExecution, scalatest will create a new instance for each parallel test,
// running the class init code many times.
// Therefore, to avoid duplicating work, one should instead load the program (with loadPrograms)
// in the companion object and save it to a lazy val, and then call testAll with the program symbols
// (or other relevant functions). See for instance ImperativeSuite.
// Note that loadProgramsWithResource allows for arbitrary computation when desired.
// See for instance VerificationComponentTestSuite which loads check files.
//
// When a custom logic is necessary without involving testAll, care must be again taken to not
// run "heavy work" in the test class itself but rather in its companion object, saved in a lazy val.
// See for instance EvaluatorComponentTest.
trait ComponentTestSuite extends inox.TestSuite with inox.ResourceUtils with InputUtils with FixedThreadPoolParallelExecution { self =>

  override def threadPoolSize: Int =
    scala.sys.props.get("testcase-parallelism").flatMap(_.toIntOption).getOrElse(1)

  override protected def sortingTimeout: Span = Span.Max

  val component: Component

  override def configurations: Seq[Seq[inox.OptionValue[?]]] = Seq(
    Seq(
      inox.optSelectedSolvers(Set("smt-z3")),
      inox.optTimeout(300.seconds),
      verification.optStrictArithmetic(false),
      frontend.optBatchedProgram(true),
      termination.optInferMeasures(false),
      termination.optCheckMeasures(YesNoOnly.No),
    )
  )

  final override def createContext(options: inox.Options) = stainless.TestContext(options)

  override protected def optionsString(options: inox.Options): String = {
    "solver=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels)
  }

  protected def filter(ctx: inox.Context, name: String): FilterStatus = Test

  def testAll(dir: String, lp: LoadedPrograms, identifierFilter: Identifier => Boolean = _ => true)
             (block: inox.Context ?=> (component.Analysis, inox.Reporter, xt.UnitDef, File) => Unit): Unit = {
    for {
      (unit, file) <- lp.unitsWithFile
      if unit.isMain
      name = unit.id.name
    } {
      test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx ?=>
        val defs = (unit.allFunctions(using lp.programSymbols).toSet ++ unit.allClasses).filter(identifierFilter)

        val deps = defs.flatMap(id => lp.programSymbols.dependencies(id) + id)
        val symbols = extraction.xlang.trees.NoSymbols
          .withClasses(lp.programSymbols.classes.values.filter(cd => deps(cd.id)).toSeq)
          .withFunctions(lp.programSymbols.functions.values.filter(fd => deps(fd.id)).toSeq)
          .withTypeDefs(lp.programSymbols.typeDefs.values.filter(td => deps(td.id)).toSeq)

        val run = component.run(extraction.pipeline)
        val exSymbols = run.extract(symbols)._1
        exSymbols.ensureWellFormed
        assert(ctx.reporter.errorCount == 0, "There were errors during pipeline extraction")

        val funs = inox.utils.fixpoint { (defs: Set[Identifier]) =>
          def derived(flags: Seq[run.trees.Flag]): Boolean =
            (defs & flags.collect { case run.trees.Derived(Some(id)) => id }.toSet).nonEmpty ||
              flags.contains(run.trees.Derived(None))

          defs ++
            exSymbols.functions.values.filter(fd => derived(fd.flags)).map(_.id) ++
            exSymbols.sorts.values.filter(sort => derived(sort.flags)).map(_.id)
        }(defs).toSeq.filter(exSymbols.functions.contains)

        val report = Await.result(run.execute(funs, exSymbols, ExtractionSummary.NoSummary), Duration.Inf)
        block(report, ctx.reporter, unit, file)
      }
    }
  }
}
object ComponentTestSuite extends inox.ResourceUtils with InputUtils {
  case class LoadedPrograms(unitsWithFile: Seq[(xt.UnitDef, File)], programSymbols: xt.Symbols)
  case class LoadedProgramsWithResource[R](lp: LoadedPrograms, resource: R)

  // Note: Scala files that are not kept will not even be loaded and extracted.
  def loadProgramsWithResource[R](dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true)
                                 (mkResource: LoadedPrograms => R): LoadedProgramsWithResource[R] = {
    val fs = resourceFiles(dir, f => f.endsWith(".scala") && keepOnly(f), recursive).toList
    val ctx: inox.Context = inox.TestContext.empty
    import ctx.given

    val (unitsWithFile, program) = loadFiles(fs.map(_.getPath))
    assert(ctx.reporter.errorCount == 0, "There should be no error while loading the files")

    val userFiltering = new DebugSymbols {
      val name = "UserFiltering"
      val context = ctx
      val s: xt.type = xt
      val t: xt.type = xt
    }

    val programSymbols = userFiltering.debugWithoutSummary(frontend.UserFiltering().transform)(program.symbols)._1
    programSymbols.ensureWellFormed
    val lp = LoadedPrograms(unitsWithFile, programSymbols)
    val resource = mkResource(lp)
    LoadedProgramsWithResource(lp, resource)
  }

  def loadPrograms(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true): LoadedPrograms =
    loadProgramsWithResource(dir, recursive, keepOnly)(_ => ()).lp
}
