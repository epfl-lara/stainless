/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import scala.concurrent.Await
import scala.concurrent.duration._

import stainless.utils.YesNoOnly

import extraction.xlang.{ TreeSanitizer, trees => xt }
import extraction.utils.DebugSymbols

trait ComponentTestSuite extends inox.TestSuite with inox.ResourceUtils with InputUtils { self =>

  val component: Component

  override def configurations: Seq[Seq[inox.OptionValue[_]]] = Seq(
    Seq(
      verification.optTypeChecker(true),
      inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")),
      inox.optTimeout(300.seconds),
      verification.optStrictArithmetic(false),
      termination.optInferMeasures(false),
      termination.optCheckMeasures(YesNoOnly.No),
    )
  )

  final override def createContext(options: inox.Options) = stainless.TestContext(options)

  override protected def optionsString(options: inox.Options): String = {
    "solvr=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels) + " "
    "type-checker=" + options.findOptionOrDefault(verification.optTypeChecker)
  }

  protected def filter(ctx: inox.Context, name: String): FilterStatus = Test

  def testAll(dir: String, recursive: Boolean = false)(block: (component.Analysis, inox.Reporter) => Unit): Unit = {
    require(dir != null, "Function testAll must be called with a non-null directory string")
    val fs = resourceFiles(dir, _.endsWith(".scala"), recursive).toList

    // Toggle this variable if you need to debug one specific test.
    // You might also want to run `it:testOnly *<some test suite>* -- -z "<some test filter>"`.
    val DEBUG = false

    if (DEBUG) {
      for {
        file <- fs.sortBy(_.getPath)
        path = file.getPath
        name = file.getName stripSuffix ".scala"
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx ?=>
        val (structure, program) = loadFiles(Seq(path))
        assert(ctx.reporter.errorCount == 0, "There should be no error while loading the files")
        assert((structure count { _.isMain }) == 1, "Expecting only one main unit")

        val userFiltering = new DebugSymbols {
          val name = "UserFiltering"
          val context = ctx
          val s: xt.type = xt
          val t: xt.type = xt
        }

        val programSymbols = userFiltering.debug(frontend.UserFiltering().transform)(program.symbols)
        programSymbols.ensureWellFormed
        val errors = TreeSanitizer(xt).enforce(programSymbols)
        if (!errors.isEmpty) {
          ctx.reporter.fatalError("There were errors in TreeSanitizer")
        }

        val run = component.run(extraction.pipeline)

        val exProgram = inox.Program(run.trees)(run extract programSymbols)
        exProgram.symbols.ensureWellFormed
        assert(ctx.reporter.errorCount == 0, "There were errors during extraction")

        val unit = structure.find(_.isMain).get
        assert(unit.id.name == name, "Expecting compilation unit to have same name as source file")

        val defs = inox.utils.fixpoint { (defs: Set[Identifier]) =>
          def derived(flags: Seq[run.trees.Flag]): Boolean =
            (defs & flags.collect { case run.trees.Derived(Some(id)) => id }.toSet).nonEmpty ||
            flags.contains(run.trees.Derived(None))

          defs ++
          exProgram.symbols.functions.values.filter(fd => derived(fd.flags)).map(_.id) ++
          exProgram.symbols.sorts.values.filter(sort => derived(sort.flags)).map(_.id)
        } (unit.allFunctions(using program.symbols).toSet ++ unit.allClasses)

        val funs = defs.filter(exProgram.symbols.functions contains _).toSeq

        val report = Await.result(run.execute(funs, exProgram.symbols), Duration.Inf)
        block(report, ctx.reporter)
      }
    } else {
      val ctx: inox.Context = inox.TestContext.empty
      import ctx.given
      val (structure, program) = loadFiles(fs.map(_.getPath))
      assert(ctx.reporter.errorCount == 0, "There should be no error while loading the files")

      val userFiltering = new DebugSymbols {
        val name = "UserFiltering"
        val context = ctx
        val s: xt.type = xt
        val t: xt.type = xt
      }

      val programSymbols = userFiltering.debug(frontend.UserFiltering().transform)(program.symbols)
      programSymbols.ensureWellFormed

      for {
        unit <- structure
        if unit.isMain
        name = unit.id.name
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx ?=>
        val defs = unit.allFunctions(using programSymbols).toSet ++ unit.allClasses

        val deps = defs.flatMap(id => programSymbols.dependencies(id) + id)
        val symbols = extraction.xlang.trees.NoSymbols
          .withClasses(programSymbols.classes.values.filter(cd => deps(cd.id)).toSeq)
          .withFunctions(programSymbols.functions.values.filter(fd => deps(fd.id)).toSeq)
          .withTypeDefs(programSymbols.typeDefs.values.filter(td => deps(td.id)).toSeq)

        val run = component.run(extraction.pipeline)
        val exSymbols = run extract symbols
        exSymbols.ensureWellFormed
        assert(ctx.reporter.errorCount == 0, "There were errors during pipeline extraction")

        val funs = inox.utils.fixpoint { (defs: Set[Identifier]) =>
          def derived(flags: Seq[run.trees.Flag]): Boolean =
            (defs & flags.collect { case run.trees.Derived(Some(id)) => id }.toSet).nonEmpty ||
            flags.contains(run.trees.Derived(None))

          defs ++
          exSymbols.functions.values.filter(fd => derived(fd.flags)).map(_.id) ++
          exSymbols.sorts.values.filter(sort => derived(sort.flags)).map(_.id)
        } (defs).toSeq.filter(exSymbols.functions contains _)

        val report = Await.result(run.execute(funs, exSymbols),Duration.Inf)

        block(report, ctx.reporter)
      }
    }
  }
}

