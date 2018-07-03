/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import scala.concurrent.Await
import scala.concurrent.duration._

trait ComponentTestSuite extends inox.TestSuite with inox.ResourceUtils with InputUtils { self =>

  val component: Component

  override def configurations: Seq[Seq[inox.OptionValue[_]]] = Seq(
    Seq(inox.optSelectedSolvers(Set("smt-z3")), inox.optTimeout(300.seconds))
  )

  final override def createContext(options: inox.Options) = stainless.TestContext(options)

  override protected def optionsString(options: inox.Options): String = {
    "solvr=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels)
  }

  private class ComponentTestRun(val run: ComponentRun { val component: self.component.type }) {

    implicit val ctx: run.context.type = run.context

    type Structure = (
      Seq[extraction.xlang.trees.UnitDef],
      stainless.Program {
        val trees: extraction.xlang.trees.type
      },
      inox.Program {
        val trees: run.trees.type
        val symbols: run.trees.Symbols
      }
    )

    def apply(id: Identifier, symbols: extraction.xlang.trees.Symbols) =
      run.apply(id, symbols)

    def apply(functions: Seq[Identifier], symbols: run.trees.Symbols) =
      run.apply(functions, symbols)

    def extractStructure(files: Seq[String]): Structure = {
      val (structure, program) = loadFiles(files)

      program.symbols.ensureWellFormed
      val exProgram = inox.Program(run.trees)(run extract program.symbols)
      exProgram.symbols.ensureWellFormed

      assert(ctx.reporter.errorCount == 0)

      (structure, program, exProgram)
    }

    def extractFunctions(program: Program { val trees: extraction.xlang.trees.type },
                         exProgram: Program { val trees: run.trees.type },
                         unit: extraction.xlang.trees.UnitDef)
                        : Seq[Identifier] = {
      val unitDefs = unit.allFunctions(program.symbols) ++ unit.allClasses
      val allDefs = inox.utils.fixpoint { (defs: Set[Identifier]) =>
        def derived(flags: Seq[run.trees.Flag]): Boolean =
          (defs & flags.collect { case run.trees.Derived(id) => id }.toSet).nonEmpty

        defs ++
        exProgram.symbols.functions.values.filter(fd => derived(fd.flags)).map(_.id) ++
        exProgram.symbols.sorts.values.filter(sort => derived(sort.flags)).map(_.id)
      } (unitDefs.toSet)

      allDefs.filter(exProgram.symbols.functions contains _).toSeq
    }

    // Ensure no tests share data inappropriately, but is really slow... Use with caution!
    def extractOne(file: String): (String, Seq[Identifier], Program { val trees: run.trees.type }) = {
      val (structure, program, exProgram) = extractStructure(Seq(file))

      assert((structure count { _.isMain }) == 1, "Expecting only one main unit")
      val uOpt = structure find { _.isMain }
      val u = uOpt.get

      (u.id.name, extractFunctions(program, exProgram, u), exProgram)
    }

    // More efficient, but might mix tests together...
    def extractAll(files: Seq[String]): (Seq[(String, Seq[Identifier])], Program { val trees: run.trees.type }) = {
      val (structure, program, exProgram) = extractStructure(files)

      (for (u <- structure if u.isMain) yield {
        (u.id.name, extractFunctions(program, exProgram, u))
      }, exProgram)
    }
  }

  protected def filter(ctx: inox.Context, name: String): FilterStatus = Test

  def testAll(dir: String)(block: (component.Analysis, inox.Reporter) => Unit): Unit = {
    val fs = resourceFiles(dir, _.endsWith(".scala")).toList

    // Toggle this variable if you need to debug one specific test.
    // You might also want to run `it:testOnly *<some test suite>* -- -z "<some test filter>"`.
    val DEBUG = false

    if (DEBUG) {

      for {
        file <- fs.sortBy(_.getPath)
        path = file.getPath
        name = file.getName dropRight ".scala".length
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { implicit ctx =>
        val run = new ComponentTestRun(component.run(extraction.pipeline))
        val (uName, funs, program) = run.extractOne(path)
        assert(uName == name)
        val report = Await.result(run.apply(funs, program.symbols), Duration.Inf)
        block(report, ctx.reporter)
      }

    } else {
      val emptCtx = inox.TestContext.empty
      val run = new ComponentTestRun(component.run(extraction.pipeline(emptCtx))(emptCtx))
      val (funss, program) = run.extractAll(fs.map(_.getPath))
      for ((name, funs) <- funss) {
        test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { implicit ctx =>
          val run = new ComponentTestRun(component.run(extraction.pipeline))

          // We need to cast the symbols here because the program is extracted using a different ComponentTestRun instance
          // than the one the component is ran with. This should be safe (tm) because the trees are the same behind the scenes. - @romac
          val report = Await.result(run.apply(funs, program.symbols.asInstanceOf[run.run.trees.Symbols]), Duration.Inf)
          block(report, ctx.reporter)
        }
      }

    }
  }

}

