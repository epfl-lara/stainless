/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import scala.concurrent.duration._

trait ComponentTestSuite extends inox.TestSuite with inox.ResourceUtils {

  val component: SimpleComponent

  override def configurations: Seq[Seq[inox.OptionValue[_]]] = Seq(
    Seq(inox.optSelectedSolvers(Set("smt-z3")), inox.optTimeout(300.seconds))
  )

  override protected def optionsString(options: inox.Options): String = {
    "solvr=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels)
  }

  // Ensure no tests share data inappropriately, but is really slow... use for debugging!!!
  private def extractOne(file: String): (String, Seq[Identifier], Program { val trees: component.trees.type }) = {
    val reporter = new inox.TestSilentReporter

    val ctx = inox.Context(reporter, new inox.utils.InterruptManager(reporter))
    val (structure, program) = Main.extractFromSource(ctx, Main.libraryFiles :+ file)
    program.symbols.ensureWellFormed
    val exProgram = component.extract(program)
    exProgram.symbols.ensureWellFormed

    assert(reporter.lastErrors.isEmpty)

    val uOpt = structure find { _.isMain }
    val u = uOpt.get

    val unitFuns = u.allFunctions(program.symbols)
    val allFuns = inox.utils.fixpoint { (funs: Set[Identifier]) =>
      funs ++ exProgram.symbols.functions.values.flatMap { fd =>
        val source = fd.flags.collect { case component.trees.Derived(id) => id }.toSet
        if ((source intersect funs).nonEmpty) {
          Some(fd.id)
        } else {
          None
        }
      }
    } (unitFuns.toSet)

    (u.id.name, allFuns.toSeq, exProgram)
  }

  // More efficient, but might mix tests together...
  private def extractAll(files: Seq[String]): (Seq[(String, Seq[Identifier])], Program { val trees: component.trees.type }) = {
    val reporter = new inox.TestSilentReporter

    val ctx = inox.Context(reporter, new inox.utils.InterruptManager(reporter))
    val (structure, program) = Main.extractFromSource(ctx, Main.libraryFiles ++ files.toList)
    program.symbols.ensureWellFormed
    val exProgram = component.extract(program)
    exProgram.symbols.ensureWellFormed

    assert(reporter.lastErrors.isEmpty)
    (for (u <- structure if u.isMain) yield {
      val unitFuns = u.allFunctions(program.symbols)
      val allFuns = inox.utils.fixpoint { (funs: Set[Identifier]) =>
        funs ++ exProgram.symbols.functions.values.flatMap { fd =>
          val source = fd.flags.collect { case component.trees.Derived(id) => id }.toSet
          if ((source intersect funs).nonEmpty) {
            Some(fd.id)
          } else {
            None
          }
        }
      } (unitFuns.toSet)
      (u.id.name, allFuns.toSeq)
    }, exProgram)
  }

  protected def filter(ctx: inox.Context, name: String): FilterStatus = Test

  def testAll(dir: String)(block: (component.Report, inox.Reporter) => Unit): Unit = {
    val fs = resourceFiles(dir, _.endsWith(".scala")).toList

    // Toggle this variable if you need to debug one specific test.
    // You might also want to run `it:testOnly *<some test suite>* -- -z "<some test filter>"`.
    val DEBUG = false

    if (DEBUG) {

      for {
        file <- fs
        path = file.getPath
        name = file.getName dropRight (".scala".length)
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx =>
        val (uName, funs, program) = extractOne(path)
        assert(uName == name)
        val newProgram = program.withContext(ctx)
        val report = component.apply(funs, newProgram)
        block(report, ctx.reporter)
      }

    } else {

      val (funss, program) = extractAll(fs.map(_.getPath))
      for ((name, funs) <- funss) {
        test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx =>
          val newProgram = program.withContext(ctx)
          val report = component.apply(funs, newProgram)
          block(report, ctx.reporter)
        }
      }

    }
  }
}
