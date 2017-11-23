/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import scala.concurrent.duration._

trait ComponentTestSuite extends inox.TestSuite with inox.ResourceUtils with InputUtils {

  val component: SimpleComponent

  override def configurations: Seq[Seq[inox.OptionValue[_]]] = Seq(
    Seq(inox.optSelectedSolvers(Set("smt-z3")), inox.optTimeout(300.seconds))
  )

  final override def createContext(options: inox.Options) = stainless.TestContext(options)

  override protected def optionsString(options: inox.Options): String = {
    "solvr=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels)
  }

  private def extractStructure(files: Seq[String], ctx: inox.Context) = {
    val (structure, program) = loadFiles(ctx, files)

    program.symbols.ensureWellFormed
    val exProgram = component.extract(program, ctx)
    exProgram.symbols.ensureWellFormed

    assert(ctx.reporter.errorCount == 0)

    (structure, program, exProgram)
  }

  // Ensure no tests share data inappropriately, but is really slow... Use with caution!
  private def extractOne(file: String, ctx: inox.Context)
              : (String, Seq[Identifier], Program { val trees: component.trees.type }) = {
    val (structure, program, exProgram) = extractStructure(Seq(file), ctx)

    assert((structure count { _.isMain }) == 1, "Expecting only one main unit")
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
    } (unitFuns.filter(exProgram.symbols.functions contains _).toSet)

    (u.id.name, allFuns.toSeq, exProgram)
  }

  // More efficient, but might mix tests together...
  private def extractAll(files: Seq[String], ctx: inox.Context)
              : (Seq[(String, Seq[Identifier])], Program { val trees: component.trees.type }) = {
    val (structure, program, exProgram) = extractStructure(files, ctx)

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
      } (unitFuns.filter(exProgram.symbols.functions contains _).toSet)
      (u.id.name, allFuns.toSeq)
    }, exProgram)
  }

  protected def filter(ctx: inox.Context, name: String): FilterStatus = Test

  def testAll(dir: String)(block: (component.Analysis, inox.Reporter) => Unit): Unit = {
    val fs = resourceFiles(dir, _.endsWith(".scala")).toList

    // Toggle this variable if you need to debug one specific test.
    // You might also want to run `it:testOnly *<some test suite>* -- -z "<some test filter>"`.
    val DEBUG = false

    if (DEBUG) {

      for {
        file <- fs
        path = file.getPath
        name = file.getName dropRight ".scala".length
      } test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx =>
        val (uName, funs, program) = extractOne(path, ctx)
        assert(uName == name)
        val report = component.apply(funs, program, ctx)
        block(report, ctx.reporter)
      }

    } else {

      val ctx = inox.TestContext.empty
      val (funss, program) = extractAll(fs.map(_.getPath), ctx)
      for ((name, funs) <- funss) {
        test(s"$dir/$name", ctx => filter(ctx, s"$dir/$name")) { ctx =>
          val report = component.apply(funs, program, ctx)
          block(report, ctx.reporter)
        }
      }

    }
  }

}

