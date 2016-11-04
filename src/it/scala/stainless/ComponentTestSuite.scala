/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

trait ComponentTestSuite extends inox.TestSuite {

  val component: SimpleComponent

  def extract(files: Seq[String]): (Seq[(String, Seq[Identifier])], Program { val trees: component.trees.type }) = {
    val reporter = new inox.TestSilentReporter

    val ctx = inox.Context(reporter, new inox.utils.InterruptManager(reporter))
    val (structure, program) = frontends.scalac.ScalaCompiler(ctx, Build.libraryFiles ++ files.toList)
    val exProgram = component.extract(program)

    (for (u <- structure if u.isMain) yield (u.id.name, u.allFunctions(program.symbols)), exProgram)
  }
}
