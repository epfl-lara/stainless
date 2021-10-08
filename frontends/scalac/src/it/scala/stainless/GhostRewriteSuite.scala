package stainless

import scala.tools.nsc.Global
import scala.tools.nsc.Settings
import scala.tools.nsc.reporters.StoreReporter
import scala.tools.nsc.reporters.ConsoleReporter

import org.scalatest.funspec.AnyFunSpec
import stainless.frontends.scalac.StainlessPlugin

class GhostRewriteSuite extends AnyFunSpec {
  val settings = new Settings()
  settings.stopAfter.value = List("refchecks")
  settings.usejavacp.value = false

  val reporter = new StoreReporter(settings)

  def newCompiler: CheckingGlobal = {
    new CheckingGlobal(settings)
  }

  class CheckingGlobal(settings: Settings) extends Global(settings, reporter) { glob =>

    private val ctx: inox.Context = stainless.TestContext.empty

    override def loadPlugins() = {
      class Impl(override val stainlessContext: inox.Context) extends StainlessPlugin(this)
      List(new Impl(ctx))
    }

    class GhostChecks extends Traverser {
      val ghostAnnotation = rootMirror.getRequiredClass("stainless.annotation.ghost")
      override def traverse(tree: Tree): Unit = {
        val sym = tree.symbol
        tree match {
          case Ident(_) if sym.hasAnnotation(ghostAnnotation) && !currentOwner.isSynthetic =>
            glob.reporter.error(tree.pos, s"Access to ghost symbol leftover after rewrite.")

          case Select(qual, _) if sym.hasAnnotation(ghostAnnotation) && !currentOwner.isSynthetic =>
            if (!currentOwner.isAccessor)
              glob.reporter.error(tree.pos, s"Access to ghost symbol leftover after rewrite.")
            super.traverse(tree)

          case Assign(Ident(_), rhs) =>
            traverse(rhs) // don't check assignments to locals

          case _ =>
            super.traverse(tree)
        }
      }
    }
  }

  def ignoreError(i: StoreReporter.Info) = {
    val s = i.toString

    s.contains("The Z3 native interface is not available") ||
    s.endsWith("VALID WARNING")
  }

  def compileFile(file: String) = {
    reporter.reset()
    val compiler = newCompiler

    val run = new compiler.Run()
    run.compile(Main.libraryFiles.toList :+ file)
    val unitToCheck = run.units.toList.last

    (new compiler.GhostChecks).traverse(unitToCheck.body)

    val errors = reporter.infos.filterNot(ignoreError)
    assert(errors.isEmpty, errors.mkString("\n\n"))
  }


  describe("Rewrite suite should remove all ghosts") {
    ignore("should not leave ghost code around in GhostMethods.scala") {
      compileFile("frontends/benchmarks/extraction/valid/GhostMethods.scala")
    }

    ignore("should not leave ghost code around in GhostCaseClass.scala") {
      compileFile("frontends/benchmarks/extraction/valid/GhostCaseClass.scala")
    }
  }

}
