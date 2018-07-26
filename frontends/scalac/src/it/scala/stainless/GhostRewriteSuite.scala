package stainless

import scala.tools.nsc.Global
import scala.tools.nsc.Settings
import scala.tools.nsc.reporters.StoreReporter
import scala.tools.nsc.reporters.ConsoleReporter

import org.scalatest._
import stainless.frontends.scalac.StainlessPlugin

class GhostRewriteSuite extends FunSpec {
  val reporter = new StoreReporter

  def newCompiler: CheckingGlobal = {
    val settings = new Settings()
    settings.stopAfter.value = List("refchecks")
    settings.usejavacp.value = false
    settings.classpath.value = Main.extraClasspath

    new CheckingGlobal(settings)
  }

  class CheckingGlobal(settings: Settings) extends Global(settings, reporter) {


    override def loadPlugins() = List(new StainlessPlugin(this))

    class GhostChecks extends Traverser {
      val ghostAnnotation = rootMirror.getRequiredClass("stainless.annotation.ghost")
      override def traverse(tree: Tree): Unit = {
        val sym = tree.symbol
        tree match {
          case Ident(_) if sym.hasAnnotation(ghostAnnotation) && !currentOwner.isSynthetic =>
            reporter.error(tree.pos, s"Access to ghost symbol leftover after rewrite.")

          case Select(qual, _) if sym.hasAnnotation(ghostAnnotation) && !currentOwner.isSynthetic =>
            if (!currentOwner.isAccessor)
              reporter.error(tree.pos, s"Access to ghost symbol leftover after rewrite.")
            super.traverse(tree)

          case Assign(Ident(_), rhs) =>
            traverse(rhs) // don't check assignments to locals

          case _ =>
            super.traverse(tree)
        }
      }
    }
  }


  def compileFile(file: String) = {
    reporter.reset()
    val compiler = newCompiler

    val run = new compiler.Run()
    run.compile(Main.libraryFiles.toList :+ file)
    val unitToCheck = run.units.toList.last

    (new compiler.GhostChecks).traverse(unitToCheck.body)

    assert(reporter.infos.isEmpty, reporter.infos.mkString("\n\n"))
  }


  describe("Rewrite suite should remove all ghosts") {
    it("should not leave ghost code around in ghost-methods.scala") {
      compileFile("frontends/benchmarks/extraction/valid/ghost-methods.scala")
    }

    it("should not leave ghost code around in ghost-caseclass.scala") {
      compileFile("frontends/benchmarks/extraction/valid/ghost-caseclass.scala")
    }
  }

}
