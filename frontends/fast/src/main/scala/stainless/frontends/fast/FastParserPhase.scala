package stainless.frontends.fast

import dotty.tools.dotc.{CompilationUnit, ast}
import dotty.tools.dotc.ast.Trees.{Import, PackageDef, TypeDef}
import dotty.tools.dotc.ast.tpd
import dotty.tools.dotc.config.Config
import dotty.tools.dotc.config.Printers.{default, typr}
import dotty.tools.dotc.core.Contexts.Context
import dotty.tools.dotc.core.Phases.Phase
import dotty.tools.dotc.parsing.JavaParsers.JavaParser
import dotty.tools.dotc.parsing.Parsers.Parser
import dotty.tools.dotc.util.Stats.record

import scala.util.control.NonFatal

class FastParserPhase extends Phase {

  override def phaseName = "fast parser frontend"
  override def isTyper = false

  /** The contexts for compilation units that are parsed but not yet entered */
  private var remaining: List[Context] = Nil

  /** Does a source file ending with `<name>.scala` belong to a compilation unit
    *  that is parsed but not yet entered?
    */
  def stillToBeEntered(name: String): Boolean =
    remaining.exists(_.compilationUnit.toString.endsWith(name + ".scala"))

  def monitor(doing: String)(body: => Unit)(implicit ctx: Context): Unit =
    try body
    catch {
      case NonFatal(ex) =>
        ctx.echo(s"exception occurred while $doing ${ctx.compilationUnit}")
        throw ex
    }

  def parse(implicit ctx: Context): Unit = monitor("parsing") {
    val unit = ctx.compilationUnit
    unit.untpdTree =
      if (unit.isJava) new JavaParser(unit.source).parse()
      else new Parser(unit.source).parse()
    val printer = if (ctx.settings.Xprint.value.contains("parser")) default else typr
    printer.println("parsed:\n" + unit.untpdTree.show)
    if (Config.checkPositions)
      unit.untpdTree.checkPos(nonOverlapping = !unit.isJava && !ctx.reporter.hasErrors)
  }

  override def runOn(units: List[CompilationUnit])(implicit ctx: Context): List[CompilationUnit] = {
    val unitContexts = for (unit <- units) yield {
      ctx.inform(s"compiling ${unit.source}")
      ctx.fresh.setCompilationUnit(unit)
    }
    unitContexts foreach (parse(_))
    record("parsedTrees", ast.Trees.ntrees)
    unitContexts.map(_.compilationUnit)
  }

  override def run(implicit ctx: Context): Unit = {
    parse
  }
}
