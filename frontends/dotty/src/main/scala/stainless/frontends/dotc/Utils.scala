package stainless
package frontends.dotc

import dotty.tools.dotc
import dotc._
import core._
import Symbols._
import dotc.util._
import Contexts.{Context => DottyContext}
import ast.tpd
import Flags._
import transform._

object Utils {

  case class ExportedSymbolsMapping private(private val mapping: Map[Symbol, (Option[Symbol], Symbol)]) {
    def add(from: Symbol, recv: Option[Symbol], to: Symbol): ExportedSymbolsMapping = {
      val newMapping = mapping + (from -> (recv, to))
      ExportedSymbolsMapping(newMapping)
    }

    def get(sym: Symbol): Option[Seq[Symbol]] = {
      def loop(sym: Symbol, acc: Seq[Symbol]): Seq[Symbol] = {
        mapping.get(sym) match {
          case Some((recv, fwd)) =>
            val newPath = acc ++ recv.toSeq
            loop(fwd, newPath)
          case None => acc :+ sym
        }
      }

      if (mapping.contains(sym)) Some(loop(sym, Seq.empty))
      else None
    }
  }

  object ExportedSymbolsMapping {
    def empty: ExportedSymbolsMapping = ExportedSymbolsMapping(Map.empty)
  }

  def exportedSymbolsMapping(ctx: inox.Context, start: Int, units: List[CompilationUnit])(using dottyCtx: DottyContext): ExportedSymbolsMapping = {
    var mapping = ExportedSymbolsMapping.empty

    class Traverser(override val dottyCtx: DottyContext) extends tpd.TreeTraverser with ASTExtractors {
      import StructuralExtractors._
      import ExpressionExtractors._

      override def traverse(tree: tpd.Tree)(using DottyContext): Unit = {
        tree match {
          case ExFunctionDef(sym, _, _, _, ExCall(recv, fwd, _, _)) if sym is Exported =>
            mapping = mapping.add(sym, recv.map(_.symbol), fwd)
          case _ => traverseChildren(tree)
        }
      }
    }

    import dotty.tools.dotc.typer.ImportInfo.withRootImports
    for (unit <- units) {
      val newCtx = dottyCtx.fresh.setPhase(start).setCompilationUnit(unit).withRootImports
      val traverser = new Traverser(newCtx)
      traverser.traverse(unit.tpdTree)
    }
    mapping
  }
}
