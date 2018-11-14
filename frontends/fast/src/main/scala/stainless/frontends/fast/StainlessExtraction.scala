package stainless.frontends.fast

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._
import inox.ast.FreshIdentifier
import stainless.frontend.CallBack
import stainless.frontends.dotc.{CodeExtraction, SymbolsContext}
import stainless.extraction.xlang.{trees => xt}
import stainless.frontends.fast.extraction.DottyToInoxIR


class StainlessExtraction(inoxCtx: inox.Context, callback: CallBack, cache: SymbolsContext) extends Phase {

  def phaseName: String = "stainless extraction"

  def run(implicit ctx: Context): Unit = {
    // probably the stupidest
    val dottyToInoxIR = new IRs {}.asInstanceOf[DottyToInoxIR]

    import dottyToInoxIR.{extractRef, extractStatic, outOfSubsetError}

    val unit = ctx.compilationUnit
    val tree = unit.untpdTree
    val (id, stats) = tree match {
      case pd @ PackageDef(refTree, lst) =>
        val id = lst.collectFirst { case PackageDef(ref, stats) => ref } match {
          case Some(ref) => extractRef(ref)(inoxCtx, cache, ctx)
          case None => FreshIdentifier(unit.source.file.name.replaceFirst("[.][^.]+$", ""))
        }
        (id, pd.stats)
      case _ => outOfSubsetError(tree, "Unexpected unit body")
    }



    val extracted = extractStatic(stats)(inoxCtx, cache, ctx)

//    val file = unit.source.file.absolute.path
//    val isLibrary = Main.libraryFiles contains file
//    val xtUnit = xt.UnitDef(id, Seq(), Seq(), Seq(), !isLibrary)
//
//    callback(file, xtUnit, Seq(), functions)
  }

}
