package stainless.frontends.fast

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._
import inox.ast.{FreshIdentifier, Trees}
import inox.parser.InterpolatorException
import stainless.extraction.xlang
import stainless.frontend.CallBack
import stainless.frontends.dotc.{CodeExtraction, SymbolsContext}
import stainless.extraction.xlang.{trees => xt}
import stainless.frontends.fast.extraction.DottyToInoxIR

import scala.language.reflectiveCalls


class StainlessExtraction(inoxCtx: inox.Context, callback: CallBack, cache: SymbolsContext) extends Phase {

  def phaseName: String = "stainless extraction"

  def run(implicit ctx: Context): Unit = {
    // probably the stupidest
    val dottyToInoxIR = new Elaborators {
      // currently using inox just to see what happens
      override val trees: Trees = xt

      def makeProgram(extracted: Seq[Either[ADTs.Sort, Functions.Function]]): Programs.Program = Programs.Program(extracted)

      def fullElaboration(program: Programs.Program): Seq[trees.Definition] = {
        ProgramE.elaborate(program)(createStore(trees.NoSymbols, Seq())).get match {
          case Left(err) =>
            throw InterpolatorException(err)
          case Right((evs, cs)) => solve(cs) match {
            case Left(err) => throw InterpolatorException(err)
            case Right(u) => evs.map(_.get(u))
          }
        }
      }

      def extractFunctions(definitions: Seq[trees.Definition]): Seq[trees.FunDef] =
        definitions.flatMap{
          case a: trees.FunDef => Some(a)
          case _ => None
        }
    }

    import dottyToInoxIR.{extractRef, extractStatic}

    val unit = ctx.compilationUnit
    val tree = unit.untpdTree
    val (id, stats) = tree match {
      case pd @ PackageDef(refTree, lst) =>
        val id = lst.collectFirst { case PackageDef(ref, stats) => ref } match {
          case Some(ref) => extractRef(ref)(inoxCtx, cache, ctx)
          case None => FreshIdentifier(unit.source.file.name.replaceFirst("[.][^.]+$", ""))
        }
        (id, pd.stats)
    }



    val extracted = extractStatic(stats)(inoxCtx, cache, ctx)

    val program = dottyToInoxIR.makeProgram(extracted)

    val result = dottyToInoxIR.fullElaboration(program)


    val functions = dottyToInoxIR.extractFunctions(result)
    val file = unit.source.file.absolute.path
    val isLibrary = Main.libraryFiles contains file
    val xtUnit = xt.UnitDef(id, Seq(), Seq(), Seq(), !isLibrary)

    val funs = functions.asInstanceOf[Seq[xt.FunDef]]

    callback(file, xtUnit, Seq(), funs)
  }

}
