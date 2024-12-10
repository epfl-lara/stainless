/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import scala.collection.mutable.{LinkedHashMap, ArrayBuffer}

import dotty.tools.io.AbstractFile
import dotty.tools.dotc._
import core.Names._
import core.Symbols._
import core.CompilationUnitInfo
import core.Contexts.{Context => DottyContext}
import transform._
import ast.tpd
import ast.Trees._
import typer._

import inox.DebugSection

import extraction.xlang.{trees => xt}
import frontend.{CallBack, Frontend, FrontendFactory, ThreadedFrontend, UnsupportedCodeException, DebugSectionFrontend}
import Utils._
import stainless.verification.CoqEncoder.m

case class ExtractedUnit(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef], typeDefs: Seq[xt.TypeDef])

class StainlessExtraction(val inoxCtx: inox.Context) {
  private val symbolMapping = new SymbolMapping

  def extractUnit(exportedSymsMapping: ExportedSymbolsMapping)(using ctx: DottyContext): Option[ExtractedUnit] = {
    val unit = ctx.compilationUnit
    val tree = unit.tpdTree
    extractUnit(tree, unit.source.file, exportedSymsMapping, isFromSource = true)
  }

  def extractUnit(
    tree: tpd.Tree,
    file: AbstractFile,
    exportedSymsMapping: ExportedSymbolsMapping,
    isFromSource: Boolean,
  )(using ctx: DottyContext): Option[ExtractedUnit] = {
    // Remark: the method `extractUnit` is called for each compilation unit (which corresponds more or less to a Scala file)
    // Therefore, the symbolMapping instances needs to be shared accross compilation unit.
    // Since `extractUnit` is called within the same thread, we do not need to synchronize accesses to symbolMapping.
    val extraction = new CodeExtraction(inoxCtx, symbolMapping, exportedSymsMapping)
    import extraction._

    val (id, stats) = tree match {
      case pd@PackageDef(pid, lst) =>
        val id = lst.collectFirst { case PackageDef(ref, _) => ref } match {
          case Some(ref) => extractRef(ref)
          case None => FreshIdentifier(file.name.replaceFirst("[.][^.]+$", ""))
        }
        (id, pd.stats)
      case _ =>
        inoxCtx.reporter.info("Empty package definition: " + file.name)
        (FreshIdentifier(file.name.replaceFirst("[.][^.]+$", "")), List.empty)
    }

    val fragmentChecker = new FragmentChecker(inoxCtx)
    fragmentChecker.ghostChecker(tree)
    fragmentChecker.checker(tree)

    if (!fragmentChecker.hasErrors()) tryExtractUnit(extraction, file, id, stats, isFromSource)
    else None
  }

  private def tryExtractUnit(extraction: CodeExtraction,
                             file: AbstractFile,
                             id: Identifier,
                             stats: List[tpd.Tree],
                             isFromSource: Boolean
  )(using DottyContext): Option[ExtractedUnit] = {
    // If the user annotates a function with @main, the compiler will generate a top-level class
    // with the same name as the function.
    // This generated class defines def main(args: Array[String]): Unit
    // that just wraps the annotated function in a try-catch.
    // The catch clause intercepts CommandLineParser.ParseError exceptions, causing recovery failure in
    // later Stainless phases so we simply drop that synthetic class.
    val filteredStats = findMain(stats)
      .map(name => stats.filter {
        case TypeDef(n, _) => name != n.toTermName
        case _ => true
      }).getOrElse(stats)
    try {
      val (imports, unitClasses, unitFunctions, _, subs, classes, functions, typeDefs) = extraction.extractStatic(filteredStats)
      assert(unitFunctions.isEmpty, "Packages shouldn't contain functions")
      val xtUnit = xt.UnitDef(id, imports, unitClasses, subs, isFromSource)
      Some(ExtractedUnit(file.absolute.path, xtUnit, classes, functions, typeDefs))
    } catch {
      case UnsupportedCodeException(pos, msg) =>
        inoxCtx.reporter.error(pos, msg)
        None
      case e => throw e
    }
  }

  private def findMain(stats: List[tpd.Tree])(using DottyContext): Option[TermName] = {
    val trAcc = new tpd.TreeAccumulator[Option[TermName]] {
      override def apply(found: Option[TermName], tree: tpd.Tree)(using DottyContext): Option[TermName] = {
        if (found.isDefined) found
        else tree match {
          case dd@DefDef(nme, _, _, _) if dd.symbol.denot.annotations.exists(_.symbol == defn.MainAnnot) =>
            Some(nme)
          case _ => foldOver(None, tree)
        }
      }
    }
    trAcc(None, stats)
  }

  /** Extract units defined in Tasty files.
    * 
    * This will only extract units that have not been extracted yet.
    * 
    * See [[SymbolMapping.popUsedTastyUnits]] for more information about how
    * these units are collected.
    * 
    * Side-effect: calls [[SymbolMapping.popUsedTastyUnits]].
    */
  def extractTastyUnits(exportedSymsMapping: ExportedSymbolsMapping, inoxCtx: inox.Context)(using DottyContext): Seq[ExtractedUnit] = {
    given DebugSection = DebugSectionFrontend

    def extractTastyUnit(tree: tpd.Tree, info: CompilationUnitInfo): Option[ExtractedUnit] = {
      val res = extractUnit(tree, info.associatedFile, exportedSymsMapping, isFromSource = false)
      res match {
        case Some(extracted) => inoxCtx.reporter.debug(s"- Extracted ${extracted.unit.id}.")
        case None => inoxCtx.reporter.debug(s"- Failed to extract Tasty unit from ${info.associatedFile.path}.")
      }
      res
    }

    // We avoid extracting Tasty units under `scala` because these are generally
    // not supported by Stainless, and because only a fragment of the Scala
    // standard library is available as Tasty files. Trying to extract units
    // from `scala` would therefore cause missing dependencies errors.  
    //
    // TODO(mbovel): However, this is not a general fix. A similar situation
    // could happen for non-library files: extracting the Tasty unit of a symbol
    // accessed only from within an `@exern` method could yield failures when
    // extracting the unit is not required in the first place. This is an edge
    // case to be addressed later, either by making sure that the body of
    // `@extern` methods is not visited at all, or by not registering used Tasty
    // units for symbols accessed only from within `@extern` methods.
    val unextractedPackages: Set[Symbol] = Set(defn.ScalaPackageClass)

    // Potential performance improvement: share the Map of extracted Tasty units
    // accross runs, so that we don't extract the same units multiple times in
    // watch mode. However that could also cause a memory leak if the map is
    // never cleared. To be investigated.
    val extractedTastyUnits = LinkedHashMap[tpd.Tree, Option[ExtractedUnit]]()

    var depth = 0

    while depth < 100 do
      inoxCtx.reporter.debug(f"Extracting Tasty units at depth $depth:")
      val newUnits =
        symbolMapping
          .popUsedTastyUnits()
          .filterNot((tree, _) => extractedTastyUnits.contains(tree))
          .filterNot((tree, _) => tree.symbol.ownersIterator.exists(unextractedPackages))
          .map((tree, info) => tree -> extractTastyUnit(tree, info))
      if newUnits.isEmpty then
        inoxCtx.reporter.debug(f"- No more units to extract.")
        return extractedTastyUnits.values.flatten.toSeq
      extractedTastyUnits ++= newUnits
      depth += 1

    // This should not be reached.
    inoxCtx.reporter.error("Reached maximum depth while extracting Tasty units. This is likely a bug in Stainless.")
    Nil
  }
}

