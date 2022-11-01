/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package testgen

import stainless.extraction.xlang
import xlang.{trees => xt}
import stainless.verification._

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import scala.concurrent.Future
import scala.util.matching.Regex

object ScalaTestGen {

  import stainless.trees._

  private val testCaseFnRegex: Regex = """\s*def testCase(\d+): Unit = (.+)""".r
  private val importsRegex: Regex = """import ((?<path>\w+\.)*)(?<iden>(\w+)|\{((?<idens>\w+\s*,\s*)*\w+)\})""".r

  def generateTestCases(origSyms: xt.Symbols)
                       (p: inox.Program {val trees: stainless.trees.type})
                       (res: Map[VC[p.trees.type], VCResult[p.Model]])
                       (using ctx: inox.Context): Unit = {
    val counterExs = res.toSeq.collect {
      case (vc, VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), _, _)) => (vc, model)
    }
    if (counterExs.isEmpty) {
      return
    }

    given XLangTestGen.TyParamSubst = XLangTestGen.TyParamSubst(IntegerType(), x => Some(IntegerLiteral(x)))

    val output = ctx.options.findOptionOrDefault(testgen.optOutputFile)
    val existingContent = readExistingContent(output)

    val testCaseNbrOffset = existingContent.map(_.lastTextNbr).getOrElse(0) + 1
    val xtTestCases = counterExs.zipWithIndex.flatMap {
      case ((vc, model), i) =>
        given XLangTestGen.TestCaseCtx = XLangTestGen.TestCaseCtx(origSyms, p, vc)(model)
        XLangTestGen.generateTestCase(i + testCaseNbrOffset).map((_, fd) => (fd.id.name, fd.body.get))
    }

    val existingTests = existingContent.toSet.flatMap(_.testBodies)

    val printer = new CustomPrinter
    val testCases = xtTestCases.flatMap { case (name, funBody) =>
      val pctx = xt.PrinterContext(funBody, Nil, xt.PrinterOptions().baseIndent, xt.PrinterOptions())
      printer.pp(funBody)(using pctx)
      val bodyStr = pctx.sb.toString
      if (existingTests.contains(bodyStr)) None
      else Some(s"def $name: Unit = $bodyStr")
    }

    if (testCases.isEmpty) {
      return
    }

    val importsCollector = new ImportsCollector
    xtTestCases.foreach((_, funBody) => importsCollector.traverse(funBody))
    val currTestsImports = importsCollector.imports

    val fileContent = existingContent match {
      case Some(existingContent) =>
        val allImports = existingContent.imports ++ currTestsImports
        val lastBraceIx = existingContent.linesNoImports.zipWithIndex.reverse.find((l, _) => l.trim == "}").map(_._2)
        lastBraceIx.map { ix =>
          val (linesBefore, linesAfter) = existingContent.linesNoImports.splitAt(ix)
          s"""${allImports.pretty}
             |${linesBefore.mkString("\n")}
             |
             |${testCases.mkString("  ", "\n\n  ", "")}
             |${linesAfter.mkString("\n")}""".stripMargin
        }.getOrElse {
          // This should not happen. If it does, to not overwrite existing content,
          // we just append the test cases (wrapped in an object TestCases)
          s"""${existingContent.linesNoImports.mkString("\n")}
             |${withWrapper(allImports, testCases)}""".stripMargin
        }
      case None =>
        withWrapper(baseImports ++ currTestsImports, testCases)
    }

    val outputPath = output.getAbsoluteFile.toPath
    Files.createDirectories(outputPath.getParent)
    Files.write(outputPath, fileContent.getBytes(StandardCharsets.UTF_8))
  }

  private case class ExistingContent(lastTextNbr: Int,
                                     // The test case bodies, which are all on a single line
                                     testBodies: Set[String],
                                     imports: Imports,
                                     // The file content, except that we have filtered out the imports
                                     // (because we may need to add new imports)
                                     linesNoImports: IndexedSeq[String])

  private def readExistingContent(file: File): Option[ExistingContent] = {
    if (!file.exists()) {
      None
    } else {
      val existingContentSrc = scala.io.Source.fromFile(file)
      try {
        val lines = existingContentSrc.getLines().toIndexedSeq
        val (testNbrs, existingTestBodies) = lines.collect {
          case testCaseFnRegex(ix, body) => (ix.toInt, body)
        }.unzip
        val (existingImports, importsIxs) = parseExistingImports(lines)
        val linesNoImports = lines.zipWithIndex.filterNot((_, ix) => importsIxs(ix)).map(_._1)
        Some(ExistingContent(testNbrs.maxOption.getOrElse(0), existingTestBodies.toSet, existingImports, linesNoImports))
      } finally {
        existingContentSrc.close()
      }
    }
  }

  private def withWrapper(imports: Imports, tests: Seq[String]): String = {
    s"""${imports.pretty}
       |
       |object TestCases {
       |${tests.mkString("  ", "\n\n  ", "")}
       |}""".stripMargin
  }

  private def parseExistingImports(lines: Seq[String]): (Imports, Set[Int]) = {
    val (importss, ixs) = lines.zipWithIndex
      .flatMap { case (line, ix) =>
        importsRegex.findFirstMatchIn(line).flatMap { mtch =>
          val prefixPath = Option(mtch.group("path")).toSeq
            .flatMap(p => p.dropRight(1).split("\\."))
          val iden = Option(mtch.group("iden"))
          val idens = Option(mtch.group("idens"))
          (iden, idens) match {
            case (Some(iden), None) =>
              // Single identifier import (possibly with a prefix path) such as `import Foo` or `import aa.bb.Foo`
              Some(Imports(Map(Path(prefixPath) -> Set(iden))) -> ix)
            case (None, Some(idensStr)) if prefixPath.nonEmpty =>
              // Multiple identifier imports with a prefix path such as `import aa.bb.{Foo, Qux, cc}`
              val idens = idensStr.split(",").map(_.trim).toSet
              Some(Imports(Map(Path(prefixPath) -> idens)) -> ix)
            case _ => None // Should not happen, if it does, silently ignore
          }
        }
      }.unzip
    val imports = importss.foldLeft(Imports(Map.empty))(_ ++ _)
    (imports, ixs.toSet)
  }

  private val baseImports = Imports(Map(
    Path(Seq("stainless")) -> Set("_"),
    Path(Seq("stainless", "lang")) -> Set("_"),
    Path(Seq("stainless", "collection")) -> Set("_"),
    Path(Seq("stainless", "math")) -> Set("_"),
    Path(Seq("stainless", "math", "BitVectors")) -> Set("_"),
  ))

  private case class Path(parts: Seq[String])

  private case class Imports(imports: Map[Path, Set[String]]) {
    def ++(other: Imports): Imports = {
      Imports((imports.keySet ++ other.imports.keySet).foldLeft(Map.empty) {
        case (acc, path) =>
          val idens0 = imports.getOrElse(path, Set.empty) ++ other.imports.getOrElse(path, Set.empty)
          val idens = if (idens0.contains("_")) Set("_") else idens0
          acc + (path -> idens)
      })
    }

    def pretty: String = {
      val (withoutPrefix, withPrefix) = imports.toSeq.partition(_._1.parts.isEmpty)
      val withoutPrefixPretty = withoutPrefix.flatMap(_._2).sorted
      val withPrefixPretty = withPrefix
        .sortBy { case (path, _) => (if (path.parts.head.contains("stainless")) 0 else 1, path.parts.size, path.parts.mkString(".")) }
        .map {
          case (path, idens) =>
            val pathsStr = path.parts.mkString(".")
            idens.toSeq match {
              case Seq() => pathsStr
              case Seq(iden) => s"${pathsStr}.$iden"
              case idens => s"${pathsStr}.{${idens.mkString(", ")}}"
            }
        }

      (withPrefixPretty ++ withoutPrefixPretty).mkString("import ", "\nimport ", "")
    }
  }

  private class ImportsCollector extends xt.ConcreteOOSelfTreeTraverser {
    var imports: Imports = Imports(Map.empty)

    override def traverse(id: Identifier): Unit = id match {
      case sid: SymbolIdentifier =>
        assert(sid.symbol.path.nonEmpty)
        imports ++= Imports(Map(Path(sid.symbol.path.init) -> Set(sid.symbol.path.last)))
      case _ => ()
    }
  }

  private class CustomPrinter(override val trees: xt.type) extends xlang.Printer {
    def this() = this(xt)

    override def ppBody(tree: xt.Tree)(using xt.PrinterContext): Unit = tree match {
      case bv: xt.BVLiteral =>
        val bigInt = bv.toBigInt
        val bigIntStr = bigInt.toString
        val litStr =
          if (Int.MinValue <= bigInt && bigInt <= Int.MaxValue) bigIntStr
          else if (Long.MinValue <= bigInt && bigInt <= Long.MaxValue) s"${bigIntStr}L"
          else s"""BigInt("$bigIntStr")"""

        if (bv.signed && bv.size == 8) p"$litStr.toByte"
        else if (bv.signed && bv.size == 16) p"$litStr.toShort"
        else if (bv.signed && bv.size == 32) p"$litStr"
        else if (bv.signed && bv.size == 64) p"${litStr}L"
        else {
          val bvTypeStr = s"""${if (bv.signed) "I" else "U"}Int${bv.size}"""
          p"$litStr: $bvTypeStr"
        }
      case _ => super.ppBody(tree)
    }
  }
}