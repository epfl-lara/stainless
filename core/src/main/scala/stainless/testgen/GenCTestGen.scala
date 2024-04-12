package stainless
package testgen

import stainless.extraction.throwing.{trees => tt}
import stainless.extraction.xlang.{trees => xt}
import stainless.genc._
import stainless.genc.phases._
import stainless.verification._

import java.io.File
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, OpenOption, StandardOpenOption}

object GenCTestGen {
  import stainless.trees._

  def generateTestCases(origSyms: xt.Symbols)
                       (p: inox.Program {val trees: stainless.trees.type})
                       (res: Map[VC[p.trees.type], VCResult[p.Model]])
                       (using ctx: inox.Context): Unit = {
    val counterExs = res.toSeq.collect {
      case (vc, VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), _, _, _)) => (vc, model)
    }
    if (counterExs.isEmpty) {
      return
    }

    given XLangTestGen.TyParamSubst = XLangTestGen.TyParamSubst(
      BVType(true, 64),
      x =>
        if (Long.MinValue <= x && x <= Long.MaxValue) Some(BVLiteral(true, x, 64))
        else None)

    val output = {
      val pathStr = ctx.options.findOptionOrDefault(testgen.optOutputFile).getAbsolutePath
      new File(pathStr.replace(".scala", ".c"))
    }
    val existingContent = readExistingTestBodies(output)

    val testCaseNbrOffset = existingContent.map(_._1).getOrElse(0) + 1
    val xtTestCases = counterExs.zipWithIndex.flatMap {
      case ((vc, model), i) =>
        given XLangTestGen.TestCaseCtx = XLangTestGen.TestCaseCtx(origSyms, p, vc)(model)

        XLangTestGen.generateTestCase(i + testCaseNbrOffset).map {
          case (faultyFd0, testCase0) =>
            val faultyFd = faultyFd0.copy(flags = faultyFd0.flags :+ xt.Annotation("cCode.drop", Seq.empty))
            val testCase = testCase0.copy(flags = testCase0.flags :+ xt.Annotation("cCode.export", Seq.empty))
            (faultyFd, testCase)
        }
    }

    val testNames: Set[String] = xtTestCases.map(_._2.id.name).toSet
    val testCaseSyms = xt.NoSymbols
      .withFunctions(xtTestCases.map(_._1) ++ xtTestCases.map(_._2))
      .withClasses(origSyms.classes.values.toSeq)

    val symbolsAfterPipeline: tt.Symbols = GenCRun.pipelineBegin.extract(testCaseSyms)._1
    val cprog = GenerateC.pipeline(symbolsAfterPipeline).run(symbolsAfterPipeline)
    val fnTestCases = cprog.functions.filter(f => testNames.contains(f.id.name))
      .toSeq.sortBy(_.id.name.drop("testCase".length).toInt)

    existingContent match {
      case Some((_, existingBodies)) =>
        val fnBodyStrMap = fnTestCases.map { fn =>
          val str = fn.toString
          // Only take what's inside the function:
          //   void testCaseX(void) {  // drop
          //      ...                  // trimmed
          //   }                       // drop
          val bodyStr = str.split("\n").init.tail.map(_.trim)
          StrTestBody(bodyStr.toSeq) -> str
        }
        val toBeAppended = fnBodyStrMap.filter((strTestBody, _) => !existingBodies.contains(strTestBody)).map(_._2)
        if (toBeAppended.nonEmpty) {
          Files.write(output.toPath, ("\n\n" ++ toBeAppended.mkString("\n\n")).getBytes(StandardCharsets.UTF_8), StandardOpenOption.APPEND)
        }

      case None =>
        val includes = ctx.options.findOptionOrDefault(testgen.optGenCIncludes)
          .map(hd => s"""#include "$hd"""")
          .mkString("\n")
        val content =
          s"""$includes
              |
              |${fnTestCases.mkString("\n\n")}""".stripMargin
        Files.createDirectories(output.toPath.getParent)
        Files.write(output.toPath, content.getBytes(StandardCharsets.UTF_8))
    }
  }

  ////////////////////////////////////////////////

  private case class StrTestBody(trimmedLines: Seq[String])

  private val testCaseFnRegex = """\s*(?>STAINLESS_FUNC_PURE )?void testCase(\d+)\(void\) \{""".r

  private def readExistingTestBodies(file: File): Option[(Int, Set[StrTestBody])] = {
    def fnBodyContent(lines: IndexedSeq[String], fnStartIx: Int): Option[StrTestBody] = {
      def go(bracesCnt: Int, lineIx: Int): Option[StrTestBody] = {
        if (lineIx >= lines.length) {
          // Either we do not know how to count, or the C function is ill-formed
          None
        } else {
          val currLine = lines(lineIx)
          val newCnt = currLine.foldLeft(bracesCnt) {
            case (acc, '{') => acc + 1
            case (acc, '}') => acc - 1
            case (acc, _) => acc
          }
          if (newCnt == 0) {
            // Note: we assume that the last '}' is on a line of its own so that we do not have to include the last line of the last '}'
            // We also do not include the "void testCaseX(void) {" (hence the start at fnStartIx + 1)
            Some(StrTestBody(lines.slice(fnStartIx + 1, lineIx).map(_.trim)))
          } else {
            go(newCnt, lineIx + 1)
          }
        }
      }

      go(1, fnStartIx + 1)
    }

    if (!file.exists()) {
      None
    } else {
      val existingContentSrc = scala.io.Source.fromFile(file)
      try {
        val lines = existingContentSrc.getLines().toIndexedSeq
        val fnLineIndices = lines.zipWithIndex.flatMap {
          case (testCaseFnRegex(testNbr), lineIx) => Some((testNbr.toInt, lineIx))
          case _ => None
        }

        if (fnLineIndices.isEmpty) {
          None
        } else {
          val lastTestNbr = fnLineIndices.maxBy(_._1)._1
          val existingBodies = fnLineIndices.flatMap((_, fnStartIx) => fnBodyContent(lines, fnStartIx)).toSet
          Some((lastTestNbr, existingBodies))
        }
      } finally {
        existingContentSrc.close()
      }
    }
  }
}
