package stainless

import stainless.verification.{VC, VCResult, VCStatus, VerificationAnalysis}

import java.io.File
import scala.sys.process.*

object Utils {
  enum Solver {
    case Z3
    case cvc5
    case Princess
  }
  object Solver {
    def fromInoxName(str: String): Option[Solver] = str match {
      case "smt-z3" => Some(Solver.Z3)
      case "smt-cvc5" => Some(Solver.cvc5)
      case "princess" => Some(Solver.Princess)
      case _ => None
    }
  }

  def prettyInvalidVCs[VA <: VerificationAnalysis](analysis: VA, indent: Int = 2): Seq[String] = {
    val program: analysis.program.type = analysis.program
    val trees: analysis.program.trees.type = program.trees
    val indentStr = " " * indent

    def pp(vc: VC[trees.type], vr: VCResult[program.Model]): Seq[String] = {
      val header = s"${indentStr}VC @ ${vc.getPos} in function ${vc.fid.name} of kind ${vc.kind.name} with status ${vr.status.name}"
      val ctex = vr.status match {
        case VCStatus.Invalid(VCStatus.CounterExample(ctex)) =>
          // The baseIndent in PrinterOptions does not seem to work as we expect.
          // We split the lines and reindent them ourselves
          val ctexStr = ctex.asString(using trees.PrinterOptions())
          s"${indentStr}Counterexample:" +: ctexStr.split("\n").toSeq.map(l => s"${indentStr * 2}$l")
        case VCStatus.Invalid(VCStatus.Unsatisfiable) => Seq(s"${indentStr * 2}(unsatisfiable)")
        case _ => Seq.empty
      }
      header +: ctex
    }

    val invalid = analysis.vrs.filter(_._2.isInvalid)
    val inconclusive = analysis.vrs.filter(_._2.isInconclusive)

    val invalidLines = {
      if (invalid.isEmpty) Seq.empty
      else {
        val header = "The following VCs are invalid:"
        val vcs = invalid.flatMap(pp)
        header +: vcs
      }
    }
    val inconclusiveLines = {
      if (inconclusive.isEmpty) Seq.empty
      else {
        val header = "The following VCs are inconclusive:"
        val vcs = inconclusive.flatMap(pp)
        header +: vcs
      }
    }

    invalidLines ++ inconclusiveLines
  }

  def runCommand(cmd: String): (List[String], Int) = {
    val std = scala.collection.mutable.ListBuffer[String]()
    val exitCode = cmd ! ProcessLogger(std append _)
    (std.toList, exitCode)
  }

  def runMainWithArgs(args: Array[String]): (inox.Context, Option[AbstractReport[?]]) = {
    val ctx = Main.setup(args).copy(reporter = new inox.TestSilentReporter())
    val compilerArgs = args.toList filterNot { _.startsWith("--") }
    val compiler = frontend.build(ctx, compilerArgs, stainless.Main.factory)
    ctx.reporter.info(s"Running: stainless ${args.mkString(" ")}")
    compiler.run()
    compiler.join()
    (ctx, compiler.getReport)
  }

  def getFolders(dir: String): Seq[String] = {
    Option(getClass.getResource(s"/$dir")).toSeq.flatMap { dirUrl =>
      val dirFile = new File(dirUrl.getPath)
      Option(dirFile.listFiles().toSeq).getOrElse(Seq.empty).filter(_.isDirectory)
        .map(_.getName)
    }.sorted
  }
}
