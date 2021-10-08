/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import java.util.concurrent.TimeUnit

import inox.solvers._
import stainless.verification.CoqStatus.Valid

import scala.concurrent.duration.Duration
import scala.concurrent.{Await, Future, TimeoutException}
import scala.util.{Failure, Success}

object DebugSectionCoq extends inox.DebugSection("coq")

trait CoqVerificationChecker { self =>
  val program: StainlessProgram
  val context: inox.Context

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  given givenDebugSection: DebugSectionCoq.type = DebugSectionCoq

  type VC = verification.VC[program.trees.type]
  def VC(condition: program.trees.Expr, fd: Identifier, kind: VCKind, satisfiability: Boolean): VC =
    verification.VC(program.trees)(condition, fd, kind, satisfiability)

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  def verify(funs: Seq[Identifier]) = {
    val pCoq = CoqEncoder.transformProgram(program, context)
    CoqIO.makeOutputDirectory()
    val files = CoqIO.writeToCoqFile(pCoq.map { case (id, name, com) => (name, com) } )
    val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None)
    val vcs: Seq[VC] = pCoq map { case(fun, _, _) =>
      VC(getFunction(fun).fullBody, fun, VCKind.CoqMethod, true).setPos(symbols.getFunction(fun))
    }
    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap

    val res: Map[VC, VCResult] = pCoq.zip(vcs).map {case(((fun, file, commands)), vc) => {
      val fName : String = CoqIO.makeFilename(file)
      CoqIO.writeToCoqFile(commands)
      val (time: Long, tryRes) = timers.verification.runAndGetTime {
        CoqIO.coqc(fName, context)

      }
      context.reporter.info(s"Total time: ${time / 1000.0}s")
      val vcres: VCStatus = tryRes match {
        case _ if interruptManager.isInterrupted => {
          interruptManager.reset()
          VCStatus.Cancelled
        }


        case Success(coqRes) => coqRes match {
          case CoqStatus.Unknown => VCStatus.Unknown
          case CoqStatus.Valid => VCStatus.Valid
          case CoqStatus.Timeout => VCStatus.Timeout
          case CoqStatus.Invalid => VCStatus.Invalid(null)
          case CoqStatus.Cancelled => VCStatus.Cancelled
          case CoqStatus.InternalError => VCStatus.Crashed
          case CoqStatus.ExternalBug => VCStatus.ExternalBug
        }

        case Failure(u: inox.Unsupported) =>
          reporter.warning(u.getMessage)
          VCStatus.Unsupported

        case Failure(e) => reporter.internalError(e)
      }

      vc -> VCResult(vcres, None, Some(time))
    }}.toMap


    Future(new VerificationAnalysis {
      override val program: self.program.type = self.program
      override val sources = Set[stainless.Identifier]()
      override val results = initMap ++ res
      override val context = self.context
    })
  }
}

object CoqVerificationChecker {
  def verify(funs: Seq[Identifier], p: StainlessProgram, ctx: inox.Context) = {
    object Checker extends CoqVerificationChecker {
      val program: p.type = p
      val context = ctx
    }
    Checker.verify(funs)
  }
}
