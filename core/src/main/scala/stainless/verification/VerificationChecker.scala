/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import inox.solvers._

import scala.util.{ Success, Failure }
import scala.concurrent.Future

object optFailEarly extends inox.FlagOptionDef("fail-early", false)
object optFailInvalid extends inox.FlagOptionDef("fail-invalid", false)
object optVCCache extends inox.FlagOptionDef("vc-cache", true)

object DebugSectionVerification extends inox.DebugSection("verification")

trait VerificationChecker { self =>
  val program: Program
  val context: inox.Context

  import context._
  import program._
  import program.trees._
  import program.symbols._

  private lazy val failEarly = options.findOptionOrDefault(optFailEarly)
  private lazy val failInvalid = options.findOptionOrDefault(optFailInvalid)

  implicit val debugSection = DebugSectionVerification

  type VC = verification.VC[program.trees.type]
  val VC = verification.VC

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  protected def getFactory: SolverFactory {
    val program: self.program.type
    type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  protected def defaultStop(res: VCResult): Boolean = {
    if (failEarly) !res.isValid
    else if (failInvalid) res.isInvalid
    else false
  }

  def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean = defaultStop): Future[Map[VC, VCResult]] = {
    val sf = options.findOption(inox.optTimeout) match {
      case Some(to) => getFactory.withTimeout(to)
      case None => getFactory
    }

    try {
      reporter.debug("Checking Verification Conditions...")
      checkVCs(vcs, sf, stopWhen)
    } finally {
      sf.shutdown()
    }
  }

  private lazy val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None)

  def checkVCs(vcs: Seq[VC],
               sf: SolverFactory { val program: self.program.type },
               stopWhen: VCResult => Boolean = defaultStop): Future[Map[VC, VCResult]] = {
    @volatile var stop = false

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap

    import MainHelpers._
    val results = Future.traverse(vcs)(vc => Future {
      if (stop) None else {
        val res = checkVC(vc, sf)

        val shouldStop = stopWhen(res)
        interruptManager.synchronized { // Make sure that we only interrupt the manager once.
          if (shouldStop && !stop && !interruptManager.isInterrupted) {
            stop = true
            interruptManager.interrupt()
          }
        }

        if (interruptManager.isInterrupted) interruptManager.reset()
        Some(vc -> res)
      }
    }).map(_.flatten)

    results.map(initMap ++ _)
  }

  protected def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }): VCResult = {
    import SolverResponses._
    val s = sf.getNewSolver

    try {
      val cond = simplifyLets(vc.condition)
      reporter.synchronized {
        reporter.info(s" - Now solving '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        reporter.debug(cond.asString)
        reporter.debug("Solving with: " + s.name)
      }

      val (time, tryRes) = timers.verification.runAndGetTime {
        if (vc.satisfiability) {
          s.assertCnstr(cond)
          s.check(Simple)
        } else {
          s.assertCnstr(Not(cond))
          s.check(Model)
        }
      }

      val vcres = tryRes match {
        case _ if interruptManager.isInterrupted =>
          VCResult(VCStatus.Cancelled, Some(s), Some(time))

        case Success(res) => res match {
          case Unknown =>
            VCResult(s match {
              case ts: inox.solvers.combinators.TimeoutSolver => ts.optTimeout match {
                case Some(t) if t < time => VCStatus.Timeout
                case _ => VCStatus.Unknown
              }
              case _ => VCStatus.Unknown
            }, Some(s), Some(time))

          case Unsat if !vc.satisfiability =>
            VCResult(VCStatus.Valid, s.getResultSolver, Some(time))

          case SatWithModel(model) if !vc.satisfiability =>
            VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s.getResultSolver, Some(time))

          case Sat if vc.satisfiability =>
            VCResult(VCStatus.Valid, s.getResultSolver, Some(time))

          case Unsat if vc.satisfiability =>
            VCResult(VCStatus.Invalid(VCStatus.Unsatisfiable), s.getResultSolver, Some(time))
        }

        case Failure(u: Unsupported) =>
          reporter.warning(u.getMessage)
          VCResult(VCStatus.Unsupported, Some(s), Some(time))

        case Failure(e) => reporter.internalError(e)
      }

      reporter.synchronized {
        reporter.info(s" - Result for '${vc.kind}' VC for ${vc.fd} @${vc.getPos}:")

        vcres.status match {
          case VCStatus.Valid =>
            reporter.info(" => VALID")

          case VCStatus.Invalid(reason) =>
            reporter.warning(" => INVALID")
            reason match {
              case VCStatus.CounterExample(cex) =>
                reporter.warning("Found counter-example:")
                reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))

              case VCStatus.Unsatisfiable =>
                reporter.warning("Property wasn't satisfiable")
            }

          case status =>
            reporter.warning(" => " + status.name.toUpperCase)
        }
      }

      vcres
    } finally {
      s.free()
    }
  }
}

object VerificationChecker {
  def verify(p: StainlessProgram, ctx: inox.Context)
            (vcs: Seq[VC[p.trees.type]]): Future[Map[VC[p.trees.type], VCResult[p.Model]]] = {
    class Checker extends VerificationChecker {
      val program: p.type = p
      val context = ctx

      protected def getFactory = solvers.SolverFactory(p, ctx)
    }

    val checker = if (ctx.options.findOptionOrDefault(optVCCache)) {
      new Checker with VerificationCache
    } else {
      new Checker
    }

    checker.verify(vcs)
  }
}
