/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers._

object optFailEarly extends inox.FlagOptionDef("fail-early", false)
object optFailInvalid extends inox.FlagOptionDef("fail-invalid", false)
object optVCCache extends inox.FlagOptionDef("vc-cache", false)

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

  def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
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

  def checkVCs(vcs: Seq[VC], sf: SolverFactory { val program: self.program.type }, stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    var stop = false

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap

    val results = MainHelpers.par(vcs) flatMap { vc =>
      if (stop) None else {
        val res = checkVC(vc, sf)
        if (interruptManager.isInterrupted) interruptManager.reset()
        stop = stopWhen(res)
        Some(vc -> res)
      }
    }

    initMap ++ results
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

      val timer = timers.verification.start()

      val vcres = try {
        s.assertCnstr(Not(cond))

        val res = s.check(Model)

        val time = timer.stop()

        res match {
          case _ if interruptManager.isInterrupted =>
            VCResult(VCStatus.Cancelled, Some(s), Some(time))

          case Unknown =>
            VCResult(s match {
              case ts: inox.solvers.combinators.TimeoutSolver => ts.optTimeout match {
                case Some(t) if t < time => VCStatus.Timeout
                case _ => VCStatus.Unknown
              }
              case _ => VCStatus.Unknown
            }, Some(s), Some(time))

          case Unsat =>
            VCResult(VCStatus.Valid, s.getResultSolver, Some(time))

          case SatWithModel(model) =>
            VCResult(VCStatus.Invalid(model), s.getResultSolver, Some(time))
        }
      } catch {
        case u: Unsupported =>
          val time = if (timer.isRunning) timer.stop else timer.time
          reporter.warning(u.getMessage)
          VCResult(VCStatus.Unsupported, Some(s), Some(time))
      } finally {
        if (timer.isRunning) timer.stop()
      }

      reporter.synchronized {
        reporter.info(s" - Result for '${vc.kind}' VC for ${vc.fd} @${vc.getPos}:")

        vcres.status match {
          case VCStatus.Valid =>
            reporter.info(" => VALID")

          case VCStatus.Invalid(cex) =>
            reporter.warning(" => INVALID")
            reporter.warning("Found counter-example:")
            reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))

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
            (vcs: Seq[VC[p.trees.type]]): Map[VC[p.trees.type], VCResult[p.Model]] = {
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
