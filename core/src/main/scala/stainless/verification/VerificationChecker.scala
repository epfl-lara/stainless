/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers._

object optParallelVCs extends inox.FlagOptionDef("parallelvcs", false)
object optFailEarly extends inox.FlagOptionDef("failearly", false)

object DebugSectionVerification extends inox.DebugSection("verification")

trait VerificationChecker { self =>
  val program: Program
  val options: inox.Options

  private lazy val parallelCheck = options.findOptionOrDefault(optParallelVCs)
  private lazy val failEarly = options.findOptionOrDefault(optFailEarly)

  import program._
  import program.trees._
  import program.symbols._
  import CallGraphOrderings._

  implicit val debugSection = DebugSectionVerification

  type VC = verification.VC[program.trees.type]
  val VC = verification.VC

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  protected def getTactic(fd: FunDef): Tactic { val program: self.program.type }
  protected def getFactory: SolverFactory {
    val program: self.program.type
    type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  private def defaultStop(res: VCResult): Boolean = if (failEarly) res.status != VCStatus.Valid else false

  def verify(funs: Seq[Identifier], stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    val sf = ctx.options.findOption(inox.optTimeout) match {
      case Some(to) => getFactory.withTimeout(to)
      case None => getFactory
    }

    try {
      ctx.reporter.debug("Generating Verification Conditions...")
      val vcs = generateVCs(funs)

      ctx.reporter.debug("Checking Verification Conditions...")
      checkVCs(vcs, sf, stopWhen)
    } finally {
      sf.shutdown()
    }
  }

  def generateVCs(funs: Seq[Identifier]): Seq[VC] = {
    val vcs: Seq[VC] = (for (id <- funs) yield {
      val fd = getFunction(id)
      val tactic = getTactic(fd)

      if (fd.body.isDefined) {
        tactic.generateVCs(id)
      } else {
        Nil
      }
    }).flatten

    vcs.sortBy(vc => (getFunction(vc.fd),
      if (vc.kind.underlying == VCKind.Precondition) 0
      else if (vc.kind.underlying == VCKind.Assert) 1
      else 2
    ))
  }

  private lazy val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None)

  def checkVCs(vcs: Seq[VC], sf: SolverFactory { val program: self.program.type }, stopWhen: VCResult => Boolean = defaultStop): Map[VC, VCResult] = {
    var stop = false

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap

    // scala doesn't seem to have a nice common super-type of vcs and vcs.par, so these
    // two quasi-identical pieces of code have to remain separate...
    val results = if (parallelCheck) {
      for (vc <- vcs.par if !stop && !ctx.interruptManager.isInterrupted) yield {
        val res = checkVC(vc, sf)
        if (ctx.interruptManager.isInterrupted) ctx.interruptManager.reset()
        stop = stopWhen(res)
        vc -> res
      }
    } else {
      for (vc <- vcs if !stop && !ctx.interruptManager.isInterrupted) yield {
        val res = checkVC(vc, sf)
        if (ctx.interruptManager.isInterrupted) ctx.interruptManager.reset()
        stop = stopWhen(res)
        vc -> res
      }
    }

    initMap ++ results
  }

  private def checkVC(vc: VC, sf: SolverFactory { val program: self.program.type }): VCResult = {
    import SolverResponses._
    val s = sf.getNewSolver

    try {
      val cond = simplifyLets(vc.condition)
      ctx.reporter.synchronized {
        ctx.reporter.info(s" - Now considering '${vc.kind}' VC for ${vc.fd} @${vc.getPos}...")
        ctx.reporter.debug(cond.asString)
        ctx.reporter.debug("Solving with: " + s.name)
      }

      val timer = ctx.timers.verification.start()

      val vcres = try {
        s.assertCnstr(Not(cond))

        val res = s.check(Model)

        val time = timer.stop()

        res match {
          case _ if ctx.interruptManager.isInterrupted =>
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
          val t = timer.selfTimer.get
          val time = if (t.isRunning) t.stop else t.runs.last
          ctx.reporter.warning(u.getMessage)
          VCResult(VCStatus.Unsupported, Some(s), Some(time))
      }

      val time = timer.stop()

      ctx.reporter.synchronized {
        if (parallelCheck)
          ctx.reporter.info(s" - Result for '${vc.kind}' VC for ${vc.fd} @${vc.getPos}:")

        vcres.status match {
          case VCStatus.Valid =>
            ctx.reporter.info(" => VALID")

          case VCStatus.Invalid(cex) =>
            ctx.reporter.warning(" => INVALID")
            ctx.reporter.warning("Found counter-example:")
            ctx.reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))

          case status =>
            ctx.reporter.warning(" => " + status.name.toUpperCase)
        }
      }

      vcres
    } finally {
      s.free()
    }
  }
}

object VerificationChecker {
  def verify(p: StainlessProgram, opts: inox.Options)
            (funs: Seq[Identifier]): Map[VC[p.trees.type], VCResult[p.Model]] = {
    object checker extends VerificationChecker {
      val program: p.type = p
      val options = opts

      val defaultTactic = DefaultTactic(p)
      val inductionTactic = InductionTactic(p)

      protected def getTactic(fd: p.trees.FunDef) =
        if (fd.flags contains "induct") {
          inductionTactic
        } else {
          defaultTactic
        }

      protected def getFactory = solvers.SolverFactory.apply(p, opts)
    }

    checker.verify(funs)
  }

  def verify(p: StainlessProgram)(funs: Seq[Identifier]): Map[VC[p.trees.type], VCResult[p.Model]] = {
    verify(p, p.ctx.options)(funs)
  }
}
