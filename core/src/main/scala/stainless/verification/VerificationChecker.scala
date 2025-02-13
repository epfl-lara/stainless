/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import inox.Options
import inox.solvers.*
import stainless.transformers.LatticesSimplifier

import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger}
import scala.util.{Failure, Success}
import scala.concurrent.Future
import scala.collection.mutable

object optSilent extends inox.FlagOptionDef("silent-verification", false)
object optFailEarly extends inox.FlagOptionDef("fail-early", false)
object optFailInvalid extends inox.FlagOptionDef("fail-invalid", false)
object optVCCache extends inox.FlagOptionDef("vc-cache", true)
object optSimplifier extends inox.OptionDef[SimplifierKind] {
  override val name: String = "simplifier"

  def default: SimplifierKind = SimplifierKind.Vanilla

  def parser: inox.OptionParsers.OptionParser[SimplifierKind] = SimplifierKind.tryFromString

  def usageRhs: String = "vanilla|ocbsl|ol|bland"
}

object DebugSectionVerification extends inox.DebugSection("verification")
object DebugSectionFullVC extends inox.DebugSection("full-vc")

enum SimplifierKind {
  case Vanilla
  case OCBSL
  case OL
  case Bland
}
object SimplifierKind {
  def tryFromString(s: String): Option[SimplifierKind] = s.toLowerCase match {
    case "vanilla" => Some(Vanilla)
    case "ocbsl" => Some(OCBSL)
    case "ol" | "olympique lyonnais" => Some(OL)
    case "bland" | "unflavored" | "lattice-core" => Some(Bland)
    case _ => None
  }
  def toLatticeAlgo(self: OCBSL.type | OL.type | Bland.type): LatticesSimplifier.UnderlyingAlgo = self match {
    case OCBSL => LatticesSimplifier.UnderlyingAlgo.OCBSL
    case OL => LatticesSimplifier.UnderlyingAlgo.OL
    case Bland => LatticesSimplifier.UnderlyingAlgo.Bland
  }
}

trait VerificationChecker { self =>
  val program: Program
  val context: inox.Context
  val semantics: program.Semantics

  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  private lazy val failEarly = options.findOptionOrDefault(optFailEarly)
  private lazy val failInvalid = options.findOptionOrDefault(optFailInvalid)
  private lazy val checkModels = options.findOptionOrDefault(optCheckModels)

  given givenDebugSection: DebugSectionVerification.type = DebugSectionVerification
  private case object VCReportTag

  type VC = verification.VC[program.trees.type]
  val VC = verification.VC

  type VCStatus = verification.VCStatus[program.Model]

  type VCResult = verification.VCResult[program.Model]
  val VCResult = verification.VCResult

  type TimeoutSolverFactory = SolverFactory {
    val program: self.program.type
    type S <: inox.solvers.combinators.TimeoutSolver { val program: self.program.type }
  }

  lazy val evaluator = semantics.getEvaluator(using context)

  protected def createFactory(opts: Options): TimeoutSolverFactory

  protected val factoryCache: mutable.Map[Options, TimeoutSolverFactory] = mutable.Map()
  protected def getFactory(opts: inox.Options = options): TimeoutSolverFactory = {
    factoryCache.getOrElse(opts, {
      val res = opts.findOption(inox.optTimeout) match {
        case Some(to) => createFactory(opts).withTimeout(to)
        case None => createFactory(opts)
      }
      factoryCache(opts) = res
      res
    })
  }

  /** @see [[checkAdtInvariantModel]] */
  protected def getFactoryForVC(vc: VC): TimeoutSolverFactory = vc.kind match {
    case _: VCKind.AdtInvariant => getFactory(options + optCheckModels(false))
    case _ => getFactory()
  }

  protected def defaultStop(res: VCResult): Boolean = {
    if (failEarly) !res.isValid
    else if (failInvalid) res.isInvalid
    else false
  }

  def verify(vcs: Seq[VC], stopWhen: VCResult => Boolean = defaultStop): Future[Map[VC, VCResult]] = {
    try {
      checkVCs(vcs, stopWhen)
    } finally {
      factoryCache.values.foreach(_.shutdown())
      factoryCache.clear()
    }
  }

  private lazy val unknownResult: VCResult = VCResult(VCStatus.Unknown, None, None, None)

  def checkVCs(vcs: Seq[VC], stopWhen: VCResult => Boolean = defaultStop): Future[Map[VC, VCResult]] = {
    if (!VerificationChecker.startedVerification.getAndSet(true)) reporter.info("Starting verification...")

    @volatile var stop = false

    VerificationChecker.total.addAndGet(vcs.length)
    infoReportVCProgress(VerificationChecker.verified.get(), VerificationChecker.total.get())

    val initMap: Map[VC, VCResult] = vcs.map(vc => vc -> unknownResult).toMap

    import MainHelpers._
    import SimplifierKind._

    val simplifyVC: Expr => Expr = {
      context.options.findOptionOrDefault(optSimplifier) match {
        case lat@(OCBSL | OL | Bland) =>
          // Note: the class instance is outside of the closure scope to avoid repeated creation instances
          // (so that computation can be preserved across VCs)
          val latticeSimp = LatticesSimplifier(trees, symbols, PurityOptions.assumeChecked, toLatticeAlgo(lat))
          (e: Expr) => latticeSimp.simplify(simplifyLets(removeAssertionsAndGhostAnnotations(e)))
        case Vanilla =>
          (e: Expr) => simplifyExpr(simplifyLets(removeAssertionsAndGhostAnnotations(e)))(using PurityOptions.assumeChecked)
      }
    }

    def processVC(vc: VC): Option[(VC, VCResult)] = {
      if (stop) None else {
        val simplifiedCondition = simplifyVC(vc.condition)

        // For some reasons, the synthesized copy method lacks default parameters...
        val simplifiedVC = (vc.copy()(condition = simplifiedCondition, fid = vc.fid, kind = vc.kind, satisfiability = vc.satisfiability): VC).setPos(vc)

        val sf = getFactoryForVC(vc)
        val res = checkVC(simplifiedVC, vc, sf)

        val shouldStop = stopWhen(res)
        val verif =
          if (res.isValid) VerificationChecker.verified.incrementAndGet()
          else VerificationChecker.verified.get()
        infoReportVCProgress(verif, VerificationChecker.total.get())

        interruptManager.synchronized { // Make sure that we only interrupt the manager once.
          if (shouldStop && !stop && !interruptManager.isInterrupted) {
            stop = true
            interruptManager.interrupt()
          }
        }

        if (interruptManager.isInterrupted) {
          interruptManager.reset()
        }

        Some(vc -> res)
      }
    }

    val results = Future.traverse(vcs) { vc =>
      // Note that `successful(e)` is eager and gets immediately evaluated whereas Future(e) is a scheduled task.
      // If parallelism is not explicitly enabled, we fallback to eager evaluation
      // (even on a thread pool of a single thread, it seems that the VCs won't necessarily be sequentially processed).
      if (nParallel.exists(_ > 1)) Future(processVC(vc))
      else Future.successful(processVC(vc))
    }.map(_.flatten)

    results.map(initMap ++ _)
  }

  /** Check whether the model for the ADT invariant specified by the given (invalid) VC is
   *  valid, ie. whether evalutating the invariant with the given model actually returns `false`.
   *
   *  One needs to be careful, because simply evaluating the invariant over the model
   *  returned by Inox fails with a 'class invariant' violation. While this is expected,
   *  we cannot know whether it was the invariant that we are interested in at this point
   *  or some other invariant that failed.
   *
   *  Instead, we need to put the constructed ADT value in the model when evaluating the
   *  condition, in order for the evaluator to not attempt to re-construct it.
   *
   *  As such, we instead need to:
   *  - evaluate the ADT's arguments to figure out whether those are valid.
   *  - rebuild the ADT over its evaluated arguments, and add it to the model under a fresh name.
   *  - rewrite the invariant's invocation to be applied to this new variable instead.
   *  - evaluate the resulting condition under the new model.
   */
  protected def checkAdtInvariantModel(vc: VC, invId: Identifier, model: Model): VCStatus = {
    import inox.evaluators.EvaluationResults._

    val Seq((inv, adt, path)) = collectWithPC(vc.condition) {
      case (inv @ FunctionInvocation(`invId`, _, Seq(adt: ADT)), path) => (inv, adt, path)
    }

    def success: VCStatus = {
      reporter.debug("- Model validated.")
      VCStatus.Invalid(VCStatus.CounterExample(model))
    }

    def failure(reason: String): VCStatus = {
      reporter.warning(reason)
      VCStatus.Unknown
    }

    evaluator.eval(path.toClause, model) match {
      case Successful(BooleanLiteral(true)) => // path condition was true, we must evaluate invariant
      case Successful(BooleanLiteral(false)) => return success
      case Successful(e) => return failure(s"- ADT inv. path condition unexpectedly evaluates to: ${e.asString}")
      case RuntimeError(msg) => return failure(s"- ADT inv. path condition leads to runtime error: $msg")
      case EvaluatorError(msg) => return failure(s"- ADT inv. path condition leads to evaluator error: $msg")
    }

    val evaledArgs = adt.args.map { arg =>
      val wrapped = path.bindings.foldRight(arg) { case ((vd, e), b) => let(vd, e, b) }
      evaluator.eval(wrapped, model)
    }

    val (newArgs, errs) = evaledArgs.partitionMap {
      case Successful(e) => Left(e)
      case RuntimeError(msg) => Right(failure(s"- ADT inv. argument leads to runtime error: $msg"))
      case EvaluatorError(msg) => Right(failure(s"- ADT inv. argument leads to evaluator error: $msg"))
    }
    if (errs.nonEmpty) errs.head
    else {
      val newAdt = ADT(adt.id, adt.tps, newArgs)
      val adtVar = Variable(FreshIdentifier("adt"), adt.getType(using symbols), Seq())
      val newInv = FunctionInvocation(invId, inv.tps, Seq(adtVar))
      val newModel = inox.Model(program)(model.vars + (adtVar.toVal -> newAdt), model.chooses)
      val newCondition = exprOps.replace(Map(inv -> newInv), vc.condition)

      evaluator.eval(newCondition, newModel) match {
        case Successful(BooleanLiteral(false)) => success
        case Successful(_) => failure("- Invalid model.")
        case RuntimeError(msg) => failure(s"- Model leads to runtime error: $msg")
        case EvaluatorError(msg) => failure(s"- Model leads to evaluation error: $msg")
      }
    }
  }

  private def removeAssertionsAndGhostAnnotations(expr: Expr): Expr = {
    exprOps.postMap {
      case Assert(_, _, e) => Some(e)
      case Annotated(e, flags0) =>
        val flags = flags0.filter(f => f != DropVCs && f != DropConjunct && f != Ghost)
        if (flags.isEmpty) Some(e)
        else Some(Annotated(e, flags).copiedFrom(expr))
      case _ => None
    }(expr)
  }

  protected def prettify(expr: Expr): Expr = {
    def rec(expr: Expr): Expr = expr match {
      case Annotated(e, Seq(DropVCs)) => rec(e)
      case Annotated(e, Seq(DropConjunct)) => rec(e)
      case Operator(es, recons) => recons(es map rec)
    }

    rec(expr)
  }

  protected def checkVC(vc: VC, origVC: VC, sf: SolverFactory { val program: self.program.type }): VCResult = {
    import SolverResponses._
    val cond = vc.condition
    if (cond == BooleanLiteral(true)) {
      if(vc.kind.isInstanceOf[VCKind.SATPrecondCheck.type]) {
        // an UNSAT VC here means that the precondition is UNSAT so we return Invalid
        return VCResult(VCStatus.Invalid(VCStatus.Unsatisfiable), None, None, None)
      }
      return VCResult(VCStatus.Trivial, None, None, None)
    }

    val s = sf.getNewSolver()
    try {
      reporter.synchronized {
        reporter.debug(s" - Now solving '${vc.kind}' VC for ${vc.fid.asString} @${vc.getPos}...")
        debugVC(vc, origVC)
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
          VCResult(VCStatus.Cancelled, Some(s.name), Some(time), s.getSmtLibFileId)

        case Success(res) => res match {
          case Unknown =>
            VCResult(s match {
              case ts: inox.solvers.combinators.TimeoutSolver => ts.optTimeout match {
                case Some(t) if t < time => VCStatus.Timeout
                case _ => VCStatus.Unknown
              }
              case _ => VCStatus.Unknown
            }, Some(s.name), Some(time), s.getSmtLibFileId)

          case Unsat if vc.kind.isInstanceOf[VCKind.SATPrecondCheck.type] =>
            VCResult(VCStatus.Invalid(VCStatus.Unsatisfiable), s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case Sat if vc.kind.isInstanceOf[VCKind.SATPrecondCheck.type] =>
            VCResult(VCStatus.Valid, s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case SatWithModel(_) if vc.kind.isInstanceOf[VCKind.SATPrecondCheck.type] =>
            VCResult(VCStatus.Valid, s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case Unsat if !vc.satisfiability =>
            VCResult(VCStatus.Valid, s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case SatWithModel(model) if checkModels && vc.kind.isInstanceOf[VCKind.AdtInvariant] =>
            val VCKind.AdtInvariant(invId) = vc.kind: @unchecked
            val status = checkAdtInvariantModel(vc, invId, model)
            VCResult(status, s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case SatWithModel(model) if !vc.satisfiability =>
            VCResult(VCStatus.Invalid(VCStatus.CounterExample(model)), s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case Sat if vc.satisfiability =>
            VCResult(VCStatus.Valid, s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case Unsat if vc.satisfiability =>
            VCResult(VCStatus.Invalid(VCStatus.Unsatisfiable), s.getResultSolver.map(_.name), Some(time), s.getSmtLibFileId)

          case _ => sys.error(s"Unreachable: $res")
        }

        case Failure(u: inox.Unsupported) =>
          reporter.warning(u.getMessage)
          VCResult(VCStatus.Unsupported, Some(s.name), Some(time), s.getSmtLibFileId)

        case Failure(e @ NotWellFormedException(d, info)) =>
          reporter.error(d.getPos, e.getMessage)
          VCResult(VCStatus.Crashed, Some(s.name), Some(time), s.getSmtLibFileId)

        case Failure(e) => reporter.internalError(e)
      }

      val vcResultMsg = VCResultMessage(vc, vcres)
      reporter.debug(vcResultMsg)

      val silent = options.findOptionOrDefault(optSilent)
      if (!silent) {
        reporter.synchronized {
          val descr = s" - Result for '${vc.kind}' VC for ${vc.fid.asString} @${vc.getPos}:"
          vcres.status match {
            case VCStatus.Valid =>
              reporter.debug(descr)
              reporter.debug(" => VALID")

            case VCStatus.Invalid(reason) =>
              reporter.warning(descr)
              // avoid reprinting VC if --debug=verification is enabled
              if (!reporter.isDebugEnabled(using DebugSectionVerification))
                reporter.warning(prettify(vc.condition).asString)
              reporter.warning(vc.getPos, " => INVALID")
              reason match {
                case VCStatus.CounterExample(cex) =>
                  vc.kind match {
                    case VCKind.MeasureMissing =>
                      reporter.warning("Measure is missing, cannot check termination")
                    case _ =>
                      reporter.warning("Found counter-example:")
                      reporter.warning("  " + cex.asString.replaceAll("\n", "\n  "))
                  }

                case VCStatus.Unsatisfiable =>
                  reporter.warning("Property wasn't satisfiable")
              }

            case status =>
              reporter.warning(descr)
              // avoid reprinting VC if --debug=verification is enabled
              if (!reporter.isDebugEnabled(using DebugSectionVerification))
                reporter.warning(prettify(vc.condition).asString)
              reporter.warning(vc.getPos, " => " + status.name.toUpperCase)
          }
        }
      }

      vcres
    } finally {
      s.free()
    }
  }

  protected def infoReportVCProgress(curr: Int, total: Int): Unit = {
    if curr == 1 then
      reporter.emit(reporter.ProgressMessage(reporter.INFO, VCReportTag, s"Verifying: $total verification conditions:"))
    if !isCompactModeOn then
      reporter.emit(reporter.ProgressMessage(reporter.INFO, VCReportTag, s" Verified: $curr / $total"))
  }

  protected def debugVC(simplifiedVC: VC, origVC: VC)(using inox.DebugSection): Unit = {
    import stainless.utils.StringUtils.indent

    if (reporter.isDebugEnabled) {
      if (!reporter.isDebugEnabled(using DebugSectionFullVC)) {
        reporter.debug(prettify(simplifiedVC.condition).asString)
      } else {
        reporter.whenDebug(DebugSectionFullVC) { debug =>
          debug(s"")
          debug(s" - Original VC:")
          debug(indent(prettify(origVC.condition).asString, 3))
          debug(s"")
          debug(s" - Simplified VC:")
          debug(indent(prettify(simplifiedVC.condition).asString, 3))
          debug(s"")
        }
      }
    }
  }
}

object VerificationChecker {
  // number of verified VCs (incremented when a VC is verified)
  val verified: AtomicInteger = new AtomicInteger(0)
  // total number of VCs (we add to that counter when entering `checkVCs`)
  // this is cumulative across different subprograms (for `SplitCallBack`)
  val total: AtomicInteger = new AtomicInteger(0)

  // flag to remember whether we have shown "Starting verification" message to the user
  val startedVerification: AtomicBoolean = new AtomicBoolean(false)

  // reset the counters before each watch cycle
  def reset(): Unit = {
    verified.set(0)
    total.set(0)
    startedVerification.set(false)
  }

  def verify(p: StainlessProgram, ctx: inox.Context)
            (vcs: Seq[VC[p.trees.type]]): Future[Map[VC[p.trees.type], VCResult[p.Model]]] = {
    class Checker extends VerificationChecker {
      val program: p.type = p
      val context = ctx
      val semantics = program.getSemantics

      protected def createFactory(opts: Options) = solvers.SolverFactory(p, ctx.withOpts(opts.options*))
    }

    val checker = if (ctx.options.findOptionOrDefault(optVCCache)) {
      new Checker with VerificationCache
    } else {
      new Checker
    }

    checker.verify(vcs)
  }
}
