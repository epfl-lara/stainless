/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.Expressions._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Common._
import purescala.Types._
import purescala.TypeOps.instantiateType
import purescala.Extractors._
import invariant.util.PredicateUtil._
import leon.utils._

/**
 * This tactic applies only to non-recursive functions.
 * Inducts over the recursive calls of the first recursive procedure in the body of `funDef`
 */
class TraceInductionTactic(vctx: VerificationContext) extends Tactic(vctx) {
  val description: String = "A tactic that performs induction over the recursions of a function."

  val cg = vctx.program.callGraph
  val defaultTactic = new DefaultTactic(vctx)
  val deepInduct = true // a flag for enabling deep induction pattern discovery

  def generatePostconditions(function: FunDef): Seq[VC] = {
    assert(!cg.isRecursive(function) && function.body.isDefined)
    val inductFunname = function.extAnnotations("traceInduct") match {
      case Seq(Some(arg: String)) => Some(arg)
      case a => None
    }
    // print debug info
    if(inductFunname.isDefined)
      ctx.reporter.debug("Extracting induction pattern from: "+inductFunname.get)(DebugSectionVerification)

    // helper function
    def selfRecs(fd: FunDef): Set[FunctionInvocation] = {
      if(fd.body.isDefined){
        collect{
          case fi@FunctionInvocation(tfd, _) if tfd.fd == fd =>
            Set(fi)
          case _ => Set.empty[FunctionInvocation]
        }(fd.body.get)
      } else Set()
    }

    if (function.hasPostcondition) {
      // construct post(body)
      val prop = application(function.postcondition.get, Seq(function.body.get))
      val paramVars = function.paramIds.map(_.toVariable)
      // extract the first recursive call when scanning `prop` AST from left to right
      var funInv: Option[FunctionInvocation] = None
      preTraversal {
        case _ if funInv.isDefined =>
        // do nothing
        case fi @ FunctionInvocation(tfd, args) if cg.isRecursive(tfd.fd) // function is recursive
          =>
          val argCheck =
            if (deepInduct) {
              // here we do a much deeper check
              // collect all arguments that are not `paramVars`
              val rest = args.zipWithIndex.filterNot(p => paramVars.contains(p._1))
              // check if 'rest' is invariant in all recursive calls
              val calleeParams = tfd.fd.params.map(_.id.toVariable)
              val restInv = selfRecs(tfd.fd).forall {
                case FunctionInvocation(_, recArgs) =>
                  rest.forall { case (_, i) => calleeParams(i) == recArgs(i) }
              }
              val paramArgs = args.filter(paramVars.contains)
              paramArgs.toSet.size == paramArgs.size && // paramArgs are unique ?
                restInv
            } else {
              args.forall(paramVars.contains) && // all arguments are parameters
                args.toSet.size == args.size // all arguments are unique
            }
          if (argCheck) {
            if (inductFunname.isDefined) {
              if (inductFunname.get == tfd.fd.id.name)
                funInv = Some(fi)
            } else {
              funInv = Some(fi)
            }
          }
        case _ =>
      }(prop)
      funInv match {
        case None =>
          ctx.reporter.warning("Cannot discover induction pattern! Falling back to normal tactic.")
          defaultTactic.generatePostconditions(function)
        case Some(finv) =>
          // create a new function that realizes the tactic
          val tactFun = new FunDef(FreshIdentifier(function.id.name + "-VCTact"), function.tparams,
            function.params, BooleanType)
          tactFun.precondition = function.precondition
          // the body of tactFun is a conjunction of induction pattern of finv, and the property
          val callee = finv.tfd.fd
          val paramIndex = paramVars.zipWithIndex.toMap
          val framePositions = finv.args.zipWithIndex.collect { // note: the index here is w.r.t calleeArgs
            case (v: Variable, i) if paramVars.contains(v) => (v, i)
          }.toMap
          val footprint = paramVars.filterNot(framePositions.keySet.contains)
          val indexedFootprint = footprint.map { a => paramIndex(a) -> a }.toMap // index here is w.r.t params

          // the returned expression will have boolean value
          def inductPattern(e: Expr): Expr = {
            e match {
              case IfExpr(c, th, el) =>
                createAnd(Seq(inductPattern(c),
                    IfExpr(c, inductPattern(th), inductPattern(el))))

              case MatchExpr(scr, cases) =>
                val scrpat = inductPattern(scr)
                val casePats = cases.map{
                  case MatchCase(pat, optGuard, rhs) =>
                    val guardPat = optGuard.toSeq.map(inductPattern _)
                    (guardPat, MatchCase(pat, optGuard, inductPattern(rhs)))
                }
                val pats = scrpat +: casePats.flatMap(_._1) :+ MatchExpr(scr, casePats.map(_._2))
                createAnd(pats)

              case Let(i, v, b) =>
                createAnd(Seq(inductPattern(v), Let(i, v, inductPattern(b))))

              case FunctionInvocation(tfd, args) =>
                val argPattern = createAnd(args.map(inductPattern))
                if (tfd.fd == callee) { // self recursive call ?
                  // create a tactFun invocation to mimic the recursion pattern
                  val indexedArgs = framePositions.map {
                    case (f, i) => paramIndex(f) -> args(i)
                  }.toMap ++ indexedFootprint
                  val recArgs = (0 until indexedArgs.size).map(indexedArgs)
                  val recCall = FunctionInvocation(TypedFunDef(tactFun, tactFun.tparams.map(_.tp)), recArgs)
                  createAnd(Seq(argPattern, recCall))
                } else {
                  argPattern
                }

              case Operator(args, op) =>
                // conjoin all the expressions and return them
                createAnd(args.map(inductPattern))
            }
          }
          val argsMap = callee.params.map(_.id).zip(finv.args).toMap
          val tparamMap = callee.typeArgs.zip(finv.tfd.tps).toMap
          val inlinedBody = instantiateType(replaceFromIDs(argsMap, callee.body.get), tparamMap, Map())
          val inductScheme = inductPattern(inlinedBody)
          // add body, pre and post for the tactFun
          tactFun.body = Some(createAnd(Seq(inductScheme, prop)))
          tactFun.precondition = function.precondition
          // postcondition is `holds`
          val resid = FreshIdentifier("holds", BooleanType)
          tactFun.postcondition = Some(Lambda(Seq(ValDef(resid)), resid.toVariable))

          // print debug info if needed
          ctx.reporter.debug("Autogenerated tactic fun: "+tactFun)(DebugSectionVerification)

          // generate vcs using the tactfun
          (defaultTactic.generatePostconditions(tactFun) ++
            defaultTactic.generatePreconditions(tactFun) ++
            defaultTactic.generateCorrectnessConditions(tactFun)) map {
              // rename the VCs to a user-friendly name
              case VC(cond, _, vcinfo) =>
                VC(cond, function, VCKinds.Info(VCKinds.PostTactVC, vcinfo.toString))
            }
      }
    } else Seq()
  }

  def generatePreconditions(function: FunDef): Seq[VC] =
    defaultTactic.generatePreconditions(function)

  def generateCorrectnessConditions(function: FunDef): Seq[VC] =
    defaultTactic.generateCorrectnessConditions(function)
}
