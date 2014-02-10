/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

class InductionTactic(reporter: Reporter) extends DefaultTactic(reporter) {
  override val description = "Induction tactic for suitable functions"
  override val shortDescription = "induction"

  private def firstAbsClassDef(args: Seq[VarDecl]) : Option[(AbstractClassType, VarDecl)] = {
    args.map(vd => (vd.getType, vd)).collect {
      case (act: AbstractClassType, vd) => (act, vd)
    }.headOption
  } 

  private def selectorsOfParentType(parentType: ClassType, cct: CaseClassType, expr: Expr) : Seq[Expr] = {
    val childrenOfSameType = cct.fields.filter(_.tpe == parentType)
    for (field <- childrenOfSameType) yield {
      CaseClassSelector(cct, expr, field.id)
    }
  }

  override def generatePostconditions(funDef: FunDef) : Seq[VerificationCondition] = {
    assert(funDef.body.isDefined)
    firstAbsClassDef(funDef.args) match {
      case Some((cct, arg)) =>
        val prec = funDef.precondition
        val optPost = funDef.postcondition
        val body = matchToIfThenElse(funDef.body.get)
        val argAsVar = arg.toVariable
        val parentType = cct

        optPost match {
          case None =>
            Seq.empty
          case Some((pid, post)) =>
            for (cct <- parentType.knownCCDescendents) yield {
              val selectors = selectorsOfParentType(parentType, cct, argAsVar)
                // if no subtrees of parent type, assert property for base case
              val resFresh = FreshIdentifier("result", true).setType(body.getType)
              val bodyAndPostForArg = Let(resFresh, body, replace(Map(Variable(pid) -> Variable(resFresh)), matchToIfThenElse(post)))
              val withPrec = if (prec.isEmpty) bodyAndPostForArg else Implies(matchToIfThenElse(prec.get), bodyAndPostForArg)

              val conditionForChild = 
                if (selectors.size == 0) 
                  withPrec
                else {
                  val inductiveHypothesis = (for (sel <- selectors) yield {
                    val resFresh = FreshIdentifier("result", true).setType(body.getType)
                    val bodyAndPost = Let(resFresh, replace(Map(argAsVar -> sel), body), replace(Map(Variable(pid) -> Variable(resFresh), argAsVar -> sel), matchToIfThenElse(post))) 
                    val withPrec = if (prec.isEmpty) bodyAndPost else Implies(replace(Map(argAsVar -> sel), matchToIfThenElse(prec.get)), bodyAndPost)
                    withPrec
                  })
                  Implies(And(inductiveHypothesis), withPrec)
                }
              new VerificationCondition(Implies(CaseClassInstanceOf(cct, argAsVar), conditionForChild), funDef, VCKind.Postcondition, this).setPos(funDef)
            }
        }

      case None =>
        reporter.warning("Could not find abstract class type argument to induct on")
        super.generatePostconditions(funDef)
    }
  }

  override def generatePreconditions(function: FunDef) : Seq[VerificationCondition] = {
    val defaultPrec = super.generatePreconditions(function)
    firstAbsClassDef(function.args) match {
      case Some((cct, arg)) => {
        val toRet = if(function.hasBody) {
          val parentType = cct
          val cleanBody = expandLets(matchToIfThenElse(function.body.get))

          val allPathConds = collectWithPathCondition((t => t match {
            case FunctionInvocation(tfd, _) if(tfd.hasPrecondition) => true
            case _ => false
          }), cleanBody)

          def withPrec(path: Seq[Expr], shouldHold: Expr) : Expr = if(function.hasPrecondition) {
            Not(And(And(matchToIfThenElse(function.precondition.get) +: path), Not(shouldHold)))
          } else {
            Not(And(And(path), Not(shouldHold)))
          }

          val conditionsForAllPaths : Seq[Seq[VerificationCondition]] = allPathConds.map(pc => {
            val path : Seq[Expr] = pc._1
            val fi = pc._2.asInstanceOf[FunctionInvocation]
            val FunctionInvocation(tfd, args) = fi

            for (cct <- parentType.knownCCDescendents) yield {
              val argAsVar = arg.toVariable
              val selectors = selectorsOfParentType(parentType, cct, argAsVar)
              
              val prec : Expr = freshenLocals(matchToIfThenElse(tfd.precondition.get))
              val newLetIDs = tfd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe))
              val substMap = Map[Expr,Expr]((tfd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
              val newBody : Expr = replace(substMap, prec)
              val newCall : Expr = (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e))

              val toProve = withPrec(path, newCall)

              val conditionForChild =
                if (selectors.isEmpty)
                  toProve
                else {
                  val inductiveHypothesis = (for (sel <- selectors) yield {
                    val prec : Expr = freshenLocals(matchToIfThenElse(tfd.precondition.get))
                    val newLetIDs = tfd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe))
                    val substMap = Map[Expr,Expr]((tfd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
                    val newBody : Expr = replace(substMap, prec)
                    val newCall : Expr = (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e))

                    val toReplace = withPrec(path, newCall)
                    replace(Map(argAsVar -> sel), toReplace)
                  })
                  Implies(And(inductiveHypothesis), toProve)
                }
              new VerificationCondition(Implies(CaseClassInstanceOf(cct, argAsVar), conditionForChild), function, VCKind.Precondition, this).setPos(fi)
            }
          }).toSeq

          conditionsForAllPaths.flatten
        } else {
          Seq.empty
        }
        toRet
      }
      case None => {
        reporter.warning("Induction tactic currently supports exactly one argument of abstract class type")
        defaultPrec
      }
    }
  }
}
