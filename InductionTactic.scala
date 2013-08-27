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

  private def firstAbsClassDef(args: VarDecls) : Option[(AbstractClassDef, VarDecl)] = {
    val filtered = args.filter(arg =>
      arg.getType match {
        case AbstractClassType(_) => true
        case _ => false
      })
    if (filtered.size == 0) None else (filtered.head.getType match {
      case AbstractClassType(classDef) => Some((classDef, filtered.head))
      case _ => scala.sys.error("This should not happen.")
    })
  } 

  private def selectorsOfParentType(parentType: ClassType, ccd: CaseClassDef, expr: Expr) : Seq[Expr] = {
    val childrenOfSameType = ccd.fields.filter(field => field.getType == parentType)
    for (field <- childrenOfSameType) yield {
      CaseClassSelector(ccd, expr, field.id).setType(parentType)
    }
  }

  override def generatePostconditions(funDef: FunDef) : Seq[VerificationCondition] = {
    assert(funDef.body.isDefined)
    val defaultPost = super.generatePostconditions(funDef)
    firstAbsClassDef(funDef.args) match {
      case Some((classDef, arg)) =>
        val prec = funDef.precondition
        val optPost = funDef.postcondition
        val body = matchToIfThenElse(funDef.body.get)
        val argAsVar = arg.toVariable

        optPost match {
          case None =>
            Seq.empty
          case Some((pid, post)) =>
            val children = classDef.knownChildren
            val conditionsForEachChild = (for (child <- classDef.knownChildren) yield (child match {
              case ccd @ CaseClassDef(id, prnt, vds) =>
                val selectors = selectorsOfParentType(classDefToClassType(classDef), ccd, argAsVar)
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
                new VerificationCondition(Implies(CaseClassInstanceOf(ccd, argAsVar), conditionForChild), funDef, VCKind.Postcondition, this)
              case _ => scala.sys.error("Abstract class has non-case class subtype.")
            }))
            conditionsForEachChild
        }

      case None =>
        reporter.warning("Induction tactic currently supports exactly one argument of abstract class type")
        defaultPost
    }
  }

  override def generatePreconditions(function: FunDef) : Seq[VerificationCondition] = {
    val defaultPrec = super.generatePreconditions(function)
    firstAbsClassDef(function.args) match {
      case Some((classDef, arg)) => {
        val toRet = if(function.hasBody) {
          val cleanBody = expandLets(matchToIfThenElse(function.body.get))

          val allPathConds = collectWithPathCondition((t => t match {
            case FunctionInvocation(fd, _) if(fd.hasPrecondition) => true
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
            val FunctionInvocation(fd, args) = fi

            val conditionsForEachChild = (for (child <- classDef.knownChildren) yield (child match {
              case ccd @ CaseClassDef(id, prnt, vds) => {
                val argAsVar = arg.toVariable
                val selectors = selectorsOfParentType(classDefToClassType(classDef), ccd, argAsVar)
                
                val prec : Expr = freshenLocals(matchToIfThenElse(fd.precondition.get))
                val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe))
                val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
                val newBody : Expr = replace(substMap, prec)
                val newCall : Expr = (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e))

                val toProve = withPrec(path, newCall)

                val conditionForChild =
                  if (selectors.isEmpty)
                    toProve
                  else {
                    val inductiveHypothesis = (for (sel <- selectors) yield {
                      val prec : Expr = freshenLocals(matchToIfThenElse(fd.precondition.get))
                      val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe))
                      val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
                      val newBody : Expr = replace(substMap, prec)
                      val newCall : Expr = (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e))

                      val toReplace = withPrec(path, newCall)
                      replace(Map(argAsVar -> sel), toReplace)
                    })
                    Implies(And(inductiveHypothesis), toProve)
                  }
                new VerificationCondition(Implies(CaseClassInstanceOf(ccd, argAsVar), conditionForChild), function, VCKind.Precondition, this).setPosInfo(fi)
              }
              case _ => scala.sys.error("Abstract class has non-case class subtype")
            }))
            conditionsForEachChild
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
