/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.annotation.tailrec

class RecursionProcessor(override val checker: ProcessingPipeline)
                        // Alias for checker, as we cannot use it to define ordering
                        (override val chker: checker.type)
                        (override val ordering: OrderingRelation with Strengthener with RelationBuilder {
                          val checker: chker.type
                        })
  extends OrderingProcessor("Recursion Processor", checker, ordering) {

  def this(chker: ProcessingPipeline,
           ordering: OrderingRelation with Strengthener with RelationBuilder {
             val checker: chker.type
           }) =
    this(chker)(chker)(ordering)

  import checker._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols.{given, _}
  import ordering._

  private def isSubtreeOf(expr: Expr, v: Variable): Boolean = {
    @tailrec
    def rec(e: Expr, fst: Boolean): Boolean = e match {
      case v2: Variable if v == v2 => !fst
      case ADTSelector(cc, _)      => rec(cc, false)
      case Annotated(e, _)         => rec(e, fst)
      case _                       => false
    }
    rec(expr, true)
  }

  def run(problem: Problem) =
    if (problem.funDefs.size > 1) None
    else
      timers.termination.processors.recursion.run {
        val funDef = problem.funDefs.head
        val relations = getRelations(funDef)
        val (recursive, others) = relations.partition {
          case Relation(fd, _, fi, _) => fd == fi.tfd.fd
        }

        val noGuarantees = others.exists {
          case Relation(_, _, fi, _) => !checker.terminates(fi.tfd.fd).isGuaranteed
        }

        if (noGuarantees) {
          None
        } else if (recursive.isEmpty) {
          val inductiveLemmas = 
            Some((ordering.getPostconditions, ordering.insertedApps))
          Some(Cleared(funDef, None, inductiveLemmas) :: Nil)
        } else {
          val decreases = funDef.params.zipWithIndex.find {
            case (arg, index) =>
              recursive.forall {
                case Relation(_, path, FunctionInvocation(_, _, args), _) =>
                  args(index) match {
                    // handle case class deconstruction in match expression!
                    case v: Variable =>
                      path.bindings.exists {
                        case (vd, ccs) if vd.toVariable == v => isSubtreeOf(ccs, arg.toVariable)
                        case _                               => false
                      }
                    case expr =>
                      isSubtreeOf(expr, arg.toVariable)
                  }
              }
          }

          decreases match {
            case Some(p) =>
              val measure = ordering.measure(Seq(p._1.toVariable))
              measureCache.add(funDef -> measure)
              val inductiveLemmas = 
                Some((ordering.getPostconditions, ordering.insertedApps))
              Some(Cleared(funDef, Some(measure), inductiveLemmas) :: Nil)
            case None =>
              None
          }
        }
      }
}
