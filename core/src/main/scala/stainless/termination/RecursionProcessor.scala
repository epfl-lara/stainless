/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.annotation.tailrec

trait RecursionProcessor extends Processor {

  val builder: RelationBuilder {
    val checker: RecursionProcessor.this.checker.type
  }

  val name: String = "Recursion Processor"

  import builder._
  import checker._
  import program.trees._
  import program.symbols._

  private def isSubtreeOf(expr: Expr, v: Variable) : Boolean = {
    @tailrec
    def rec(e: Expr, fst: Boolean): Boolean = e match {
      case v2: Variable if v == v2 => !fst
      case ADTSelector(cc, _) => rec(cc, false)
      case _ => false
    }
    rec(expr, true)
  }

  def run(problem: Problem) = if (problem.funDefs.size > 1) None else {
    val timer = program.ctx.timers.termination.processors.recursion.start()

    val funDef = problem.funDefs.head
    val relations = getRelations(funDef)
    val (recursive, others) = relations.partition { case Relation(fd, _, fi, _) => fd == fi.tfd.fd }

    val res = if (others.exists({ case Relation(_, _, fi, _) => !checker.terminates(fi.tfd.fd).isGuaranteed })) {
      None
    } else if (recursive.isEmpty) {
      Some(Cleared(funDef) :: Nil)
    } else {
      val decreases = funDef.params.zipWithIndex.exists { case (arg, index) =>
        recursive.forall { case Relation(_, path, FunctionInvocation(_, _, args), _) =>
          args(index) match {
            // handle case class deconstruction in match expression!
            case v: Variable => path.bindings.exists {
              case (vd, ccs) if vd.toVariable == v => isSubtreeOf(ccs, arg.toVariable)
              case _ => false
            }
            case expr => isSubtreeOf(expr, arg.toVariable)
          }
        }
      }

      if (decreases)
        Some(Cleared(funDef) :: Nil)
      else
        None
    }

    timer.stop()
    res
  }
}
