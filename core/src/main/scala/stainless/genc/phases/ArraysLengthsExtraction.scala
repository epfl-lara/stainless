/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import extraction._
import extraction.throwing. { trees => tt }
import tt._


object ArraysLengthsExtraction {

  def get(syms: Symbols)(implicit ctx: inox.Context): Map[Identifier, Int] = {

    implicit val printerOpts: tt.PrinterOptions = tt.PrinterOptions.fromSymbols(syms, ctx)

    val prog = inox.Program(extraction.throwing.trees)(syms)
    val evaluator = new {
      val context = ctx
      val program: prog.type = prog
      val semantics = new inox.Semantics {
        val trees: throwing.trees.type = throwing.trees
        val symbols: syms.type = syms
        val program: prog.type = prog
        def createEvaluator(ctx: inox.Context) = ???
        def createSolver(ctx: inox.Context) = ???
      }
    } with evaluators.RecursiveEvaluator
      with inox.evaluators.HasDefaultGlobalContext
      with inox.evaluators.HasDefaultRecContext

    object TopLevelAnds {
      def unapply(e: Expr): Option[Seq[Expr]] = e match {
        case And(exprs) => Some(exprs.flatMap(unapply).flatten)
        case e => Some(Seq(e))
      }
    }

    object EvalBV {
      def unapply(expr: Expr): Option[BVLiteral] = {
        evaluator.eval(expr) match {
          case inox.evaluators.EvaluationResults.Successful(bv: BVLiteral) => Some(bv)
          case _ => None
        }
      }
    }


    val arrayLengths: Seq[(Identifier, Int)] = syms.classes.values.toSeq.flatMap(cd => cd.flags
      .find(_.isInstanceOf[HasADTInvariant]).toSeq.flatMap {
        case HasADTInvariant(inv) =>
          val invFd = syms.getFunction(inv)
          val Seq(tthisVd) = invFd.params
          val TopLevelAnds(conjuncts) = invFd.fullBody
          conjuncts.collect(e => e match {
            case Equals(ArrayLength(ClassSelector(tthis: Variable, array)), EvalBV(bv))
              if tthisVd.id == tthis.id && cd.fields.map(_.id).contains(array) =>

              array -> bv.toBigInt.toInt
          })
      }
    )

    val grouped = arrayLengths.groupBy(_._1)
    val duplicate = grouped.find {
      case (id, ys) => ys.length > 1
    }

    if (duplicate.nonEmpty)
      ctx.reporter.fatalError(s"Cannot specify two lengths for array ${duplicate.head._1.asString} in a class invariant")

    arrayLengths.toMap
  }

}
