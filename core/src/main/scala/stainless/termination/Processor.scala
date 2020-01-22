/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import scala.language.existentials

trait Processor {
  val name: String

  implicit val debugSection = DebugSectionTermination

  val checker: ProcessingPipeline

  def run(problem: checker.Problem): Option[Seq[checker.Result]]

}

trait OrderingProcessor extends Processor {

  val ordering: OrderingRelation with Strengthener {
    val checker: OrderingProcessor.this.checker.type
  }

  import checker._
  import checker.context._
  import checker.program.trees._
  import checker.program.symbols._
  import ordering._

  // if given a measure of the form (induced,rest) where
  // induced is potentially a tuple, flatten will compute
  // the measure (induced.flatten,rest)
  //
  // in principle we consider only one nesting depth
  def flatten(induced: Expr, rest: Seq[Expr]) = {
    val updatedSymbols = apiTransform(checker.program.symbols)
    val unwrapped: Seq[Expr] = induced.getType(updatedSymbols) match {
      case TupleType(_) => unwrapTuple(induced, true)(updatedSymbols)
      case _            => Seq(induced)
    }
    tupleWrap(unwrapped ++ rest)
  }

  // takes a expression which is potentially a tuple expression
  // and returns the same expression with zero elements in each entry
  //
  // in principle we consider only one nesting depth
  def zeroTuple(expr: Expr): Expr = {
    val updatedSymbols = apiTransform(checker.program.symbols)
    expr.getType(updatedSymbols) match {
      case TupleType(tpes) =>
        tupleWrap(unwrapTuple(expr, true)(updatedSymbols).map(e => zeroTuple(e)))
      case tpe =>
        tpe match {
          case IntegerType()   => IntegerLiteral(0)
          case BVType(s, size) => BVLiteral(s, 0, size)
          case tpe             => reporter.fatalError("Unexpected measure type here: " + tpe)
        }
    }
  }

  /** Transforms a sequence of bindings extracted from a path in a sequence of lets.
    * This is useful in the measure annotation of the Chain and Decreases processors. */
  def bindingsToLets(bindings: Seq[(ValDef, Expr)], expr: Expr): Expr = {
    bindings.foldRight(expr) { case ((vd, vl), acc) =>
      Let(vd, vl, acc)
    }
  }
}
