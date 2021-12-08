/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

trait OrderingRelation extends SolverProvider {
  val checker: ProcessingPipeline
  import checker.program.trees._

  val description: String

  /** Strictly decreasing: args1 < args2 */
  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr

  /** Weakly decreasing: args1 <= args2 */
  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr

  /** Associated measure to the ordering */
  def measure(args: Seq[Expr]): Expr
}

trait SumOrdering extends OrderingRelation { self: StructuralSize =>
  import checker.program.trees._
  import checker.program.symbols.{given, _}

  val description = "comparing sum of argument sizes"

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    LessThan(self.fullSize(tupleWrap(args1)), self.fullSize(tupleWrap(args2)))
  }

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    LessEquals(self.fullSize(tupleWrap(args1)), self.fullSize(tupleWrap(args2)))
  }

  def measure(args: Seq[Expr]): Expr = self.fullSize(tupleWrap(args))
}

trait LexicographicOrdering extends OrderingRelation { self: StructuralSize =>
  import checker.program.trees._
  import checker.program.symbols.{given, _}

  val description = "comparing argument lists lexicographically"

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    lexicographicallySmaller(args1, args2, strict = true, sizeOfOneExpr = e => self.fullSize(e))
  }

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    lexicographicallySmaller(args1, args2, strict = false, sizeOfOneExpr = e => self.fullSize(e))
  }

  // this should be extended to handle several types of lexicographic measures
  def measure(args: Seq[Expr]): Expr =
    tupleWrap(args.map { arg =>
      self.fullSize(arg)
    })
}

trait BVOrdering extends OrderingRelation { self: StructuralSize =>
  import checker.program.trees._
  import checker.program.symbols.{given, _}

  val description = "comparing bitvector arguments lexicographically"

  def bvSize(e: Expr): Expr = FunctionInvocation(bvAbs(e.getType.asInstanceOf[BVType]).id, Seq(), Seq(e))

  /* Note: We swap the arguments to the [[lexicographicallySmaller]] call since
   * [[bvSize]] maps into negative values! (avoids -Integer.MIN_VALUE overflow) */
  def groupedBySize(as: Seq[Expr]): Map[Int, Seq[Expr]] =
    as.collect { case IsTyped(e, BVType(_, i)) => i -> e }.groupBy(_._1).view.mapValues(_.map(_._2)).toMap

  private def compare(args1: Seq[Expr], args2: Seq[Expr], strict: Boolean): Expr = {
    val bv1 = groupedBySize(args1)
    val bv2 = groupedBySize(args2)

    val commonKeys = bv1.keys.toSet intersect bv2.keys.toSet

    orJoin(commonKeys.map { k =>
      // Here we swap bv1 and bv2!
      val kindDecreasing = lexicographicallySmaller(bv2(k), bv1(k), strict = strict, sizeOfOneExpr = bvSize)

      val kindsNotIncreasing =
        andJoin(
          commonKeys
            .filter { _ != k }
            .map { pk =>
              lexicographicallySmaller(bv2(pk), bv1(pk), strict = false, sizeOfOneExpr = bvSize)
            }
            .toSeq
        )

      and(kindDecreasing, kindsNotIncreasing)
    }.toSeq)
  }

  def lessThan(args1: Seq[Expr], args2: Seq[Expr]): Expr = compare(args1, args2, true)

  def lessEquals(args1: Seq[Expr], args2: Seq[Expr]): Expr = compare(args1, args2, false)

  // the ordering is unsound for size-change termination.
  // no correct measure will be inferred.
  def measure(args: Seq[Expr]): Expr = {
    val bv = groupedBySize(args)
    val maxLength = bv.keys.reduceLeft(_ max _)

    val measures = bv.view.mapValues { s =>
      self.fullSize(tupleWrap(s))
    }.values

    val widens = measures.map { m =>
      new BVWideningCast(m, BVType(true, maxLength))
    }.toSeq

    self.fullSize(tupleWrap(widens))
  }
}
