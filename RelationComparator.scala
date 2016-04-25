/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import leon.purescala.Constructors._
import leon.purescala.Types.Int32Type

trait RelationComparator { self : StructuralSize =>
  
  val comparisonMethod: String
  
  def isApplicableFor(p: Problem): Boolean

  /** strictly decreasing: args1 > args2 */
  def sizeDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr

  /** weakly decreasing: args1 >= args2 */
  def softDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr
}


trait ArgsSizeSumRelationComparator extends RelationComparator { self : StructuralSize =>

  val comparisonMethod = "comparing sum of argument sizes"

  def isApplicableFor(p: Problem): Boolean = true

  def sizeDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterThan(self.fullSize(tupleWrap(args1)), self.fullSize(tupleWrap(args2)))
  }

  def softDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterEquals(self.fullSize(tupleWrap(args1)), self.fullSize(tupleWrap(args2)))
  }
}


trait ArgsOuterSizeRelationComparator extends RelationComparator { self : StructuralSize =>

  val comparisonMethod = "comparing outer structural sizes of argument types"

  def isApplicableFor(p: Problem): Boolean = true

  def sizeDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterThan(self.outerSize(tupleWrap(args1)), self.outerSize(tupleWrap(args2)))
  }

  def softDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterEquals(self.outerSize(tupleWrap(args1)), self.outerSize(tupleWrap(args2)))
  }
}


trait LexicographicRelationComparator extends RelationComparator { self : StructuralSize =>

  val comparisonMethod = "comparing argument lists lexicographically"

  def isApplicableFor(p: Problem): Boolean = true

  def sizeDecreasing(s1: Seq[Expr], s2: Seq[Expr]): Expr = {
    lexicographicDecreasing(s1, s2, strict = true, sizeOfOneExpr = e => self.fullSize(e))
  }

  def softDecreasing(s1: Seq[Expr], s2: Seq[Expr]): Expr = {
    lexicographicDecreasing(s1, s2, strict = false, sizeOfOneExpr = e => self.fullSize(e))
  }
}

// for bitvector Ints
trait BVRelationComparator extends RelationComparator { self : StructuralSize =>

  /*
  Note: It might seem that comparing the sum of all Int arguments is more flexible, but on
  bitvectors, this causes overflow problems, so we won't be able to prove anything!
  So that's why this function is useless:
  
  def bvSize(args: Seq[Expr]): Expr = {
    val absValues: Seq[Expr] = args.collect{
      case e if e.getType == Int32Type => FunctionInvocation(typedAbsIntFun, Seq(e))
    }
    absValues.foldLeft[Expr](IntLiteral(0)){ case (sum, expr) => BVPlus(sum, expr) }
  }
  */

  val comparisonMethod = "comparing Int arguments lexicographically"

  def isApplicableFor(p: Problem): Boolean = {
    p.funDefs.forall(fd => fd.params.exists(valdef => valdef.getType == Int32Type))
  }

  def bvSize(e: Expr): Expr = FunctionInvocation(typedAbsIntFun, Seq(e))

  /* Note: We swap the arguments to the `lexicographicDecreasing` call
   * since bvSize maps into negative ints! (avoids -Integer.MIN_VALUE overflow) */

  def sizeDecreasing(s10: Seq[Expr], s20: Seq[Expr]): Expr = {
    val s1 = s10.filter(_.getType == Int32Type)
    val s2 = s20.filter(_.getType == Int32Type)
    lexicographicDecreasing(s2, s1, strict = true, sizeOfOneExpr = bvSize)
  }

  def softDecreasing(s10: Seq[Expr], s20: Seq[Expr]): Expr = {
    val s1 = s10.filter(_.getType == Int32Type)
    val s2 = s20.filter(_.getType == Int32Type)
    lexicographicDecreasing(s2, s1, strict = false, sizeOfOneExpr = bvSize)
  }
}


// vim: set ts=4 sw=4 et:
