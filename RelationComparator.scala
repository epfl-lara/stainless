/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import leon.purescala.Constructors._

trait RelationComparator { self : StructuralSize =>
  
  val comparisonMethod: String

  def sizeDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr

  def softDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr

}


trait ArgsSizeSumRelationComparator extends RelationComparator { self : StructuralSize =>

  val comparisonMethod = "comparing sum of argument sizes"

  def sizeDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterThan(self.size(tupleWrap(args1)), self.size(tupleWrap(args2)))
  }

  def softDecreasing(args1: Seq[Expr], args2: Seq[Expr]): Expr = {
    GreaterEquals(self.size(tupleWrap(args1)), self.size(tupleWrap(args2)))
  }

}


trait LexicographicRelationComparator extends RelationComparator { self : StructuralSize =>

  val comparisonMethod = "comparing argument lists lexicographically"
  
  def lexicographicDecreasing(s1: Seq[Expr], s2: Seq[Expr], strict: Boolean): Expr = {
    val sameSizeExprs = for ((arg1, arg2) <- (s1 zip s2)) yield Equals(self.size(arg1), self.size(arg2))
    
    val greaterBecauseGreaterAtFirstDifferentPos =
      orJoin(for (firstDifferent <- 0 until scala.math.min(s1.length, s2.length)) yield and(
          andJoin(sameSizeExprs.take(firstDifferent)),
          GreaterThan(self.size(s1(firstDifferent)), self.size(s2(firstDifferent)))
      ))
      
    if (s1.length > s2.length || (s1.length == s2.length && !strict)) {
      or(andJoin(sameSizeExprs), greaterBecauseGreaterAtFirstDifferentPos)
    } else {
      greaterBecauseGreaterAtFirstDifferentPos
    }
  }

  def sizeDecreasing(s1: Seq[Expr], s2: Seq[Expr]) = lexicographicDecreasing(s1, s2, strict = true)

  def softDecreasing(s1: Seq[Expr], s2: Seq[Expr]) = lexicographicDecreasing(s1, s2, strict = false)

}

// vim: set ts=4 sw=4 et:
