/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.lang.synthesis._
import leon.collection._

object Justify {
  /*
   * The Science of Programming from David Gries Section 20.1
   
   * The goal is to justify a text. We are given a list of indices corresponding
   * to the columns of the starting point of each word. Each words are already
   * separated by one space. The parameter s is the additional number of spaces
   * at the end of the line that we will need to add between words. We
   * want the number of space on the same line to differ by at most one.
   *
   * If we denote by p and q the two number of spaces between words (p and q differ
   * only by 1), then we want to only switch once the number of space between words
   * on the line. This means that we first separate words using p, then we do it using
   * q until the end of the line. 
   *
   * z is the line number, the rule is for odd line number to have more spaces on the right (q=p+1)
   * and for even line number to have more spaces on the left (p=q+1). We do not want trailing
   * spaces.
   *
   * n is the number of words on the line.
   *
   * If we apply this justify to each line of a text separately, this should lead to a good looking
   * justified text.

   * Here is an example:
   *
   * justifying lines by
   * inserting extra blanks is
   * one task of a text editor.
   *
   * results in:
   *
   * justifying     lines     by
   * inserting extra  blanks  is
   * one  task of a text editor.
   */

  def addSpaces(words: List[BigInt], p: BigInt, q: BigInt, t: BigInt, n: BigInt, i: BigInt): List[BigInt] = words match {
    case Nil() => Nil()
    case Cons(head, tail) =>
      if(i <= t) Cons(head + p*(i-1), addSpaces(tail, p, q, t, n, i+1))
      else if(i > t && i <= n) Cons(head + p*(t-1) + q*(i-t), addSpaces(tail, p, q, t, n, i+1))
      else Nil() //this should never happen
  }

  //this version implements the computation of parameters
  def justifyParamsImpl(n: BigInt, z: BigInt, s: BigInt): (BigInt, BigInt, BigInt) = {
    require(n >= 2 && s >= 0 && z >= 1)
    val (q, t, p) = if(z % 2 == 0) {
      val tmp = s / (n-1)
      (tmp, 1 + (s % (n - 1)), tmp + 1)
    } else {
      val tmp = s / (n-1)
      (tmp + 1, n - (s % (n - 1)), tmp)
    }
    (q, t, p)
  }

  def justifyImpl(n: BigInt, z: BigInt, s: BigInt, words: List[BigInt]): (BigInt, BigInt, BigInt, List[BigInt]) = {
    require(n >= 2 && s >= 0 && z >= 1)
    val (q, t, p) = if(z % 2 == 0) {
      val tmp = s / (n-1)
      (tmp, 1 + (s % (n - 1)), tmp + 1)
    } else {
      val tmp = s / (n-1)
      (tmp + 1, n - (s % (n - 1)), tmp)
    }
    (q, t, p, addSpaces(words, p, q, t, n, 0))
  }

}
