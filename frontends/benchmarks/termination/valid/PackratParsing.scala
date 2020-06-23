/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import math._

/**
 * The packrat parser that uses the Expressions grammar presented in Bran Ford ICFP'02 paper.
 * The implementation is almost exactly as it was presented in the paper, but
 * here indices are passed around between parse functions, instead of strings.
 */
object PackratParsing {

  sealed abstract class Terminal
  case class Open() extends Terminal
  case class Close() extends Terminal
  case class Plus() extends Terminal
  case class Times() extends Terminal
  case class Digit() extends Terminal

  /**
   * A mutable array of tokens returned by the lexer.
   * The string of tokens is reversed i.e,
   * string(length-1) represents the first char and string(0) represents the last char.
   */
  @extern
  def string = Array[Terminal]()

  /**
   * looking up the ith token
   */
  @extern
  def lookup(i: BigInt): Terminal = {
    string(i.toInt)
  }

  sealed abstract class Result {
    /**
     * Checks if the index in the result (if any) is
     * smaller than `i`
     */
    //@inline - makes Dotty compiler crash
    def smallerIndex(i: BigInt) = this match {
      case Parsed(m) => m < i
      case _         => true
    }
  }
  case class Parsed(rest: BigInt) extends Result
  case class NoParse() extends Result

  def pAdd(i: BigInt): Result = {
    require(i >= 0)
    decreases(2*abs(i) + 1, 0)
    // Rule 1: Add <- Mul + Add
    val mulRes = pMul(i)
    mulRes match {
      case Parsed(j) =>
        if (j > 0 && lookup(j) == Plus()) {
          pAdd(j - 1) match {
            case Parsed(rem) =>
              Parsed(rem)
            case _ =>
              mulRes // Rule2: Add <- Mul
          }
        } else mulRes
      case _ =>
        mulRes
    }
  } ensuring (res => res.smallerIndex(i))

  def pMul(i: BigInt): Result = {
    require(i >= 0)
    decreases(2*abs(i), 2)
    // Rule 1: Mul <- Prim *  Mul
    val primRes = pPrim(i)
    primRes match {
      case Parsed(j) =>
        if (j > 0 && lookup(j) == Times()) {
          pMul(j - 1) match {
            case Parsed(rem) =>
              Parsed(rem)
            case _ =>
              primRes // Rule2: Mul <- Prim
          }
        } else primRes
      case _ =>
        primRes
    }
  } ensuring (res => res.smallerIndex(i))

  def pPrim(i: BigInt): Result = {
    require(i >= 0)
    decreases(2*abs(i), 1)
    val char = lookup(i)
    if (char == Digit()) {
      if (i > 0)
        Parsed(i - 1) // Rule1: Prim <- Digit
      else
        Parsed(-1) // here, we can use -1 to convey that the suffix is empty
    } else if (char == Open() && i > 0) {
      pAdd(i - 1) match { // Rule 2: pPrim <- ( Add )
        case Parsed(rem) =>
          if (rem >= 0 && lookup(rem) == Close()) Parsed(rem - 1)
          else NoParse()
        case _ =>
          NoParse()
      }
    } else NoParse()
  } ensuring (res => res.smallerIndex(i))

  def invoke(i: BigInt): Result = {
    require(i >= 0)
    (pPrim(i) match {
      case _ => pMul(i)
    }) match {
      case _ => pAdd(i)
    }
  }

  /**
   * Parsing a string of length 'n+1'.
   * Word is represented as an array indexed by 'n'. We only pass around the index.
   * The 'lookup' function will return a character of the array.
   */
  def parse(n: BigInt): Result = {
    require(n >= 0)
    if (n == 0) invoke(n)
    else {
      parse(n - 1) match { // we parse the prefixes ending at 0, 1, 2, 3, ..., n
        case _ =>
          invoke(n)
      }
    }
  }
}
