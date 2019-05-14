/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.io

import scala.language.implicitConversions

import stainless.annotation._

/*
 * NOTEs for GenC:
 * --------------
 *
 *  - `stainless.io.State` should be completely ignored as it is an artefact for verification
 *    proofs. TODO It might be interesting to completely drop it from the C code
 *    instead of aliasing it to void* and the null pointer.
 *
 *  - While `bool` is a standard C99 type (aliased to `_Bool`), there is no specifier
 *    for scan operation. Additionnally, the actual size of a boolean is platform
 *    dependent. Therefore, for simplicity, `readBoolean` is currently dropped.
 *
 *  - Currently, GenC doesn't support `BigInt` which implies that `readBigInt` is
 *    dropped as well.
 *
 *  - In order to handle errors (e.g. EOF or invalid formatting), the API has to be
 *    updated. One solution would be to return `Option`s. Another would be to use
 *    exception, however this is probably trickier to translate to C.
 *
 *  - Decisions regarding those issues should be applied to FileInputStream as well.
 *
 *
 * FIXME Using the `scala.io.StdIn.read*` methods has a major shortcomming:
 *       the data is read from a entire line!
 */

object StdIn {

  /**
   * Reads the next signed decimal integer
   *
   * TODO to support other integer bases, one has to use SCNi32 in C.
   */
  @library
  def readInt(implicit state: State): Int = {
    state.seed += 1
    nativeReadInt(state.seed)
  }

  @library
  @extern
  private def nativeReadInt(seed: BigInt): Int = {
    /* WARNING This code is singificantly a duplicate of stainless.io.FileInputStream.nativeReadInt
     *         because there's no clean way to refactor this in Leon's library.
     *
     * This implementation mimic `scanf("%d")` for 32-bit integer.
     *
     * NOTE
     *  - The `%d` flag is for signed decimal integers;
     *  - The format of the number is the same as expected by strtol() with the value 10 for the base argument;
     *  - This format corresponds to the following regex:
     *
     *              \s*[+-]?\d+
     *
     *    where
     *      - `\s` match any character c such that `isspace(c)` holds;
     *      - a negative number (indicated by a leading `-`) is negated using the unary `-` operator;
     *  - If the converted value falls out of range of 32-bit integers, either Int.MaxValue or Int.MinValue is returned;
     *  - Note that reading the "-MaxValue" is undefined behaviour in C, and so is it in this implementation;
     *  - If the input doesn't match an integer then no input is consumed.
     */

    val EOF = -1

    val in = System.in
    assert(in.markSupported())
    def markStream() = in.mark(Int.MaxValue)

    // Handle error in parsing and restore the stream, return the given error code
    def fail(e: Int): Int = {
      in.reset()
      e // TODO throw an exception and change `e` for a decent error message
    }

    // Handle success, but also restore stream in case we peeked at the next character
    def success(x: Int): Int = {
      in.reset()
      x
    }

    // Mark the stream now, so that in case of formatting error we can cancel the read
    markStream()

    // Match C99 isspace function: either space (0x20), form feed (0x0c), line feed (0x0a), carriage return (0x0d), horizontal tab (0x09) or vertical tab (0x0b)
    def isSpace(c: Int): Boolean = Set(0x20, 0x0c, 0x0a, 0x0d, 0x09, 0x0b) contains c

    // Digit base 10
    def isDigit(c: Int): Boolean = c >= '0' && c <= '9'

    // Return the first non-space character, return -1 if reach EOF
    def skipSpaces(): Int = {
      val x = in.read()
      if (isSpace(x)) skipSpaces()
      else            x
    }

    // Safely wrap the addition of the accumulator with a digit character
    def safeAdd(acc: Int, c: Int): Int = {
      require(isDigit(c))

      val x = c - '0'
      val r = acc * 10 + x

      if (r >= 0) r
      else        Int.MaxValue
    } // ensuring { res => res >= 0 && res <= Int.MaxInt }

    // Read as many digit as possible, and after each digit we mark
    // the stream to simulate a "peek" at the next, possibly non-digit,
    // character on the stream.
    def readDecInt(acc: Int, mark: Boolean): Int = {
      if (mark) markStream()

      val c = in.read()

      if (isDigit(c)) readDecInt(safeAdd(acc, c), true)
      else if (mark)  success(acc) // at least one digit was processed
      else            fail(-2) // no digit was processed
    }

    val first = skipSpaces()
    first match {
      case EOF             => fail(-1)
      case '-'             => - readDecInt(0, false)
      case '+'             =>   readDecInt(0, false)
      case c if isDigit(c) =>   readDecInt(c - '0', true)
      case _               => fail(-3)
    }
  } ensuring((x: Int) => true)

  @library
  def readBigInt(implicit state: State): BigInt = {
    state.seed += 1
    nativeReadBigInt(state.seed)
  }

  @library
  @extern
  private def nativeReadBigInt(seed: BigInt): BigInt = {
    BigInt(scala.io.StdIn.readInt)
  } ensuring((x: BigInt) => true)

  @library
  def readBoolean(implicit state: State): Boolean = {
    state.seed += 1
    nativeReadBoolean(state.seed)
  }

  @library
  @extern
  private def nativeReadBoolean(seed: BigInt): Boolean = {
    scala.io.StdIn.readBoolean
  } ensuring((x: Boolean) => true)

}
