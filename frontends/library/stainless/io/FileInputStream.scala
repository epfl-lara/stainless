/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.io

import scala.language.implicitConversions

import stainless.lang._
import stainless.annotation._

// See NOTEs in StdIn.
//
// NOTE Don't attempt to create a FileInputStream directly. Use FileInputStream.open instead.
//
// NOTE Don't forget to close the stream.

@library
object FileInputStream {

  /**
   * Open a new stream to read from `filename`, if it exists.
   */
  @extern
  def open(filename: String)(implicit state: State): FileInputStream = {
    state.seed += 1

    new FileInputStream(
      try {
        // Check whether the stream can be opened or not
        val out = new java.io.FileReader(filename)
        out.close()
        Some[String](filename)
      } catch {
        case _: Throwable => None[String]()
      },
      0 // nothing consumed yet
    )
  }

}

@library
case class FileInputStream(var filename: Option[String], var consumed: BigInt) {

  /**
   * Close the stream; return `true` on success.
   *
   * NOTE The stream must not be used afterward, even on failure.
   */
  def close(implicit state: State): Boolean = {
    state.seed += 1

    filename = None[String]()
    true // This implementation never fails
  }

  /**
   * Test whether the stream is opened or not.
   *
   * NOTE This is a requirement for all write operations.
   */
  // We assume the stream to be opened if and only if the filename is defined.
  def isOpen: Boolean = {
    filename.isDefined
  }

  @library
  def readInt(implicit state: State): Int = {
    require(isOpen)
    state.seed += 1
    nativeReadInt(state.seed)
  }

  // Implementation detail
  @library
  @extern
  private def nativeReadInt(seed: BigInt): Int = {
    /* WARNING This code is singificantly a duplicate of stainless.io.StdIn.nativeReadInt
     *         because there's no clean way to refactor this in Leon's library.
     *
     * This implementation mimic `fscanf("%d")` for 32-bit integer.
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

    val in = new java.io.FileInputStream(filename.get)

    // Keep track of the number of by read so far in this operation
    var reads = 0
    def read(): Int = {
      reads += 1
      in.read()
    }

    // Update the mark on the stream as well as our internal consumption counter
    def markStream() = {
      consumed += reads
      reads = 0
    }

    // Skip what was already consumed by previous reads
    assert(in.skip(consumed.toLong) == consumed.toLong) // Yes, skip might not skip the requested number of bytes...

    // Handle error in parsing and close the stream, return the given error code
    def fail(e: Int): Int = {
      in.close()
      e // TODO throw an exception and change `e` for a decent error message
    }

    // Handle success (nothing to do actually) and close the stream
    def success(x: Int): Int = {
      in.close()
      x
    }

    // Match C99 isspace function: either space (0x20), form feed (0x0c), line feed (0x0a), carriage return (0x0d), horizontal tab (0x09) or vertical tab (0x0b)
    def isSpace(c: Int): Boolean = Set(0x20, 0x0c, 0x0a, 0x0d, 0x09, 0x0b) contains c

    // Digit base 10
    def isDigit(c: Int): Boolean = c >= '0' && c <= '9'

    // Return the first non-space character, return -1 if reach EOF
    def skipSpaces(): Int = {
      val x = read()
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

      val c = read()

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


}

