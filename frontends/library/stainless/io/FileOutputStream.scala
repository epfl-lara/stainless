/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.io

import scala.language.implicitConversions

import stainless.lang._
import stainless.annotation._

// NOTE I couldn't use java.io.FileOutputStream as a field of FileOutputStream... Leon doesn't
//      accept it. Instead, the stream is opened and closed everytime an operation is
//      carried out. Not efficient but better than nothing. The C99 implementation doesn't
//      suffer from this issue.
//
// NOTE Don't attempt to create a FileOutputStream directly. Use FileOutputStream.open instead.
//
// NOTE Don't forget to close the stream.

@library
object FileOutputStream {

  /**
   * Open a new stream to write into `filename`, erasing any previous
   * content of the file or creating a new one if needed.
   */
  @extern
  def open(filename: String): FileOutputStream = {
    // FIXME Importing stainless.lang.Option doesn't mean it is imported, why?
    new FileOutputStream(
      try {
        // Check whether the stream can be opened or not (and empty the file)
        val out = new java.io.FileWriter(filename, false)
        out.close()
        Some[String](filename)
      } catch {
        case _: Throwable => None[String]()
      }
    )
  }

}

@library
case class FileOutputStream(var filename: Option[String]) {

  /**
   * Close the stream; return `true` on success.
   *
   * NOTE The stream must not be used afterward, even on failure.
   */
  def close(): Boolean = {
    filename = None[String]()
    true // This implementation never fails
  }

  /**
   * Test whether the stream is opened or not.
   *
   * NOTE This is a requirement for all write operations.
   */
  // We assume the stream to be opened if and only if the filename is defined.
  def isOpen(): Boolean = filename.isDefined

  /**
   * Append an integer to the stream and return `true` on success.
   *
   * NOTE The stream must be opened first.
   */
  @extern
  def write(x: Int): Boolean = {
    require(isOpen())
    try {
      val out = new java.io.FileWriter(filename.get, true)
      out.append(x.toString)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }

  /**
   * Append a character to the stream and return `true` on success.
   *
   * NOTE The stream must be opened first.
   */
  @extern
  def write(c: Char): Boolean = {
    require(isOpen())
    try {
      val out = new java.io.FileWriter(filename.get, true)
      out.append(c)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }

  /**
   * Append a string to the stream and return `true` on success.
   *
   * NOTE The stream must be opened first.
   */
  @extern
  def write(s: String): Boolean = {
    require(isOpen())
    try {
      val out = new java.io.FileWriter(filename.get, true)
      out.append(s)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }

}

