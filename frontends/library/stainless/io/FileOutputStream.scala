/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.io

import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks._

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

  /** Open a new stream to write into `filename`, erasing any previous
    * content of the file or creating a new one if needed.
    */
  @extern
  @cCode.function(
    code = """
    |FILE* __FUNCTION__(char* filename) {
    |  FILE* this = fopen(filename, "w");
    |  /* this == NULL on failure */
    |  return this;
    |}
    """,
    headerIncludes = "",
    cIncludes = ""
  )
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
@cCode.typedef(alias = "FILE*", include = "stdio.h")
case class FileOutputStream(var filename: Option[String]) {

  /** Close the stream; return `true` on success.
    *
    * NOTE The stream must not be used afterward, even on failure.
    */
  @cCode.function(
    code = """
    |bool __FUNCTION__(FILE* this) {
    |  if (this != NULL)
    |    return fclose(this) == 0;
    |  else
    |    return true;
    |}
    """,
    headerIncludes = "",
    cIncludes = ""
  )
  def close(): Boolean = {
    filename = None[String]()
    true // This implementation never fails
  }

  /** Test whether the stream is opened or not.
    *
    * NOTE This is a requirement for all write operations.
    */
  // We assume the stream to be opened if and only if the filename is defined.
  @cCode.function(
    code = """
    |bool __FUNCTION__(FILE* this) {
    |  return this != NULL;
    |}
    """,
    headerIncludes = "",
    cIncludes = ""
  )
  def isOpen: Boolean = filename.isDefined

  /** Append a byte to the stream and return `true` on success.
    *
    * NOTE The stream must be opened first.
    *
    * NOTE This is the symmetric function to FileInputStream.readByte;
    *      i.e. the same restrictions applies to GenC.
    */
  @extern
  @cCode.function(
    code = """
    |bool __FUNCTION__(FILE* this, int8_t x) {
    |  return fprintf(this, "%c", x) >= 0;
    |}
    """,
    headerIncludes = "inttypes.h",
    cIncludes = ""
  )
  def write(x: Byte): Boolean = {
    require(isOpen)
    try {
      val out = new java.io.FileOutputStream(filename.get, true)
      val b = Array[Byte](x)
      out.write(b, 0, 1)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }.ensuring(_ => isOpen)

  /** Append an integer to the stream and return `true` on success.
    *
    * NOTE The stream must be opened first.
    */
  @extern
  @cCode.function(
    code = """
    |bool __FUNCTION__(FILE* this, int32_t x) {
    |  return fprintf(this, "%"PRIi32, x) >= 0;
    |}
    """,
    headerIncludes = "inttypes.h",
    cIncludes = ""
  )
  def write(x: Int): Boolean = {
    require(isOpen)
    try {
      val out = new java.io.FileWriter(filename.get, true)
      out.append(x.toString)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }.ensuring(_ => isOpen)

  /** Append a character to the stream and return `true` on success.
    *
    * NOTE The stream must be opened first.
    */
  @extern
  @cCode.function(
    code = """
    |bool __FUNCTION__(FILE* this, char c) {
    |  return fprintf(this, "%c", c) >= 0;
    |}
    """,
    headerIncludes = "",
    cIncludes = ""
  )
  def write(c: Char): Boolean = {
    require(isOpen)
    try {
      val out = new java.io.FileWriter(filename.get, true)
      out.append(c)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }.ensuring(_ => isOpen)

  /** Append a string to the stream and return `true` on success.
    *
    * NOTE The stream must be opened first.
    */
  @extern
  @cCode.function(
    code = """
    |bool __FUNCTION__(FILE* this, char* s) {
    |  return fprintf(this, "%s", s) >= 0;
    |}
    """,
    headerIncludes = "",
    cIncludes = ""
  )
  def write(s: String): Boolean = {
    require(isOpen)
    try {
      val out = new java.io.FileWriter(filename.get, true)
      out.append(s)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }.ensuring(_ => isOpen)

}
