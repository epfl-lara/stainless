/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.io

import stainless.annotation._
import stainless.math.BitVectors._

object StdOut {

  @library
  @extern
  @cCode.function(
    code = """
     |void __FUNCTION__(uint8_t x) {
     |  printf("%"PRIu8, x);
     |}
     """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def printU8(x: UInt8)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @library
  def printlnU8(x: UInt8)(implicit @ghost state: State): Unit = {
    printU8(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
     |void __FUNCTION__(uint16_t x) {
     |  printf("%"PRIu16, x);
     |}
     """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def printU16(x: UInt16)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @library
  def printlnU16(x: UInt16)(implicit @ghost state: State): Unit = {
    printU16(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
     |void __FUNCTION__(uint32_t x) {
     |  printf("%"PRIu32, x);
     |}
     """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def printU32(x: UInt32)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @library
  def printlnU32(x: UInt32)(implicit @ghost state: State): Unit = {
    printU32(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
     |void __FUNCTION__(uint64_t x) {
     |  printf("%"PRIu64, x);
     |}
     """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def printU64(x: UInt64)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @library
  def printlnU64(x: UInt64)(implicit @ghost state: State): Unit = {
    printU64(x)
    println()
  }

  @extern
  @library
  @cCode.function(
    code = """
      |void __FUNCTION__(char* s) {
      |  printf("%s", s);
      |}
      """,
    headerIncludes = "stdio.h",
    cIncludes = ""
  )
  def print(x: String)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(s: String)(implicit @ghost state: State): Unit = {
    print(s)
    println()
  }

  /**
   * This is the symmetric function to StdIn.readByte;
   * i.e. the same restrictions applies for GenC.
   */
  @library
  @extern
  @cCode.function(
    code = """
      |void __FUNCTION__(int8_t x) {
      |  printf("%c", x);
      |}
      """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def print(x: Byte)(implicit @ghost state: State): Unit = {
    val b = Array[Byte](x)
    System.out.write(b, 0, 1)
  }

  @library
  def println(x: Byte)(implicit @ghost state: State): Unit = {
    print(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
     |void __FUNCTION__(int32_t x) {
     |  printf("%"PRIi32, x);
     |}
     """,
    headerIncludes = "inttypes.h:stdio.h",
    cIncludes = ""
  )
  def print(x: Int)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(x: Int)(implicit @ghost state: State): Unit = {
    print(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
      |void __FUNCTION__(char c) {
      |  printf("%c", c);
      |}
      """,
    headerIncludes = "stdio.h",
    cIncludes = ""
  )
  def print(c: Char)(implicit @ghost state: State): Unit = {
    scala.Predef.print(c)
  }

  @library
  def println(c: Char)(implicit @ghost state: State): Unit = {
    print(c)
    println()
  }

  @library
  def println()(implicit @ghost state: State): Unit = {
    print('\n')
  }

  @extern
  @library
  @cCode.function(
    code = """
      |void __FUNCTION__(void* s) {
      |  printf("%s", s);
      |}
      """,
    headerIncludes = "stdio.h",
    cIncludes = ""
  )
  def print(x: Any)(implicit @ghost state: State): Unit = {
    scala.Predef.print(x)
  }

  @extern
  @library
  @cCode.function(
    code = """
      |void __FUNCTION__(void* s) {
      |  printf("%s\n", s);
      |}
      """,
    headerIncludes = "stdio.h",
    cIncludes = ""
  )
  def println(x: Any)(implicit @ghost state: State): Unit = {
    scala.Predef.println(x)
  }
}
