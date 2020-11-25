/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.io

import scala.language.implicitConversions

import stainless.annotation._
import stainless.lang.StaticChecks._

object StdOut {

  @extern
  @library
  @cCode.function(
    code = """
      |static void __FUNCTION__(char* s) {
      |  printf("%s", s);
      |}
      """,
    includes = "stdio.h"
  )
  def print(x: String): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(s: String): Unit = {
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
      |static void __FUNCTION__(int8_t x) {
      |  printf("%c", x);
      |}
      """,
    includes = "inttypes.h:stdio.h"
  )
  def print(x: Byte): Unit = {
    val b = Array[Byte](x)
    System.out.write(b, 0, 1)
  }

  @library
  def println(x: Byte): Unit = {
    print(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
     |static void __FUNCTION__(int32_t x) {
     |  printf("%"PRIi32, x);
     |}
     """,
    includes = "inttypes.h:stdio.h"
  )
  def print(x: Int): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(x: Int): Unit = {
    print(x)
    println()
  }

  @library
  @extern
  @cCode.function(
    code = """
      |static void __FUNCTION__(char c) {
      |  printf("%c", c);
      |}
      """,
    includes = "stdio.h"
  )
  def print(c: Char): Unit = {
    scala.Predef.print(c)
  }

  @library
  def println(c: Char): Unit = {
    print(c)
    println()
  }

  @library
  def println(): Unit = {
    print('\n')
  }

  @extern
  @library
  @pure
  @cCode.function(
    code = """
      |static void __FUNCTION__(void* s) {
      |  printf("%s", s);
      |}
      """,
    includes = "stdio.h"
  )
  def print(x: Any): Unit = {
    scala.Predef.print(x)
  }

  @extern
  @library
  @pure
  @cCode.function(
    code = """
      |static void __FUNCTION__(void* s) {
      |  printf("%s\n", s);
      |}
      """,
    includes = "stdio.h"
  )
  def println(x: Any): Unit = {
    scala.Predef.println(x)
  }
}
