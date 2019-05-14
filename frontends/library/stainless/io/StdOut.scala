/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.io

import scala.language.implicitConversions

import stainless.annotation._

object StdOut {

  @extern
  @library
  def print(x: String): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(s: String): Unit = {
    print(s)
    print('\n')
  }

  @library
  @extern
  def print(x: Int): Unit = {
    scala.Predef.print(x)
  }

  @library
  def println(x: Int): Unit = {
    print(x)
    print('\n')
  }

  @library
  @extern
  def print(c: Char): Unit = {
    scala.Predef.print(c)
  }

  @library
  def println(c: Char): Unit = {
    print(c)
    print('\n')
  }

  @library
  def println(): Unit = {
    print('\n')
  }

}

