/* Copyright 2009-2019 EPFL, Lausanne */
package stainless
package ast

import org.scalatest._

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}

class TreeSanitizerSuite extends FunSuite with InputUtils {

  val sources1 = List(
    """|
       |import stainless.lang._
       |import stainless.annotation._
       |
       |object test {
       |
       |  abstract class NonSealed {
       |    def bar: BigInt
       |  }
       |
       |  def foo(outer: BigInt): NonSealed = {
       |    case class Foo(y: BigInt) extends NonSealed {
       |      def bar = outer
       |    }
       |    Foo(12)
       |  }
       |
       |  def oops = {
       |    assert(foo(1) != foo(2))
       |  }
       |
       |  @ghost
       |  def ok = {
       |    assert(foo(1) != foo(2))
       |  }
       |
       |  sealed abstract class Sealed {
       |    def bar: BigInt
       |  }
       |
       |  def foo2(outer: BigInt): Sealed = {
       |    case class Foo2(y: BigInt) extends Sealed {
       |      def bar = outer
       |    }
       |    Foo2(12)
       |  }
       |
       |  def oops2 = {
       |    assert(foo2(1) != foo2(2))
       |  }
       |
       |  def oops3 = {
       |    val a = (x: BigInt) => x
       |    val b = (x: BigInt) => x
       |    assert(a == b)
       |  }
       |
       |  @ghost
       |  def ok3 = {
       |    val a = (x: BigInt) => x
       |    val b = (x: BigInt) => x
       |    assert(a == b)
       |  }
       |
       |  def ok3bis = {
       |    val a = (x: BigInt) => x
       |    val b = (x: BigInt) => x
       |    stainless.lang.StaticChecks.assert(a == b)
       |  }
       |
       |  def compare(prop: Boolean): Unit = ()
       |  def compareGhost(@ghost prop: Boolean): Unit = ()
       |
       |  def oops4 = {
       |    val a = (x: BigInt) => x
       |    val b = (x: BigInt) => x
       |    compare(a == b)
       |  }
       |
       |  def ok4 = {
       |    val a = (x: BigInt) => x
       |    val b = (x: BigInt) => x
       |    compareGhost(a == b)
       |  }
       |}
       |""".stripMargin)

  test("SoundEquality check yields the right errors") {
    implicit val ctx = stainless.TestContext.empty
    val (_, program) = load(sources1, sanitize = false)

    val errors = TreeSanitizer(xt).check(program.symbols)
    assert(errors.length == 4)

    errors
      .sortBy(_.tree.getPos)
      .zipWithIndex foreach {
        case (err, 0) => assert(err.tree.getPos.line == 19)
        case (err, 1) => assert(err.tree.getPos.line == 39)
        case (err, 2) => assert(err.tree.getPos.line == 45)
        case (err, 3) => assert(err.tree.getPos.line == 67)
        case (err, _) => assert(false, s"Unexpected error yielded at ${err.tree.getPos}: ${err.getMessage}")
      }
  }
}
