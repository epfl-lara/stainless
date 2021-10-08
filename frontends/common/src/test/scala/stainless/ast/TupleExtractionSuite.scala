/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import org.scalatest.funsuite.AnyFunSuite

class TupleExtractionSuite extends AnyFunSuite with InputUtils {

  val sources = List(
    """|object Tup5 {
       |
       |  def foo(t: (Int, Int, Byte, BigInt, String)) = t._5
       |
       |  def bar = (1, 2, 3, 4, 5)
       |
       |} """.stripMargin,

    """|object Tup6 {
       |
       |  def foo(t: (Int, Int, Byte, BigInt, String, Array[String])) = t._5
       |
       |  def bar = (1, 2, 3, 4, 5, 6)
       |
       |} """.stripMargin,

    """|object Tup22 {
       |
       |  def foo(t: (Int, Int, Byte, BigInt, String, Array[String],
       |              Int, Int, Int, Int, Int, Int, Int, Int, Int, Int,
       |              Int, Int, Int, Int, Int, Boolean)) = t._5
       |
       |  def bar = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22)
       |
       |} """.stripMargin
  )

  val ctx: inox.Context = stainless.TestContext.empty
  import ctx.given
  val (_, xlangProgram) = load(sources)
  val run = verification.VerificationComponent.run(extraction.pipeline)
  val program = inox.Program(run.trees)(run extract xlangProgram.symbols)

  import stainless.trees._

  /* Mini DSL for testing purposes */

  def funDef(name: String) = program.lookup[FunDef](name)

  test("Tuple5 extraction") {
    funDef("Tup5.foo").returnType match {
      case StringType() => // Ok
      case tpe => fail(s"Expected String, got '$tpe'")
    }

    funDef("Tup5.foo").params match {
      case Seq(p) => p.tpe match {
        case TupleType(bases) if bases.size == 5 => // ok
        case tpe => fail(s"Expected tuple of 5 elements, got '$tpe'")
      }
      case params => fail(s"Expected one tuple of 5 elements, got '$params'")
    }

    funDef("Tup5.bar").returnType match {
      case TupleType(bases) if (bases.size == 5) && (bases forall (_ == Int32Type())) => // ok
      case tpe => fail(s"Expected Tuple5, got '$tpe': ${tpe.getClass}")
    }
  }

  test("Tuple6 extraction") {
    funDef("Tup6.foo").returnType match {
      case StringType() => // Ok
      case tpe => fail(s"Expected String, got '$tpe'")
    }

    funDef("Tup6.foo").params match {
      case Seq(p) => p.tpe match {
        case TupleType(bases) if bases.size == 6 => // ok
        case tpe => fail(s"Expected tuple of 6 elements, got '$tpe'")
      }
      case params => fail(s"Expected one tuple of 6 elements, got '$params'")
    }

    funDef("Tup6.bar").returnType match {
      case TupleType(bases) if (bases.size == 6) && (bases forall (_ == Int32Type())) => // ok
      case tpe => fail(s"Expected Tuple6, got '$tpe': ${tpe.getClass}")
    }
  }
  test("Tuple22 extraction") {
    funDef("Tup22.foo").returnType match {
      case StringType() => // Ok
      case tpe => fail(s"Expected String, got '$tpe'")
    }

    funDef("Tup22.foo").params match {
      case Seq(p) => p.tpe match {
        case TupleType(bases) if bases.size == 22 => // ok
        case tpe => fail(s"Expected tuple of 22 elements, got '$tpe'")
      }
      case params => fail(s"Expected one tuple of 22 elements, got '$params'")
    }

    funDef("Tup22.bar").returnType match {
      case TupleType(bases) if (bases.size == 22) && (bases forall (_ == Int32Type())) => // ok
      case tpe => fail(s"Expected Tuple6, got '$tpe': ${tpe.getClass}")
    }
  }

}

