/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import org.scalatest.funsuite.AnyFunSuite
import frontend.UnsupportedCodeException

import scala.util.control.NonFatal

class ExplicitNumericPromotionSuite extends AnyFunSuite with InputUtils {

  val unsupported = List(
    """|object Shift1 {
       | def foo(i: Byte, j: Long) = i << j
       |} """.stripMargin,

    """|object Shift3 {
       | def foo(i: Short, j: Long) = i >> j
       |} """.stripMargin,

    """|object Shift2 {
       | def foo(i: Int, j: Long) = i >>> j
       |} """.stripMargin
  )

  test("Catch unsupported expressions") {
    for (u <- unsupported) {
      val ctx = stainless.TestContext.empty
      try {
        load(Seq(u))(using ctx)
        // load did not throw an exception. It may have reported the error to the reporter
        assert(ctx.reporter.errorCount == 1)
      } catch {
        case uce: UnsupportedCodeException => () // Ok
        case NonFatal(e) => fail(e)
      }
    }
  }

  val sources = List(
    """|object Ints {
       |
       |  def foo(i: Int, j: Int) = i + j
       |
       |  def bar(i: Int, j: Int) = i & j
       |
       |  def gun(i: Int) = -i
       |
       |} """.stripMargin,

    """|object Longs {
       |
       |  def foo(i: Long, j: Long) = i + j
       |
       |  def bar(i: Long, j: Long) = i & j
       |
       |  def gun(i: Long) = +i
       |
       |} """.stripMargin,

    """|object IntByte {
       |
       |  def foo(i: Int, j: Byte) = i + j
       |
       |  def bar(i: Int, j: Byte) = i & j
       |
       |} """.stripMargin,

    """|object ByteInt {
       |
       |  def foo(i: Byte, j: Int) = i + j
       |
       |  def bar(i: Byte, j: Int) = i & j
       |
       |} """.stripMargin,

    """|object IntShort {
       |
       |  def foo(i: Int, j: Short) = i + j
       |
       |  def bar(i: Int, j: Short) = i & j
       |
       |} """.stripMargin,

    """|object ByteShort {
       |
       |  def foo(i: Byte, j: Short) = i + j
       |
       |} """.stripMargin,

    """|object MixWithLong {
       |
       |  def foo(i: Long, j: Int) = i + j
       |
       |  def bar(i: Byte, j: Long) = i | j
       |
       |} """.stripMargin,

    """|object Shifts {
       |
       |  def fun1 (i: Byte,  j: Byte ) = i <<  j
       |  def fun2 (i: Byte,  j: Short) = i >>> j
       |  def fun3 (i: Byte,  j: Int  ) = i >>  j
       |  //def fun4 (i: Byte,  j: Long ) = i <<  j // UNSUPPORTED
       |
       |  def fun5 (i: Short, j: Byte ) = i >>> j
       |  def fun6 (i: Short, j: Short) = i >>  j
       |  def fun7 (i: Short, j: Int  ) = i <<  j
       |  //def fun8 (i: Short, j: Long ) = i >>> j // UNSUPPORTED
       |
       |  def fun9 (i: Int,   j: Byte ) = i >>  j
       |  def fun10(i: Int,   j: Short) = i <<  j
       |  def fun11(i: Int,   j: Int  ) = i >>> j
       |  //def fun12(i: Int,   j: Long ) = i >>  j // UNSUPPORTED
       |
       |  def fun13(i: Long,  j: Byte ) = i <<  j
       |  def fun14(i: Long,  j: Short) = i >>> j
       |  def fun15(i: Long,  j: Int  ) = i >>  j
       |  def fun16(i: Long,  j: Long ) = i <<  j
       |
       |} """.stripMargin,

    """|object Bytes {
       |
       |  def foo(i: Byte, j: Byte) = i + j
       |
       |  def bar(i: Byte, j: Byte) = i & j
       |
       |  def gun(i: Byte) = -i
       |
       |  def hun(i: Byte) = +i
       |
       |} """.stripMargin,

    """|object ExplicitCast {
       |
       |  def foo1(i: Int)  = bar(i.toByte)
       |  def foo2(i: Long) = bar(i.toShort.toByte)
       |
       |  def bar(i: Byte) = i
       |
       |} """.stripMargin,

    """|object ImplicitCast {
       |
       |  def foo1(i: Byte)  = bar1(i) // implicit i.toInt here
       |  def foo2(i: Short) = bar1(i) // implicit i.toInt here
       |  def foo3(i: Short) = bar2(i) // implicit i.toLong here
       |
       |  def bar1(i: Int) = i
       |  def bar2(i: Long) = i
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

  def funDefBody(name: String) = program.lookup[FunDef](name).fullBody

  object Var {
    def unapply(e: Expr) = e match {
      case Variable(id, typ, _) => Some((id.name, typ))
      case _ => None
    }
  }

  object FunCall {
    def unapply(e: Expr) = e match {
      case FunctionInvocation(id, Seq(), args) => Some((id.name, args))
      case _ => None
    }
  }

  case class V(name: String, typ: Type) extends Expr {
    def getType(using Symbols): Type = typ

    override def equals(o: Any) = o match {
      case Var(nme, `typ`) => nme.dropWhile(_ == '~') == name
      case _ => false
    }
  }

  val i8  = V("i", Int8Type())
  val j8  = V("j", Int8Type())
  val i16 = V("i", Int16Type())
  val j16 = V("j", Int16Type())
  val i32 = V("i", Int32Type())
  val j32 = V("j", Int32Type())
  val i64 = V("i", Int64Type())
  val j64 = V("j", Int64Type())


  test("No redundant cast on arithmetic Int operations") {
    funDefBody("Ints.foo") match {
      case Plus(`i32`, `j32`) => // OK
      case b => fail(s"Expected a simple BV addition, got '$b'")
    }

    funDefBody("Ints.bar") match {
      case BVAnd(`i32`, `j32`) => // OK
      case b => fail(s"Expected a simple BV `&`, got '$b'")
    }

    funDefBody("Ints.gun") match {
      case UMinus(`i32`) => // OK
      case b => fail(s"Expected a simple BV unary minus, got '$b'")
    }
  }

  test("No redundant cast on arithmetic Long operations") {
    funDefBody("Longs.foo") match {
      case Plus(`i64`, `j64`) => // OK
      case b => fail(s"Expected a simple BV addition, got '$b'")
    }

    funDefBody("Longs.bar") match {
      case BVAnd(`i64`, `j64`) => // OK
      case b => fail(s"Expected a simple BV `&`, got '$b'")
    }

    funDefBody("Longs.gun") match {
      case `i64` => // OK
      case b => fail(s"Expected a simple BV unary plus (which is dropped), got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving ints & bytes") {
    funDefBody("IntByte.foo") match {
      case Plus(`i32`, `j8`) => fail(s"No explicit cast was inserted")
      case Plus(`i32`, BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("IntByte.bar") match {
      case BVAnd(`i32`, BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"Expected a BV `&` with explicit cast, got '$b'")
    }

    // Test symmetry
    funDefBody("ByteInt.foo") match {
      case Plus(BVWideningCast(`i8`, Int32Type()), `j32`) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("ByteInt.bar") match {
      case BVAnd(BVWideningCast(`i8`, Int32Type()), `j32`) => // OK
      case b => fail(s"Expected a BV `&` with explicit cast, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving ints & shorts") {
    funDefBody("IntShort.foo") match {
      case Plus(`i32`, BVWideningCast(`j16`, Int32Type())) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("IntShort.bar") match {
      case BVAnd(`i32`, BVWideningCast(`j16`, Int32Type())) => // OK
      case b => fail(s"Expected a BV addition with explicit casts, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving bytes & shorts") {
    funDefBody("ByteShort.foo") match {
      case Plus(BVWideningCast(`i8`, Int32Type()), BVWideningCast(`j16`, Int32Type())) => // OK
      case b => fail(s"Expected a BV addition with explicit casts, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving Long and other types") {
    funDefBody("MixWithLong.foo") match {
      case Plus(`i64`, BVWideningCast(`j32`, Int64Type())) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("MixWithLong.bar") match {
      case BVOr(BVWideningCast(`i8`, Int64Type()), `j64`) => // OK
      case b => fail(s"Expected a BV `|` with explicit cast, got '$b'")
    }
  }

  test("Shift operations with different operand types") {
    funDefBody("Shifts.fun1") match {
      case BVShiftLeft(BVWideningCast(`i8`, Int32Type()), BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"[01] Expected a BV << with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun2") match {
      case BVLShiftRight(BVWideningCast(`i8`, Int32Type()), BVWideningCast(`j16`, Int32Type())) => // OK
      case b => fail(s"[02] Expected a BV >>> with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun3") match {
      case BVAShiftRight(BVWideningCast(`i8`, Int32Type()), `j32`) => // OK
      case b => fail(s"[03] Expected a BV >> with explicit cast, got '$b'")
    }

    /*
     * funDefBody("Shifts.fun4") match {
     *   case b => fail(s"Unexpected, got '$b'")
     * }
     */

    funDefBody("Shifts.fun5") match {
      case BVLShiftRight(BVWideningCast(`i16`, Int32Type()), BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"[05] Expected a BV >>> with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun6") match {
      case BVAShiftRight(BVWideningCast(`i16`, Int32Type()), BVWideningCast(`j16`, Int32Type())) => // OK
      case b => fail(s"[06] Expected a BV >> with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun7") match {
      case BVShiftLeft(BVWideningCast(`i16`, Int32Type()), `j32`) => // OK
      case b => fail(s"[07] Expected a BV << with explicit cast, got '$b'")
    }

    /*
     * funDefBody("Shifts.fun8") match {
     *   case b => fail(s"Unexpected, got '$b'")
     * }
     */

    funDefBody("Shifts.fun9") match {
      case BVAShiftRight(`i32`, BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"[09] Expected a BV >> with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun10") match {
      case BVShiftLeft(`i32`, BVWideningCast(`j16`, Int32Type())) => // OK
      case b => fail(s"[10] Expected a BV << with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun11") match {
      case BVLShiftRight(`i32`, `j32`) => // OK
      case b => fail(s"[11] Expected a BV >>> with explicit cast, got '$b'")
    }

    /*
     * funDefBody("Shifts.fun12") match {
     *   case b => fail(s"Unexpected, got '$b'")
     * }
     */

    funDefBody("Shifts.fun13") match {
      case BVShiftLeft(`i64`, BVWideningCast(BVWideningCast(`j8`, Int32Type()), Int64Type())) => // OK
      case b => fail(s"[13] Expected a BV << with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun14") match {
      case BVLShiftRight(`i64`, BVWideningCast(BVWideningCast(`j16`, Int32Type()), Int64Type())) => // OK
      case b => fail(s"[14] Expected a BV >>> with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun15") match {
      case BVAShiftRight(`i64`, BVWideningCast(`j32`, Int64Type())) => // OK
      case b => fail(s"[15] Expected a BV >> with explicit cast, got '$b'")
    }

    funDefBody("Shifts.fun16") match {
      case BVShiftLeft(`i64`, `j64`) => // OK
      case b => fail(s"[16] Expected a BV << with explicit cast, got '$b'")
    }
  }

  test("Explicit cast on arithmetic operations involving only bytes") {
    funDefBody("Bytes.foo") match {
      case Plus(BVWideningCast(`i8`, Int32Type()), BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"Expected a BV addition with widening cast, got '$b'")
    }

    funDefBody("Bytes.bar") match {
      case BVAnd(BVWideningCast(`i8`, Int32Type()), BVWideningCast(`j8`, Int32Type())) => // OK
      case b => fail(s"Expected a BV `&` with widening cast, got '$b'")
    }

    funDefBody("Bytes.gun") match {
      case UMinus(BVWideningCast(`i8`, Int32Type())) => // OK
      case b => fail(s"Expected a BV unary minus with widening cast, got '$b'")
    }

    funDefBody("Bytes.hun") match {
      case BVWideningCast(`i8`, Int32Type()) => // OK
      case b => fail(s"Expected a BV unary + (which is dropped) with widening cast, got '$b'")
    }
  }

  test("Explicit casts should be preserved") {
    funDefBody("ExplicitCast.foo1") match {
      case FunCall("bar", Seq(BVNarrowingCast(`i32`, Int8Type()))) => // OK
      case b => fail(s"Expected a function call with one narrowing cast on its only argument, got '$b'")
    }

    funDefBody("ExplicitCast.foo2") match {
      case FunCall("bar", Seq(BVNarrowingCast(BVNarrowingCast(`i64`, Int16Type()), Int8Type()))) => // OK
      case b => fail(s"Expected a function call with one narrowing cast on its only argument, got '$b'")
    }
  }

  test("Implicit casts should be preserved") {
    funDefBody("ImplicitCast.foo1") match {
      case FunCall("bar1", Seq(BVWideningCast(`i8`, Int32Type()))) => // OK
      case b => fail(s"Expected a function call with one widening cast on its only argument, got '$b'")
    }

    funDefBody("ImplicitCast.foo2") match {
      case FunCall("bar1", Seq(BVWideningCast(`i16`, Int32Type()))) => // OK
      case b => fail(s"Expected a function call with one widening cast on its only argument, got '$b'")
    }

    funDefBody("ImplicitCast.foo3") match {
      case FunCall("bar2", Seq(BVWideningCast(`i16`, Int64Type()))) => // OK
      case b => fail(s"Expected a function call with one widening cast on its only argument, got '$b'")
    }
  }
}
