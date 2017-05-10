/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package ast

import org.scalatest._

class ExplicitNumericPromotionSuite extends FunSuite with InputUtils {
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
       |  def gun(i: Short, j: Long) = i << j
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
       |  def foo1(i: Int) = bar(i.toByte)
       |  def foo2(i: Long) = bar(i.toShort.toByte)
       |
       |  def bar(i: Byte) = i
       |
       |} """.stripMargin,

    """|object ImplicitCast {
       |
       |  def foo1(i: Byte) = bar1(i) // implicit i.toInt here
       |  def foo2(i: Short) = bar1(i) // implicit i.toInt here
       |  def foo3(i: Short) = bar2(i) // implicit i.toLong here
       |
       |  def bar1(i: Int) = i
       |  def bar2(i: Long) = i
       |
       |} """.stripMargin
  )

  val ctx = inox.TestContext.empty
  val (_, xlangProgram) = load(ctx, sources)
  val program = verification.VerificationComponent.extract(xlangProgram)

  import program.trees._

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
    def getType(implicit s: Symbols): Type = typ

    override def equals(o: Any) = o match {
      case Var(`name`, `typ`) => true
      case _ => false
    }
  }

  val i8  = V("i", Int8Type)
  val j8  = V("j", Int8Type)
  val i16 = V("i", Int16Type)
  val j16 = V("j", Int16Type)
  val i32 = V("i", Int32Type)
  val j32 = V("j", Int32Type)
  val i64 = V("i", Int64Type)
  val j64 = V("j", Int64Type)


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
      case Plus(`i32`, BVWideningCast(`j8`, Int32Type)) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("IntByte.bar") match {
      case BVAnd(`i32`, BVWideningCast(`j8`, Int32Type)) => // OK
      case b => fail(s"Expected a BV `&` with explicit cast, got '$b'")
    }

    // Test symmetry
    funDefBody("ByteInt.foo") match {
      case Plus(BVWideningCast(`i8`, Int32Type), `j32`) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("ByteInt.bar") match {
      case BVAnd(BVWideningCast(`i8`, Int32Type), `j32`) => // OK
      case b => fail(s"Expected a BV `&` with explicit cast, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving ints & shorts") {
    funDefBody("IntShort.foo") match {
      case Plus(`i32`, BVWideningCast(`j16`, Int32Type)) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("IntShort.bar") match {
      case BVAnd(`i32`, BVWideningCast(`j16`, Int32Type)) => // OK
      case b => fail(s"Expected a BV addition with explicit casts, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving bytes & shorts") {
    funDefBody("ByteShort.foo") match {
      case Plus(BVWideningCast(`i8`, Int32Type), BVWideningCast(`j16`, Int32Type)) => // OK
      case b => fail(s"Expected a BV addition with explicit casts, got '$b'")
    }
  }

  test("Explicit cast on binary arithmetic operations involving Long and other types") {
    funDefBody("MixWithLong.foo") match {
      case Plus(`i64`, BVWideningCast(`j32`, Int64Type)) => // OK
      case b => fail(s"Expected a BV addition with explicit cast, got '$b'")
    }

    funDefBody("MixWithLong.bar") match {
      case BVOr(BVWideningCast(`i8`, Int64Type), `j64`) => // OK
      case b => fail(s"Expected a BV `|` with explicit cast, got '$b'")
    }

    funDefBody("MixWithLong.gun") match {
      case BVShiftLeft(BVWideningCast(`i16`, Int32Type), `j64`) => // OK
      case b => fail(s"Expected a BV << with explicit cast, got '$b'")
    }
  }

  test("Explicit cast on arithmetic operations involving only bytes") {
    funDefBody("Bytes.foo") match {
      case Plus(BVWideningCast(`i8`, Int32Type), BVWideningCast(`j8`, Int32Type)) => // OK
      case b => fail(s"Expected a BV addition with widening cast, got '$b'")
    }

    funDefBody("Bytes.bar") match {
      case BVAnd(BVWideningCast(`i8`, Int32Type), BVWideningCast(`j8`, Int32Type)) => // OK
      case b => fail(s"Expected a BV `&` with widening cast, got '$b'")
    }

    funDefBody("Bytes.gun") match {
      case UMinus(BVWideningCast(`i8`, Int32Type)) => // OK
      case b => fail(s"Expected a BV unary minus with widening cast, got '$b'")
    }

    funDefBody("Bytes.hun") match {
      case BVWideningCast(`i8`, Int32Type) => // OK
      case b => fail(s"Expected a BV unary + (which is dropped) with widening cast, got '$b'")
    }
  }

  test("Explicit casts should be preserved") {
    funDefBody("ExplicitCast.foo1") match {
      case FunCall("bar", Seq(BVNarrowingCast(`i32`, Int8Type))) => // OK
      case b => fail(s"Expected a function call with one narrowing cast on its only argument, got '$b'")
    }

    funDefBody("ExplicitCast.foo2") match {
      case FunCall("bar", Seq(BVNarrowingCast(BVNarrowingCast(`i64`, Int16Type), Int8Type))) => // OK
      case b => fail(s"Expected a function call with one narrowing cast on its only argument, got '$b'")
    }
  }

  test("Implicit casts should be preserved") {
    funDefBody("ImplicitCast.foo1") match {
      case FunCall("bar1", Seq(BVWideningCast(`i8`, Int32Type))) => // OK
      case b => fail(s"Expected a function call with one widening cast on its only argument, got '$b'")
    }

    funDefBody("ImplicitCast.foo2") match {
      case FunCall("bar1", Seq(BVWideningCast(`i16`, Int32Type))) => // OK
      case b => fail(s"Expected a function call with one widening cast on its only argument, got '$b'")
    }

    funDefBody("ImplicitCast.foo3") match {
      case FunCall("bar2", Seq(BVWideningCast(`i16`, Int64Type))) => // OK
      case b => fail(s"Expected a function call with one widening cast on its only argument, got '$b'")
    }
  }

}

