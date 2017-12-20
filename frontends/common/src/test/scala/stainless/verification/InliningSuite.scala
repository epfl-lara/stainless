/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class InliningSuite extends FunSuite with InputUtils {

  val source =
    """|import stainless.lang._
       |import stainless.annotation._
       |
       |object Test {
       |  def fun1(x: BigInt): BigInt = fun2(x, BigInt(0)) ensuring (_ >= BigInt(0))
       |
       |  @inline
       |  def fun2(x: BigInt, y: BigInt): BigInt = {
       |    if (x < 0 || y < 0) {
       |      BigInt(0)
       |    } else {
       |       val s = sum(x, y)
       |       assert(s >= BigInt(0))
       |       s
       |    }
       |  } ensuring (_ >= BigInt(0))
       |
       |  @inline
       |  def sum(x: BigInt, y: BigInt): BigInt = {
       |    require(x >= BigInt(0) && y >= BigInt(0))
       |    x + y
       |  } ensuring (_ >= BigInt(0))
       |}""".stripMargin

  val ctx = stainless.TestContext.empty
  val (funs, xlangProgram) = load(ctx, List(source))
  val program = VerificationComponent.extract(xlangProgram, ctx)

  import program.trees._

  test("Inlining should occur in fun1") {
    val fun1 = program.lookup[FunDef]("Test.fun1")
    assert(program.symbols.transitiveCallees(fun1).isEmpty)
  }

  test("Inlining should occur in fun2") {
    val fun2 = program.lookup[FunDef]("Test.fun2")
    assert(program.symbols.transitiveCallees(fun2).isEmpty)
  }

  test("Conditions of inlined functions should not be checked") {
    val fun1 = program.lookup[FunDef]("Test.fun1")
    val vcs = VerificationGenerator.gen(program, ctx)(Seq(fun1.id))
    assert(vcs.size == 1)
  }

  test("Precondition of inlined functions should be checked") {
    val fun2 = program.lookup[FunDef]("Test.fun2")
    val vcs = VerificationGenerator.gen(program, ctx)(Seq(fun2.id))
    assert(vcs.size == 3)
  }
}
