/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest.funspec.AnyFunSpec

class InliningOnceSuite extends AnyFunSpec with InputUtils {

  describe("with @inlineOnce only, inlining") {
    val source =
      """|import stainless.lang._
         |import stainless.annotation._
         |
         |object Test {
         |  @inlineOnce
         |  def loop(x: BigInt): BigInt = {
         |    loop(x + 1)
         |  }
         |
         |  @inlineOnce
         |  def foo(x: BigInt): BigInt = {
         |    bar(x + 1)
         |  }
         |
         |  @inlineOnce
         |  def bar(y: BigInt): BigInt = {
         |    baz(y * 2)
         |  }
         |
         |  @inlineOnce
         |  def baz(z: BigInt): BigInt = {
         |    foo(z / 10)
         |  }
         |}""".stripMargin

    implicit val ctx = stainless.TestContext.empty
    val (funs, xlangProgram) = load(List(source))
    val run = VerificationComponent.run(extraction.pipeline)
    val program = inox.Program(run.trees)(run extract xlangProgram.symbols)

    import stainless.trees._

    val loop = program.lookup[FunDef]("Test.loop")
    val foo = program.lookup[FunDef]("Test.foo")
    val bar = program.lookup[FunDef]("Test.bar")
    val baz = program.lookup[FunDef]("Test.baz")

    it("should occur in loop") {
      assert(exprOps.exists { e => e.isInstanceOf[Let] }(loop.fullBody))
    }

    it("should occur in foo") {
      assert(exprOps.exists { e => e.isInstanceOf[Let] }(foo.fullBody))
    }

    it("should occur in bar") {
      assert(exprOps.exists { e => e.isInstanceOf[Let] }(bar.fullBody))
    }

    it("should occur in baz") {
      assert(exprOps.exists { e => e.isInstanceOf[Let] }(baz.fullBody))
    }
  }

  describe("with @inlineOnce and @opaque, inlining") {
    val source =
      """|import stainless.lang._
         |import stainless.annotation._
         |
         |object Test {
         |  @inlineOnce @opaque
         |  def foo(x: BigInt): BigInt = {
         |    bar(x + 1)
         |  }
         |
         |  @inlineOnce @opaque
         |  def bar(y: BigInt): BigInt = {
         |    baz(y * 2)
         |  }
         |
         |  @inlineOnce
         |  def baz(z: BigInt): BigInt = {
         |    foo(z / 10)
         |  }
         |}""".stripMargin

    implicit val ctx = stainless.TestContext.empty
    val (funs, xlangProgram) = load(List(source))
    val run = VerificationComponent.run(extraction.pipeline)
    val program = inox.Program(run.trees)(run extract xlangProgram.symbols)

    import stainless.trees._

    val foo = program.lookup[FunDef]("Test.foo")
    val bar = program.lookup[FunDef]("Test.bar")
    val baz = program.lookup[FunDef]("Test.baz")

    it("should make foo have a body without function calls") {
      assert(program.symbols.callees(foo).isEmpty)
    }

    it("should make baz have a body without function calls") {
      assert(program.symbols.callees(foo).isEmpty)
    }

    it("should make the body of bar have two levels of inlining") {
      assert(exprOps.exists {
        case Let(_, e, _) => e.isInstanceOf[Times] //  y * 2
        case _ => false
      }(bar.fullBody))
      assert(exprOps.exists {
        case Let(_, e, _) => e.isInstanceOf[Division] //  z / 10
        case _ => false
      }(bar.fullBody))
    }
  }

}
