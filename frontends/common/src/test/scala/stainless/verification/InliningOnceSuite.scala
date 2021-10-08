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

    val ctx: inox.Context = stainless.TestContext.empty
    import ctx.given
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

}
