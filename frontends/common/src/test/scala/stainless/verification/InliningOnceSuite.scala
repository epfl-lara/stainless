/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class InliningOnceSuite extends FunSpec with InputUtils {

  describe("with @inlineOnce only, inlining") {
    val source =
      """|import stainless.lang._
         |import stainless.annotation._
         |
         |object Test {
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

    val ctx = stainless.TestContext.empty
    val (funs, xlangProgram) = load(ctx, List(source))
    val program = VerificationComponent.extract(xlangProgram, ctx)

    import program.trees._

    val foo = program.lookup[FunDef]("Test.foo")
    val bar = program.lookup[FunDef]("Test.bar")
    val baz = program.lookup[FunDef]("Test.baz")

    it("should occur in foo") {
      assert(program.symbols.transitiveCallees(foo).map(_.id) == Set(foo.id))
    }

    it("should occur in bar") {
      assert(program.symbols.transitiveCallees(bar).map(_.id) == Set(bar.id))
    }

    it("should occur in baz") {
      assert(program.symbols.transitiveCallees(baz).map(_.id) == Set(baz.id))
    }
  }

  describe("with @inlineOnce and @synthetic, inlining") {
    val source =
      """|import stainless.lang._
         |import stainless.annotation._
         |
         |object Test {
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

    val ctx = stainless.TestContext.empty
    val (funs, xlangProgram) = load(ctx, List(source))

    val annFuns = xlangProgram.symbols.functions.values.map {
      case fd if fd.id.name == "foo" || fd.id.name == "bar" => fd.copy(flags = fd.flags ++ Seq(xlangProgram.trees.Synthetic))
      case fd => fd
    }.toSeq

    val annProgram = inox.Program(xlangProgram.trees)(xlangProgram.symbols.withFunctions(annFuns))
    val program = VerificationComponent.extract(annProgram, ctx)

    import program.trees._

    it("should make foo disappear") {
      assert(program.symbols.lookup.get[FunDef]("Test.foo").isEmpty)
    }

    it("should make bar disappear") {
      assert(program.symbols.lookup.get[FunDef]("Test.bar").isEmpty)
    }

    it("should keep baz") {
      assert(program.symbols.lookup.get[FunDef]("Test.baz").isDefined)
    }
  }

}
