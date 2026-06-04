/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import org.scalatest.funspec.AnyFunSpec
import org.scalatest.matchers.should.Matchers._

import extraction.imperative
import extraction.utils.NamedPipeline

class AntiAliasingSuite extends AnyFunSpec with InputUtils {

  private val ctx: inox.Context = stainless.TestContext.empty
  import ctx.given

  private def antiAliasingSymbols(code: String): imperative.trees.Symbols = {
    val (_, program) = load(Seq(code))
    val pipeline =
      extraction.xlang.extractor `andThen`
      extraction.innerclasses.extractor `andThen`
      extraction.methods.extractor `andThen`
      extraction.throwing.extractor `andThen`
      NamedPipeline("EffectElaboration", imperative.EffectElaboration(imperative.trees)) `andThen`
      NamedPipeline("AntiAliasing", imperative.AntiAliasing(imperative.trees))

    val (symbols, _) = pipeline.extract(program.symbols)
    symbols.ensureWellFormed
    symbols
  }

  describe("AntiAliasing") {
    it("should not introduce unused mutable match bindings") {
      val symbols = antiAliasingSymbols(
        """import stainless.annotation.*
          |object SwapInstanceOf:
          |
          |  case class Cell[@mutable T](var v: T)
          |
          |  sealed trait List
          |  case class Cons(next: Cell[List]) extends List
          |  case class Nil() extends List
          |
          |  def change(l: List): Unit =
          |    l match
          |      case Nil() => ()
          |      case Cons(n) => ()
          |""".stripMargin
      )

      val change = symbols.functions.values.find(_.id.name == "change")
        .getOrElse(fail("Could not find change after AntiAliasing"))

      change.fullBody.asString should not include "asInstanceOf[Cons].next"
    }
  }
}
