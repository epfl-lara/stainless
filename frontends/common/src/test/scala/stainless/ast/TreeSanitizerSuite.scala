/* Copyright 2009-2021 EPFL, Lausanne */
package stainless
package ast

import scala.language.experimental.macros
import org.scalatest.funspec.AnyFunSpec

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}

class TreeSanitizerSuite extends AnyFunSpec with InputUtils {

  def getFileContents(file: String): String = scala.io.Source.fromFile(file).mkString

  val sources = Map(
    "AbstractValOverrides" -> getFileContents(
      "frontends/common/src/test/resources/AbstractValOverrides.scala"
    ),
    "GhostOverrides" -> getFileContents(
      "frontends/common/src/test/resources/GhostOverrides.scala"
    ),
    "SoundEquality" -> getFileContents(
      "frontends/common/src/test/resources/SoundEquality.scala"
    ),
    "SoundInvariants" -> getFileContents(
      "frontends/common/src/test/resources/SoundInvariants.scala"
    )
  )

  makeTest("AbstractValOverrides",  Seq())
  makeTest("GhostOverrides",        Seq(19))
  makeTest("SoundEquality",         Seq(20, 40, 46, 68, 80, 89, 98))
  makeTest("SoundInvariants",       Seq(11, 22, 45))

  def makeTest(name: String, expected: Seq[Int]): Unit = {
    val ctx: inox.Context = stainless.TestContext.empty
    import ctx.given
    val (_, program) = load(Seq(sources(name)), sanitize = false)

    val errors = TreeSanitizer(xt).check(program.symbols)

    // errors.sortBy(_.tree.getPos).foreach { err =>
    //   println(s"${err.tree.getPos.fullString}")
    //   println(s"${err.getMessage}")
    //   println(s"${err.tree}")
    //   println()
    // }

    describe(s"$name check") {
      it(s"compiles successfully") {
        assert(!program.symbols.functions.isEmpty)
      }

      it(s"yields exactly ${expected.length} errors") {
        assert(errors.length == expected.size)
      }

      errors
        .zipWithIndex
        .filter { case (err, i) => i < expected.length }
        .foreach { case (err, i) =>
          val line = expected(i)
          it(s"yields an error at line $line") {
            assert(err.tree.getPos.line == line)
          }
        }

      it(s"does not yield any other errors") {
        errors
          .zipWithIndex
          .filter { case (err, i) => i >= expected.length }
          .foreach { case (err, _) =>
              assert(false, s"Unexpected error yielded at ${err.tree.getPos}: ${err.getMessage}")
          }
      }
    }
  }
}
