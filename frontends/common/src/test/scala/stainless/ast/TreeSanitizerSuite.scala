/* Copyright 2009-2019 EPFL, Lausanne */
package stainless
package ast

import scala.language.experimental.macros
import org.scalatest._

import stainless.macros.FileProvider
import stainless.extraction.xlang.{trees => xt, TreeSanitizer}

class TreeSanitizerSuite extends FunSpec with InputUtils {

  val ID = 2 // Change this to trigger re-compilation

  val sources = Map(
    "AbstractValOverrides" -> FileProvider.getFileContents(
      "frontends/common/src/test/resources/AbstractValOverrides.scala"
    ),
    "GhostOverrides" -> FileProvider.getFileContents(
      "frontends/common/src/test/resources/GhostOverrides.scala"
    ),
    "SoundEquality" -> FileProvider.getFileContents(
      "frontends/common/src/test/resources/SoundEquality.scala"
    ),
    "SoundInvariants" -> FileProvider.getFileContents(
      "frontends/common/src/test/resources/SoundInvariants.scala"
    )
  )

  makeTest("AbstractValOverrides",  Seq(26, 29, 31))
  makeTest("GhostOverrides",        Seq(19))
  makeTest("SoundEquality",         Seq(20, 40, 46, 68, 80, 89, 98))
  makeTest("SoundInvariants",       Seq(11, 22, 45, 57))

  def makeTest(name: String, expected: Seq[Int]): Unit = {
    implicit val ctx = stainless.TestContext.empty
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
