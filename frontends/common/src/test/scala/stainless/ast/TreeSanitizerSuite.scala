/* Copyright 2009-2019 EPFL, Lausanne */
package stainless
package ast

import scala.language.experimental.macros
import org.scalatest._

import stainless.macros.FileProvider
import stainless.extraction.xlang.{trees => xt, TreeSanitizer}

class TreeSanitizerSuite extends FunSuite with InputUtils {

  // Change this to trigger re-compilation
  val ID = 2

  val sources = List(
    FileProvider.getFileContents(
      "frontends/common/src/test/resources/SoundEquality.scala"
    )
  )

  implicit val ctx = stainless.TestContext.empty
  val (_, program) = load(sources, sanitize = false)

  val errors = TreeSanitizer(xt).check(program.symbols)

  // errors.sortBy(_.tree.getPos).foreach { err =>
  //   println(s"${err.tree.getPos.fullString}")
  //   println(s"${err.getMessage}")
  //   println(s"${err.tree}")
  //   println()
  // }

  val expected = Map(
    0 -> 20,
    1 -> 40,
    2 -> 46,
    3 -> 68,
    4 -> 80,
    5 -> 89,
    6 -> 98,
  )

  test(s"SoundEquality test file compiles successfully") {
    assert(!program.symbols.functions.isEmpty)
  }

  test(s"SoundEquality check yield exactly ${expected.size} errors") {
    assert(errors.length == expected.size)
  }

  errors.zipWithIndex foreach {
    case (err, i) if expected.contains(i) =>
      val line = expected(i)
      test(s"SoundEquality check yields an error at line $line") {
        assert(err.tree.getPos.line == line)
      }

    case (err, _) =>
      test(s"SoundEquality check does not yield any other errors") {
        assert(false, s"Unexpected error yielded at ${err.tree.getPos}: ${err.getMessage}")
      }
  }
}
