/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import org.scalatest.funsuite.AnyFunSuite
import extraction.methods.trees.Library

class LawsLibrarySuite extends AnyFunSuite with InputUtils {

  val sources = List(
    """|import stainless.lang._
       |import stainless.proof._
       |import stainless.collection._
       |import stainless.annotation._
       |
       |@library
       |sealed abstract class CommutativeBigInt {
       |  def append(x: BigInt, y: BigInt): BigInt
       |
       |  @law
       |  def law_commutative(x: BigInt, y: BigInt): Boolean = {
       |    append(x, y) == append(y, x)
       |  }
       |}
       |
       |@library
       |sealed abstract class AssociativeBigInt extends CommutativeBigInt {
       |  @law
       |  def law_associative(x: BigInt, y: BigInt, z: BigInt): Boolean = {
       |    append(append(x, y), z) == append(x, append(y, z))
       |  }
       |}
       |
       |@library
       |case class LibraryBigInt() extends AssociativeBigInt {
       |  def append(x: BigInt, y: BigInt): BigInt = x + y
       |}
       |
       |case class UserBigInt() extends AssociativeBigInt {
       |  def append(x: BigInt, y: BigInt): BigInt = x + y + List[Int]().length
       |}
       |""".stripMargin)

  val ctx: inox.Context = stainless.TestContext.empty
  import ctx.given
  val (_, xlangProgram) = load(sources)

  val libraryBigInt = xlangProgram.symbols.classes.values.find(_.id.name == "LibraryBigInt").get
  val libraryAppend = libraryBigInt.methods(using xlangProgram.symbols)
    .find(_.name == "append")
    .map(xlangProgram.symbols.getFunction)
    .get

  def pipeline = {
    extraction.xlang.extractor        andThen
    extraction.innerclasses.extractor andThen
    extraction.methods.Laws(extraction.methods.trees)
  }

  val symbols = pipeline extract xlangProgram.symbols

  test("LibraryBigInt#append has @library flag before extraction") {
    assert(libraryAppend.flags.contains(xlangProgram.trees.Library))
  }

  test("LibraryBigInt#append still has @library flag after extraction") {
    val libraryBigInt = symbols.classes.values.find(_.id.name == "LibraryBigInt").get

    val libraryAppend = libraryBigInt.methods(using symbols)
      .find(_.name == "append")
      .map(symbols.getFunction)
      .get

    assert(libraryAppend.flags.contains(Library))
  }

  test("Remove library flag from library laws that have non-library subclasses") {
    val userBigInt = symbols.classes.values.find(_.id.name == "UserBigInt").get

    val law_commutative = userBigInt.methods(using symbols)
      .find(_.name == "law_commutative")
      .map(symbols.getFunction)
      .get

    val law_associative = userBigInt.methods(using symbols)
      .find(_.name == "law_associative")
      .map(symbols.getFunction)
      .get

    assert(!law_commutative.flags.contains(Library))
    assert(!law_associative.flags.contains(Library))
  }

  test("Don't remove library flag from library case classes that have non-library siblings") {
    val libraryBigInt = symbols.classes.values.find(_.id.name == "LibraryBigInt").get

    val law_commutative = libraryBigInt.methods(using symbols)
      .find(_.name == "law_commutative")
      .map(symbols.getFunction)
      .get

    val law_associative = libraryBigInt.methods(using symbols)
      .find(_.name == "law_associative")
      .map(symbols.getFunction)
      .get

    assert(law_commutative.flags.contains(Library))
    assert(law_associative.flags.contains(Library))
  }

  test("Don't remove library flag from library functions that are used in non-library methods") {
    val fd = symbols.functions.values.find(_.id.name == "length").get
    assert(fd.flags.contains(Library))
  }
}
