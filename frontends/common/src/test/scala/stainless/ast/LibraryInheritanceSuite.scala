/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import org.scalatest._
import scala.language.existentials
import extraction.methods.trees.Library

class LibraryInheritanceSuite extends FunSuite with InputUtils {

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
       |}""".stripMargin)

  implicit val ctx = stainless.TestContext.empty
  val (_, xlangProgram) = load(sources)

  val libraryBigInt = xlangProgram.symbols.classes.values.find(_.id.name == "LibraryBigInt").get
  val libraryAppend = libraryBigInt.methods(xlangProgram.symbols).map(xlangProgram.symbols.getFunction).find(_.id.name == "append").get

  def pipeline = {
    extraction.xlang.extractor        andThen
    extraction.innerclasses.extractor andThen
    extraction.utils.DebugPipeline("Laws", extraction.methods.Laws(extraction.methods.trees))
  }

  val symbols = pipeline extract xlangProgram.symbols

  test("Remove library flag from library laws that have non-library subclasses") {
    val userBigInt = symbols.classes.values.find(_.id.name == "UserBigInt").get

    val law_commu = userBigInt.methods(symbols).map(symbols.getFunction).find(_.id.name == "law_commutative").get
    val law_asso = userBigInt.methods(symbols).map(symbols.getFunction).find(_.id.name == "law_associative").get

    assert(!law_commu.flags.contains(Library))
    assert(!law_asso.flags.contains(Library))
  }

  test("Don't remove library flag from library case classes that have non-library 'brothers'") {
    val libraryBigInt = symbols.classes.values.find(_.id.name == "LibraryBigInt").get

    val law_commu = libraryBigInt.methods(symbols).map(symbols.getFunction).find(_.id.name == "law_commutative").get
    val law_asso = libraryBigInt.methods(symbols).map(symbols.getFunction).find(_.id.name == "law_associative").get

    assert(libraryAppend.flags.exists(_.name == "library"))
    assert(law_commu.flags.contains(Library))
    assert(law_asso.flags.contains(Library))
  }

  test("Don't remove library flag from library functions that are used in non-library methods") {
    val fd = symbols.functions.values.find(_.id.name == "length").get
    assert(fd.flags.contains(Library))
  }
}
