/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package ast

import org.scalatest._

class LibraryLookupSuite extends FunSuite with InputUtils {

  val contents = """
    import stainless.lang._
    import stainless.collection._

    object Test {
      case class Toto(val a: Int)
      def Toto(a: Int): Int = 1
    }
  """

  implicit val ctx = stainless.TestContext.empty
  val (_, xlangProgram) = load(Seq(contents))
  val run = verification.VerificationComponent.run(extraction.pipeline)
  val program = inox.Program(stainless.trees)(run extract xlangProgram.symbols)
  import program.trees._

  test("Lookup Option classes") {
    val option = program.lookup[ADTSort]("stainless.lang.Option")
    val Seq(none, some) = option.constructors.sortBy(_.fields.size)

    assert(option.constructors.map(_.id).toSet == Set(some.id, none.id))
    assert(some.sort == option.id)
    assert(none.sort == option.id)

    assert(some.fields.size == 1)
    assert(none.fields.isEmpty)
  }

  test("Lookup Option functions") {
    val get = program.lookup[FunDef]("stainless.lang.Option.get")

    // After method-lifting, get takes `thiss` as argument
    assert(get.tparams.size == 1)
    assert(get.params.size == 1)
  }

  test("Lookup List classes") {
    val list = program.lookup[ADTSort]("stainless.collection.List")
    val Seq(nil, cons) = list.constructors.sortBy(_.fields.size)

    assert(list.constructors.map(_.id).toSet == Set(cons.id, nil.id))
    assert(cons.sort == list.id)
    assert(nil.sort == list.id)

    assert(cons.fields.size == 2)
    assert(nil.fields.isEmpty)
  }

  test("Lookup List functions") {
    val size = program.lookup[FunDef]("stainless.collection.List.size")
    val contains = program.lookup[FunDef]("stainless.collection.List.contains")

    // After method-lifting, size takes `thiss` as argument
    assert(size.tparams.size == 1)
    assert(size.params.size == 1)

    // After method-lifting, contains takes `thiss` and `v` as arguments
    assert(contains.tparams.size == 1)
    assert(contains.params.size == 2)
  }

  test("Lookup by definition type") {
    program.lookup[ADTSort]("stainless.collection.List")
  }

  test("Lookup non-library stuff") {
    program.lookup[ADTSort]("Test.Toto")
    program.lookup[FunDef]("Test.Toto")
  }

  test("lookup fails when looking up inexistent stuff") {
    try {
      program.lookup[ADTSort]("stainless.collection.List2")
      fail("Expected to throw exception")
    } catch {
      case _: ADTLookupException => // ok
    }
  }
}
