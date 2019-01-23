
package stainless.utils

import org.scalatest.FunSuite

/**
 * Test the [[IncrementalComputationalGraph]] using some basic node: a symbol-id pair.
 */
class TestIncrementalComputationalGraph extends FunSuite {

  private val mainId = "main"
  private val fooId = "foo"
  private val barId = "bar"
  private val bazId = "baz"
  private val recAId = "recA"
  private val recBId = "recB"
  private val recXId = "recX"
  private val recYId = "recY"
  private val recZId = "recZ"
  private val extId = "ext"
  private val lambdaId = "lambda"

  private type Input = (Symbol, String)
  private val main = 'main -> mainId
  private val foo1 = 'foo1 -> fooId
  private val foo2 = 'foo2 -> fooId
  private val foo3 = 'foo3 -> fooId
  private val bar = 'bar -> barId
  private val baz = 'baz -> bazId
  private val recA = 'recA -> recAId
  private val recB = 'recB -> recBId

  private val recX1 = 'recX1 -> recXId
  private val recX2 = 'recX2 -> recXId
  private val recY1 = 'recY1 -> recYId
  private val recY2 = 'recY2 -> recYId
  private val recZ = 'recZ -> recZId
  private val ext = 'ext -> extId
  private val lambda = 'lambda -> lambdaId

  private val directDependencies = Map[Input, Set[String]](
    main -> Set(fooId),
    foo1 -> Set(barId),
    foo2 -> Set(barId),
    foo3 -> Set(bazId),
    bar -> Set.empty,
    baz -> Set.empty,
    recA -> Set(recBId),
    recB -> Set(recAId),
    recX1 -> Set(recYId),
    recX2 -> Set(recYId, recZId),
    recY1 -> Set(recXId),
    recY2 -> Set(recXId, lambdaId),
    recZ -> Set(recXId),
    ext -> Set(recXId),
    lambda -> Set.empty
  )

  private class Eval {
    private val seq = scala.collection.mutable.ListBuffer[Set[Input]]()
    private val current = scala.collection.mutable.Set[Input]()

    def push(): Unit = current.clear()
    def pop(): Unit = seq += current.toSet

    // No real computation, just checking that the right dependencies are here.
    def eval(nodes: Set[(String, Input)]): Unit = {
      current ++= nodes map { _._2 }
    }

    def getSeq: Seq[Set[Input]] = seq
  }

  private def testSequence(name: String, inputs: Seq[Input], expected: Seq[Set[Input]]): Unit = test(name) {
    val e = new Eval
    val g = new IncrementalComputationalGraph[String, Input, Unit] {
      override def compute(ready: Set[(String, Input)]): Unit = e.eval(ready)
      override def equivalent(id: String, deps: Set[String], oldInput: Input, newInput: Input): Boolean = {
        oldInput._1 == newInput._1
      }
    }

    inputs foreach { fd =>
      e.push()
      g.update(fd._2, fd, directDependencies(fd), compute = true)
      e.pop()
    }

    val result = e.getSeq

    assert(result.size == expected.size, "sizes of expected data and results don't match")
    (result zip expected).zipWithIndex foreach { case ((res, exp), i) =>
      assert(res == exp, s"error at index $i")
    }
  }

  private def testSequence(name: String, ie: Seq[(Input, Set[Input])]): Unit = {
    val (inputs, expected) = ie.unzip
    testSequence(name, inputs, expected)
  }

  testSequence("empty", Seq.empty, Seq.empty)
  testSequence("foo1.a", Seq(main, foo1, bar), Seq(Set(), Set(), Set(main, foo1, bar)))
  testSequence("foo1.b", Seq(main, bar, foo1), Seq(Set(), Set(bar), Set(main, foo1, bar)))
  testSequence("foo1.c", Seq(bar, main, foo1), Seq(Set(bar), Set(), Set(main, foo1, bar)))
  testSequence("foo1.d", Seq(bar, bar, main, foo1), Seq(Set(bar), Set(), Set(), Set(main, foo1, bar)))
  testSequence("foo1.e", Seq(bar, bar, main, main, foo1, bar),
                         Seq(Set(bar), Set(), Set(), Set(), Set(main, foo1, bar), Set()))
  testSequence("foo2.a", Seq(main, foo2, bar), Seq(Set(), Set(), Set(main, foo2, bar)))
  testSequence("foo2.b", Seq(main, foo2, bar, baz), Seq(Set(), Set(), Set(main, foo2, bar), Set(baz)))
  testSequence("foo2-1", Seq(main, foo2, bar, foo1), Seq(Set(), Set(), Set(main, foo2, bar), Set(main, foo1, bar)))
  testSequence("foo3.a", Seq(main, foo3, bar, baz), Seq(Set(), Set(), Set(bar), Set(main, foo3, baz)))
  testSequence("foo3-1", Seq(main, foo3, bar, baz, foo1),
                         Seq(Set(), Set(), Set(bar), Set(main, foo3, baz), Set(main, foo1, bar)))
  //                                                sent to [[compute]] as a dependency.   ^^^


  testSequence("recursive.a", Seq(recA, recB), Seq(Set(), Set(recA, recB)))
  testSequence("recursive.b", Seq(recA, recB, recA), Seq(Set(), Set(recA, recB), Set()))

  testSequence("recursive.c", Seq(recY1, recX1, recZ, ext, recX2),
                              Seq(
                                Set(),
                                Set(recY1, recX1),
                                Set(recZ, /* + deps: */ recX1, recY1),
                                Set(ext, /* + deps: */ recX1, recY1),
                                Set(recX2, recY1, recZ, ext)
                              ))

  testSequence("recursive.d", Seq(recZ, recY1, recX2), Seq(Set(), Set(), Set(recZ, recY1, recX2)))
  testSequence("recursive.e", Seq(
    recX1 -> Set.empty,
    recY1 -> Set(recX1, recY1),
    recZ -> Set(recX1, recY1, recZ),
    ext -> Set(ext, recX1, recY1),
    recX2 -> Set(recX2, recY1, recZ, ext),
    recY2 -> Set.empty,
    lambda -> Set(recX2, recY2, recZ, lambda, ext),
    recX1 -> Set(recX1, recY2, recZ, ext, lambda),
    recX1 -> Set()
  ))

  test("removal of nodes & compute = false") {
    // Using simple String for both Id and Input. Result is a set of ids.
    val g = new IncrementalComputationalGraph[String, String, Set[String]] {
      override def compute(ready: Set[(String, String)]): Set[String] = ready map { _._1 }
      override def equivalent(id: String, deps: Set[String], oldInput: String, newInput: String): Boolean = {
        false // always recompute
      }
    }

    assert(g.update("a", "a", Set.empty, compute = true) == Some(Set("a")), "a should be computed")
    assert(g.update("a", "a", Set.empty, compute = true) == Some(Set("a")), "a should be re-computed")
    assert(g.update("b", "b", Set("a"), compute = true) == Some(Set("a", "b")), "b should be computed")
    assert(g.update("c", "c", Set("a"), compute = false) == None, "c should not be computed")
    assert(g.update("d", "d", Set.empty, compute = false) == None, "d should not be computed")
    assert(g.update("a", "a", Set.empty, compute = true) == Some(Set("a", "b")), "a & b should be re-computed, but not c")
    assertThrows[java.lang.IllegalArgumentException] { g.remove("e") }
    assert(g.update("a", "a", Set.empty, compute = true) == Some(Set("a", "b")), "a & b should be re-computed, but not c")
    assert(g.update("e", "e", Set("b"), compute = true) == Some(Set("a", "b", "e")), "e should be computed with its deps.")
    assertResult( () ) { g.remove("b") }
    assert(g.update("a", "a", Set.empty, compute = true) == Some(Set("a")), "b's ghost should not be re-computed")
    assert(g.update("b", "b", Set("c"), compute = false) == Some(Set("a", "b", "c", "e")), "e should be re-computed")
    assertResult( () ) { g.remove("b") }
    assert(g.update("b", "b", Set.empty, compute = false) == Some(Set("b", "e")), "e should be re-computed")
    assertResult( () ) { g.remove("b") }
    assert(g.update("e", "e", Set("b"), compute = false) == None, "Nothing should be computed at this stage")
    assert(g.update("b", "b", Set.empty, compute = false) == None, "Nothing should be computed at this stage (bis)")
  }

  test("freeze") {
    // Using simple String for both Id and Input. Result is a set of ids.
    val g = new IncrementalComputationalGraph[String, String, Set[String]] {
      override def compute(ready: Set[(String, String)]): Set[String] = ready map { _._1 }
      override def equivalent(id: String, deps: Set[String], oldInput: String, newInput: String): Boolean = {
        oldInput == newInput
      }
    }

    assert(g.update("a", "a$0", Set.empty, compute = true) == Some(Set("a")), "a should be computed")
    g.freeze()
    assert(g.update("a", "a$1", Set.empty, compute = true) == None, "the graph is frozen")
    assert(g.unfreeze() == Some(Set("a")), "a should be re-computed")
    assert(g.update("b", "b$0", Set("a"), compute = true) == Some(Set("a", "b")), "b should be computed")

    assert(g.update("foobar", "foobar$0", Set("Top"), compute = true) == None, "nothing ready (1)")
    assert(g.update("Top", "Top$0", Set("top_inv", "Bottom"), compute = false) == None, "nothing ready (2)")
    assert(g.update("Bottom", "Bottom$0", Set("Top"), compute = false) == None, "nothing ready (3)")
    assert(g.update("top_inv", "top_inv$0", Set(), compute = true) == Some(Set("foobar", "Top", "Bottom", "top_inv")), "ready")

    g.freeze()
    assert(g.update("Top", "Top$0", Set("top_inv", "Alt"), compute = false) == None, "frozen (1)")
    assert(g.update("Alt", "Alt$0", Set("Top"), compute = false) == None, "frozen (2)")
    assert(g.update("foobar", "foobar$0", Set("Top"), compute = true) == None, "frozen (3)")
    assert(g.update("top_inv", "top_inv$0", Set("Top"), compute = false) == None, "frozen (4)")
    g.remove("Bottom")
    assert(g.unfreeze() == Some(Set("foobar", "Top", "Alt", "top_inv")), "properly re-computed")

    g.freeze()
    assert(g.update("Top", "Top$0", Set("top_inv", "Alt"), compute = false) == None, "frozen (5)")
    assert(g.update("Alt", "Alt$0", Set("Top"), compute = false) == None, "frozen (6)")
    assert(g.update("foobar", "foobar$0", Set("Top"), compute = true) == None, "frozen (7)")
    assert(g.update("top_inv", "top_inv$0", Set("Top"), compute = false) == None, "frozen (8)")
    assert(g.unfreeze() == None, "nothing new")

    g.freeze()
    assert(g.update("Top", "Top$0", Set("top_inv", "Alt"), compute = false) == None, "frozen (9)")
    assert(g.update("Alt", "Alt$0", Set("Top"), compute = false) == None, "frozen (10)")
    assert(g.update("top_inv", "top_inv$1", Set("Top"), compute = false) == None, "frozen (11)")
    assert(g.update("foobar", "foobar$0", Set("Top"), compute = true) == None, "frozen (12)")
    g.remove("a")
    assert(g.unfreeze() == Some(Set("foobar", "Top", "Alt", "top_inv")), "properly re-computed, again")

    g.freeze()
    assert(g.update("a", "a$2", Set(), compute = false) == None, "frozen (13)")
    assert(g.unfreeze() == Some(Set("a", "b")), "re-compute b & a")
  }

  test("extra regression 01") {
    // Using simple String for both Id and Input. Result is a set of ids.
    val g = new IncrementalComputationalGraph[String, String, Set[String]] {
      override def compute(ready: Set[(String, String)]): Set[String] = ready map { _._1 }
      override def equivalent(id: String, deps: Set[String], oldInput: String, newInput: String): Boolean = {
        oldInput == newInput
      }
    }

    assert(g.update("Top", "Top$0", Set("Bottom", "inv", "prop"), compute = false) == None, "Top")
    assert(g.update("Bottom", "Bottom$0", Set("Top"), compute = false) == None, "Bottom")
    assert(g.update("inv", "inv$0", Set("Top"), compute = true) == None, "inv")
    assert(g.update("prop", "prop$0", Set("Top"), compute = true) ==
           Some(Set("prop", "inv", "Top", "Bottom")), "prop")
    assert(g.update("foo", "foo$0", Set("prop", "Top"), compute = true) ==
           Some(Set("foo", "prop", "Top", "Bottom", "inv")), "foo v1")
    g.freeze()
    assert(g.update("Top", "Top$0", Set("Bottom", "inv", "prop"), compute = false) == None, "Top")
    assert(g.update("Bottom", "Bottom$0", Set("Top"), compute = false) == None, "Bottom")
    assert(g.update("inv", "inv$0", Set("Top"), compute = true) == None, "inv")
    assert(g.update("prop", "prop$0", Set("Top"), compute = true) == None, "prop")
    assert(g.update("foo", "foo$1", Set("prop", "Top"), compute = true) == None, "foo v2")
    assert(g.unfreeze() == Some(Set("foo", "prop", "Top", "Bottom", "inv")), "unfreeze")
  }

}


