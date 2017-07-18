
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

    def getSeq: Seq[Set[Input]] = seq.toSeq
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
    (result zip expected).zipWithIndex foreach { case ((r, e), i) =>
      assert(r == e, s"error at index $i")
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

}


