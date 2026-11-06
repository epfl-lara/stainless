import stainless.lang.*

/** An anonymous class whose body uses an unsupported Scala API. */
object AnonymousClassBody:

  /** A class that the anonymous class extends. */
  abstract class Foo:
    def get: BigInt

  /** Uses `scala.collection.immutable.List` inside an anonymous class. */
  def inAnon(): BigInt =
    val foo: Foo = new Foo:
      def get: BigInt =
        val l: scala.collection.immutable.List[Int] = scala.collection.immutable.List(1, 2)
        BigInt(l.size)
    foo.get
