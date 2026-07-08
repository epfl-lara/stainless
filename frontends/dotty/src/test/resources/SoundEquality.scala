
import stainless.lang._
import stainless.annotation._
import stainless.lang.StaticChecks

object TreeSanitizerTest {

  abstract class NonSealed {
    def bar: BigInt
  }

  def foo(outer: BigInt): NonSealed = {
    case class Foo(y: BigInt) extends NonSealed {
      def bar = outer
    }
    Foo(12)
  }

  def oops = {
    assert(foo(1) != foo(2))
  }

  @ghost
  def ok = {
    assert(foo(1) != foo(2))
  }

  sealed abstract class Sealed {
    def bar: BigInt
  }

  def foo2(outer: BigInt): Sealed = {
    case class Foo2(y: BigInt) extends Sealed {
      def bar = outer
    }
    Foo2(12)
  }

  def oops2 = {
    assert(foo2(1) != foo2(2))
  }

  def oops3 = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x
    assert(a == b)
  }

  @ghost
  def ok3 = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x
    assert(a == b)
  }

  def ok3bis = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x
    StaticChecks.assert(a == b)
  }

  def compare(prop: Boolean): Unit = ()
  def compareGhost(@ghost prop: Boolean): Unit = ()

  def oops4 = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x
    compare(a == b)
  }

  def ok4 = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x
    compareGhost(a == b)
  }

  def oops5 = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x
    compare((a, a) == (b, b))
  }

  def oops6 = {
    val a = (x: BigInt) => x
    val b = (x: BigInt) => x

    case class InnerClass() {
      @ghost def innerOk(test: Boolean): Boolean = test && a == b // ok
      def innerBad(@ghost test: Boolean): Boolean = a == b // bad
    }
    StaticChecks.assert(InnerClass().innerOk(a == b)) // ok
    assert(InnerClass().innerBad(a == b)) // ok
  }

  type IAmALambda = Int => Boolean

  def oops7(iamALambdaA: IAmALambda, iamALambdaB: IAmALambda) = {
    iamALambdaA == iamALambdaB // bad
  }

  def oops8[A](optA: Option[A], optB: Option[A]) = {
    optA == optB // bad when PEDANTIC is on
  }
}

