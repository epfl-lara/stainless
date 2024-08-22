import stainless.lang._
import stainless.annotation._
import stainless.collection._

object NewImpExamples {
  final case class Box(var value: BigInt) extends AnyHeapRef
  final case class BoxBox(var inner: Box) extends AnyHeapRef

  sealed abstract class Op extends AnyHeapRef
  case class Up(var bla: BigInt) extends Op
  case class Down() extends Op

  // @extern def mystery(x: BigInt): Unit = ???

  def f(x: BigInt): BigInt =
    -x

  def g(c: Boolean, x: BigInt): BigInt =
    if (c) f(f(x)) else f(x)

  def h(b: Box): Unit = {
    reads(Set(b))
    modifies(Set(b))
    b.value = g(b.value >= 0, b.value)
  }.ensuring(_ => b.value >= 0)

  // Example inc

  def inc(b: Box): Unit = {
    reads(Set(b))
    modifies(Set(b))
    b.value = b.value + 1
  }.ensuring(_ => b.value > old(b.value))

  // Example accumulate

  def accumulateBox(b1: Box, b2: Box): Unit = {
    reads(Set(b1, b2))
    modifies(Set(b1))
    b1.value += b2.value
  }

  def accumulateBoxBox(bb: BoxBox, b: Box): Unit = {
    reads(Set(bb, bb.inner, b))
    modifies(Set(bb.inner))
    require(b.value > 0)
    accumulateBox(bb.inner, b)
  }.ensuring(_ => bb.inner.value > old(bb.inner.value))

  // Example Ops

  def runOp(b: Box, op: Boolean): Unit = {
    reads(Set(b))
    modifies(Set(b))
    if (op) b.value += 1 else b.value -= 1
  }

  def isWithin(x: BigInt, y: BigInt, k: BigInt): Boolean =
    y - k <= x && x <= y + k

  def runOps(b: Box, ops: List[Boolean]): Unit = {
    reads(Set(b))
    modifies(Set(b))
    ops match {
      case Cons(op, ops) =>
        runOp(b, op)
        runOps(b, ops)
      case _ =>
    }
  }.ensuring(_ => isWithin(b.value, old(b.value), ops.size))


  // TODO(gsps): Add local heap to reason about allocation?

  // def foo1a(op: Op): BigInt =
  //   if (op.isInstanceOf[Up]) 1 else -1

  // def foo2a(): BigInt = {
  //   foo1a(Up(2))
  // }.ensuring(res => res == 1)

  def foo1b(op: Op): BigInt = {
    reads(Set(op))
    op match {
      case Up(_) => 1
      case Down() => -1
      case _ => 0 // TODO(gsps): Assume heap well-typedness in exhaustiveness checks
    }
  }

  // def foo2b(): BigInt = {
  //   foo1b(Up(2))
  // }.ensuring(res => res == 1)


  def bar(box: Box, x: BigInt): Unit = {
    reads(Set(box))
    modifies(Set(box))
    val y = x + 1
    box.value = y
  }

  // // `StateSpec[S]` is a first-class function acting as a two-state spec
  // // It would expand to `(Heap, Heap, S) => Boolean`, and allow `old` to be used.
  // def foreach[T](xs: List[T])(f: T => Unit)(spec: StateSpec[List[T]]): Unit = {
  //   require(f.post ===> spec(xs))
  //   xs match {
  //     case Cons(x, xs) => f(x); foreach(xs)(f)
  //     case _ =>
  //   }
  // }.ensuring(_ => spec(xs))

  // def runOps2(b: Box, ops: List[Boolean]): Unit = {
  //   ops.foreach(op => runOp(b, op))(ops => isWithin(b.value, old(b.value), ops.size))
  // }.ensuring(_ => isWithin(b.value, old(b.value), ops.size))
}
