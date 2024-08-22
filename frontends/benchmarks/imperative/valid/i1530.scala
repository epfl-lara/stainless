import stainless.lang.*

object i1530 {
  case class A(var i: BigInt)

  def outer1(a: A): Unit = {
    def inner11(a1: A): Unit = {
      ()
   }.ensuring(_ => a1.i == old(a1).i)

    def inner12(a1: A, a2: A): Unit = {
      a2.i += 1
   }.ensuring(_ => a1.i == old(a1).i)
  }

  def outer2(a: A): Unit = {
    def inner21(): Unit = {
   }.ensuring(_ => a.i == old(a).i)
  }

  def outer3(a: A): Unit = {
    def inner3(a2: A): Unit = {
      a.i += 1
   }.ensuring(_ => a.i == old(a).i + 1 && a2.i == old(a2).i)
  }
}
