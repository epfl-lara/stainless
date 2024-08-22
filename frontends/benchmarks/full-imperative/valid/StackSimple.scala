import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object SimpleStackExample {
  case class Stack[T](private var data: List[T]) extends AnyHeapRef {
    def list = {
      reads(Set(this))
      data
    }

    def push(a: T): Unit = {
      reads(Set(this))
      modifies(Set(this))

      data = a :: data
    }.ensuring(_ => list == a :: old(list))

    def pop: T = {
      reads(Set(this))
      require(!list.isEmpty)
      modifies(Set(this))

      val n = data.head
      data = data.tail
      n
    }.ensuring(res => res == old(list).head &&
                       list == old(list).tail)
  }
}
