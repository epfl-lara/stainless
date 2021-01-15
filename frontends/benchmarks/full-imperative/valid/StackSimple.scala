import stainless.lang._
import stainless.collection._
import stainless.lang.Option._
import stainless.annotation._
import stainless.proof._
import stainless.lang.StaticChecks._

object SimpleStack {
  // TODO: Add a generic version of Stack
  final case class Stack(var content: List[BigInt]) extends AnyHeapRef
  {
    def push(a: BigInt): Unit = {
      reads(Set(this))
      modifies(Set(this))

      content = a :: content
    }

    def pop: BigInt = {
      reads(Set(this))
      require(!content.isEmpty)
      modifies(Set(this))

      val n = content.head
      content = content.tail
      n
    }
  }

  @extern
  def main(args: Array[String]): Unit = {
    val s = Stack(List())
    println("Stack with nodes")
    s.push(5)
    s.push(10)
    s.push(14)
    println("Stack is: " + s)
    println(s.pop)
    println(s.pop)
    println(s.pop)
    println("Stack is: " + s)
  }
}
