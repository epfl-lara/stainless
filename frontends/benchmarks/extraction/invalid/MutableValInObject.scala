object MutableValInObject {
  case class Counter(var x: BigInt) {
    def next(): BigInt = {
      val old = x
      x = x + 1
      old
    }
  }

  val c = Counter(0)

  case class A(x: BigInt) {
    def y: BigInt = c.next()
  }

  @main def main(): Unit = {
    val obj = A(10)
    val obj2 = A(10)

    assert(obj == obj2)
    assert(obj.y == obj2.y) // should fail: y should differ due to mutation
    // println("Done")
  }
}
