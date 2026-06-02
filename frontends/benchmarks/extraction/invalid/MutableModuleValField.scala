object MutableModuleValField {

  case class Counter(var x: BigInt) {
    def next(): BigInt = {
      val old = x
      x = x + 1
      old
    }
  }

  val c = Counter(0)

  case class A(x: BigInt) {
    val y = c.next()
  }

}
