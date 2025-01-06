object i1479 {
  case class MyClass(var x: BigInt, var y: BigInt, var isValid: Boolean = true) {
    require(!isValid || x <= y)
  }

  inline def changeMyClass(m: MyClass)(inline body: => Unit): Unit =
    require(m.isValid)
    m.isValid = false
    body
    m.isValid = true

  def inc(m: MyClass): Unit =
    require(m.isValid)
    changeMyClass(m):
      m.x += 1
      m.y += 1
}