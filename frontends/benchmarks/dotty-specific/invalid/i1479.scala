object i1479 {
  case class MyClass(var x: BigInt, var y: BigInt, var isValid: Boolean = true) {
    require(!isValid || x <= y)
  }

  inline def changeMyClass(m: MyClass)(inline body: => Unit): Unit =
    m.isValid = false // Note that we may not have mc.x <= mc.y so this is invalid
    body
    m.isValid = true

  def inc(m: MyClass): Unit =
    changeMyClass(m):
      m.x += 1
      m.y += 1
}