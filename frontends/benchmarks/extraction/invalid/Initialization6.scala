object InitUnsoundness {
  case class B(val x: Int)

  sealed abstract class Top {
    val g: B = this.foo
    val h: B = B(2)

    def foo = {
      B(3)
    }
  }
  case class A() extends Top {
    override def foo = {
      h
    }
  }

  def test: Int = {
    val a = A()
    a.g.x
  }
}