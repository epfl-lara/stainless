object ToString {
  abstract class A {
    def toString: String
    def fooBar: Int
  }

  case class C(s: String) extends A {
    override def toString: String = s
    override def fooBar: Int = 42
  }

  case class Auto(s: String) {
    override def toString: String = s
  }
}
