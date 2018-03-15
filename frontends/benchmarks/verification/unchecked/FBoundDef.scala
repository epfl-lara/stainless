sealed abstract class Foo[A] {
  def foo(that: A): A
}

case class Bar() extends Foo[Bar] { // <- F-Bound here
  def foo(that: Bar): Bar = Bar()
}

