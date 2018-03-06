package test

sealed abstract class Foo {
  def foo(): Unit = println("a")
}
