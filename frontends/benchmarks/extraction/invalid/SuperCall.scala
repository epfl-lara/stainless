package test

sealed abstract class Base {
  def method(): Unit = ???
}

abstract class Derived extends Base {
  override def method() = {
    super.method() // super is not allowed
  }
}

