package test

sealed abstract class Base[T]
case class Bar() extends Base[Int]
