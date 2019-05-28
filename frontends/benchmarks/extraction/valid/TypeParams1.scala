package test

object TypeParams1 {
  sealed abstract class Base[T]
  case class Bar() extends Base[Int]
}
