import stainless._
import stainless.lang._
import stainless.annotation._

object MatchMutation {

  case class Ref[@mutable T](var value: T)
  sealed trait Parent {
    var xyz: Ref[Int]
  }
  case class Child1(var xyz: Ref[Int]) extends Parent

  def t1(p: Array[Parent], i: Int): Unit = {
    require(0 <= i && i < p.length)
    p(i) match {
      case Child1(xyz) =>
        xyz.value = 42
        assert(xyz.value == 42)
    }
    assert(p(i).xyz.value == 42)
  }

  def t2(p: Ref[Parent]): Unit = {
    p.value match {
      case Child1(xyz) =>
        xyz.value = 42
    }
    assert(p.value.xyz.value == 42)
  }

  def t3(p: Parent): Unit = {
    p match {
      case Child1(xyz) =>
        xyz.value = 42
    }
    assert(p.xyz.value == 42)
  }

}
