object ExploratoryTest {

  abstract class MyList
  case class MyCons(first: Int, rest: MyList) extends MyList
  case object MyNil extends MyList

  def bar(n : Int): Int = {
    require(n > 2)
    n
  }

//  def foo(baz: Int): Int = baz match {
//    case a @ 1  => 1 + 2
//    case 42 => baz
//    case (a, b) => a
//  }
}