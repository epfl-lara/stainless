object ExploratoryTest {

  abstract class MyList
  case class MyCons(first: Int, rest: MyList) extends MyList
  case object MyNil extends MyList

  def bar(a: MyList): Int = a match {
    case b: MyCons => b.first
    case _ => 0
  }

//  def foo(baz: Int): Int = baz match {
//    case a @ 1  => 1 + 2
//    case 42 => baz
//    case (a, b) => a
//  }
}