//import stainless.lang.Bag

object ExploratoryTest {

//  val f2 = (x: Int) => x / 2
//
  abstract class MyList
  case object MyEmpty extends MyList
  case class MyCons(elem: Int, rest: MyList) extends MyList
}