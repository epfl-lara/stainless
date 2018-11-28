//import stainless.lang.Bag

object ExploratoryTest {

//  val f2 = (x: Int) => x / 2
//

//  def make(elem: Int): MyList = MyCons(1, MyEmpty())
//
//  def prepend(elem: Int, list: MyList): MyList = MyCons(elem, list)

  def append(elem: Int, list: MyList): Int = {
    if (list.isInstanceOf[MyCons]) {
      list.elem
    } else {
//      val cons: MyCons = list
//      MyCons(cons.elem, append(elem, cons.rest))
      2
    }
  }

  abstract class MyList
  case object MyEmpty extends MyList
  case class MyCons(elem: Int, rest: MyList) extends MyList
}