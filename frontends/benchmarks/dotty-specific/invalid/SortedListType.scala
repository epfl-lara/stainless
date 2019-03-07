import scala.language.implicitConversions

import stainless.lang._
import stainless.collection._

object SortedListType {

  type SortedList = { l: List[BigInt] => ListOps.isSorted(l) }

  def foo(list: { l: SortedList => l.length > BigInt(2) }): { res: (BigInt, BigInt) => res._1 <= res._2 } = {
    (list.head, list.tail.head)
  }

}
