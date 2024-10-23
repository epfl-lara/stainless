import stainless.lang.Set
import stainless.lang.Bag
import stainless.collection.List

object Typedefs3 {
  type TypeSet[A] = Set[List[A]]
  // type TypeBag[A] = Bag[List[A]]

  val t: TypeSet[Int] = Set(List(1, 2, 3), List(4, 5, 6))
  // val b: TypeBag[Int] = Bag(List(1, 2, 3), List(4, 5, 6))

}
