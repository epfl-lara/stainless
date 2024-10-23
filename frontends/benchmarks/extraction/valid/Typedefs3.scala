import stainless.lang.Set
import stainless.lang.Bag
import stainless.collection.List
import stainless.lang.Map
import stainless.lang.MutableMap

object Typedefs3 {
  type TypeSet[A] = Set[List[A]]
  type TypeBag[A] = Bag[List[A]]
  type TypeMap[A] = Map[Int, List[A]]
  type TypeMutableMap[A] = MutableMap[Int, List[A]]

  val t: TypeSet[Int] = Set(List(1, 2, 3), List(4, 5, 6))
  val b: TypeBag[Int] = Bag((List(1, 2, 3), BigInt(3)), (List(4, 5, 6), BigInt(2)))
  val m: TypeMap[Int] = Map(1 -> List(1, 2, 3), 2 -> List(4, 5, 6))
  val mm: TypeMutableMap[Int] = MutableMap.withDefaultValue[Int, List[Int]](() => List(1, 2, 3))

}
