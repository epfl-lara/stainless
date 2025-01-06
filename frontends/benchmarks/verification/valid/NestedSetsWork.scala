import stainless.lang.*
import stainless.collection.*

object NestedSetsWork:
  def meAndEmpty(s: Set[Int]): Set[Set[Int]] = {
    Set(s, Set())
 }.ensuring(result => (result.contains(s)) && (result.contains(Set())))

  def unionOfSets(lst: List[Set[Int]], s: Set[Int]): Set[Set[Int]] = {
   require(lst.contains(s))
   lst.content 
 }.ensuring(_.contains(s))
end NestedSetsWork
