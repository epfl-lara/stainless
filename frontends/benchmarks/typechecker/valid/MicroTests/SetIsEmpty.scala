
import stainless.lang._
import scala.language.postfixOps

object SetIsEmpty {

  def emptySetIsEmpty: Boolean = {
    Set().isEmpty
  }.holds

  //  def emptyContainsNothing[A](set: Set[A]): Boolean = {
  //    set.isEmpty ==> forall((x: A) => !set.contains(x))
  //  }.holds

   def complementItselfEmpty[A](set: Set[A]): Boolean = {
     (set -- set).isEmpty
   }.holds

   def addToEmptyNonEmpty[A](set: Set[A], x: A): Boolean = {
     require(set.isEmpty)
     !((set + x).isEmpty)
   }.holds

}
