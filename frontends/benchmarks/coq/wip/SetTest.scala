import stainless.lang._

object SetTest {
  def unionTest(a: Set[BigInt]): Boolean = {
    (a ++ a) == a
  }.holds

  def interTest[T](a: Set[T]): Boolean = {
    (a & a) == a
  }.holds

  def minusTest[T](a: Set[T]): Boolean = {
    (a -- a) == Set.empty[T]
  }.holds

  def subsetTest[T](a: Set[T]): Boolean = {
    (a subsetOf a)
  }.holds
}
