import leon.lang._

object Sets1 {
  def set(i: Int): Int => Boolean = x => x == i

  def complement(s: Int => Boolean): Int => Boolean = x => !s(x)

  def union(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) || s2(x)

  def intersection(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) && s2(x)

  def de_morgan_1(s1: Int => Boolean, s2: Int => Boolean, x: Int): Boolean = {
    val u1 = union(s1, s2)
    val u2 = complement(intersection(complement(s1), complement(s2)))
    u1(x) == u2(x)
  }.holds

  def de_morgan_2(s1: Int => Boolean, s2: Int => Boolean, x: Int): Boolean = {
    val u1 = intersection(s1, s2)
    val u2 = complement(union(complement(s1), complement(s2)))
    u1(x) == u2(x)
  }.holds
}
