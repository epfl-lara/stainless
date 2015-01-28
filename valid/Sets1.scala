import leon.lang._

object Sets1 {
  def set(i: Int): Int => Boolean = x => x == i

  def complement(s: Int => Boolean): Int => Boolean = x => !s(x)

  def union(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) || s2(x)

  def intersection(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) && s2(x)

  def associativity(sa1: Int => Boolean, sa2: Int => Boolean, sa3: Int => Boolean, x: Int): Boolean = {
    val u1 = union(union(sa1, sa2), sa3)
    val u2 = union(sa1, union(sa2, sa3))
    u1(x) == u2(x)
  }.holds

  def lemma(s1: Int => Boolean, s2: Int => Boolean, x: Int): Boolean = {
    val u1 = union(s1, s2)
    val u2 = complement(intersection(complement(s1), complement(s2)))
    u1(x) == u2(x)
  }.holds
}
