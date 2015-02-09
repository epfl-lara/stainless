import leon.lang._

object Sets1 {
  def set(i: Int): Int => Boolean = x => x == i

  def complement(s: Int => Boolean): Int => Boolean = x => !s(x)

  def union(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) || s2(x)

  def intersection(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) && s2(x)

  def union_associativity(sa1: Int => Boolean, sa2: Int => Boolean, sa3: Int => Boolean, x: Int): Boolean = {
    val u1 = union(union(sa1, sa2), sa3)
    val u2 = union(sa1, union(sa2, sa3))
    u1(x) == u2(x)
  }.holds

  def intersection_associativity(sa1: Int => Boolean, sa2: Int => Boolean, sa3: Int => Boolean, x: Int): Boolean = {
    val u1 = intersection(intersection(sa1, sa2), sa3)
    val u2 = intersection(sa1, intersection(sa2, sa3))
    u1(x) == u2(x)
  }.holds
}
