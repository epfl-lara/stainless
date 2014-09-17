import leon.lang._

object Closures2 {
  def set(i: Int): Int => Boolean = x => x == i

  def union(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) || s2(x)

  def intersection(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) && s2(x)

  def diff(s1: Int => Boolean, s2: Int => Boolean): Int => Boolean = x => s1(x) && !s2(x)

  def set123(): Int => Boolean = union(set(1), union(set(2), set(3)))

  def test1(): Boolean = {
    val s1 = set123()
    val s2 = union(s1, set(4))
    s2(1) && s2(2) && s2(3) && s2(4)
  }.holds

  def test2(): Boolean = {
    val s1 = set123()
    val s2 = intersection(s1, union(set(1), set(3)))
    val s3 = diff(s1, s2)
    s3(2) && !s3(1) && !s3(3)
  }.holds

  def test3(): Boolean = {
    val s1 = set123()
    val s2 = set123()
    val s3 = union(s1, s2)
    s3(1) && s3(2) && s3(3)
  }.holds
}

// vim: set ts=4 sw=4 et:
