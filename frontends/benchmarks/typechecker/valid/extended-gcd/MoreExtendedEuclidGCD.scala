import stainless.lang._
import stainless.annotation._

object GCD {
  case class Result(gcd: BigInt, // GCD value
		    ka: BigInt, kb: BigInt,  // witnesses for divisibility (quotients)
		    x: BigInt, y: BigInt)    // witnesses that ka,kb are mutually prime

  def gcd(a: BigInt, b: BigInt, r: Result): Boolean = {
    a == r.ka * r.gcd &&
    b == r.kb * r.gcd &&
    r.ka * r.x + r.kb * r.y == BigInt(1)
  }

  def abs(x: BigInt) = if (x < 0) -x else x

  def euclid(a: BigInt, b: BigInt): Result = {
    decreases(abs(b), abs(a))
    if (b == 0) {
      Result(a, BigInt(1), BigInt(0), BigInt(1), BigInt(0))
    } else {
      val r1 = euclid(b, a % b)
      assert(gcd(b, a % b, r1))
      // r1.gcd will be also our gcd
      // Witness for divisibility of b:
      assert(b == r1.ka * r1.gcd)
      val kb = r1.ka
      // Witness for divisibility of a:
      assert(a % b == r1.kb * r1.gcd)
      assert(a == b*(a/b) + a % b)
      assert(a == r1.ka * r1.gcd * (a/b) + r1.kb * r1.gcd)
      assert(a == r1.ka * (a/b) * r1.gcd + r1.kb * r1.gcd)
        // just factor out r1.gcd
      val ka = r1.ka * (a/b) + r1.kb
      // Witnesses that ka, kb are mutually prime
        // r1 witnesses from the recursive call
      assert(r1.ka * r1.x + r1.kb * r1.y == BigInt(1))
        // now want them in terms of kb and ka
        // eliminate r1.kb from definition of ka above:
      assert(r1.ka * r1.x + (ka - r1.ka*(a/b)) * r1.y == BigInt(1))
        // r1.ka is kb
      assert(kb * r1.x + (ka - kb*(a/b)) * r1.y == BigInt(1))
        // re-arrange (ring laws)
      assert(ka * r1.y + kb * (r1.x - (a/b)*r1.y) == BigInt(1))
      val x = r1.y
      val y = r1.x - (a/b)*r1.y
      Result(r1.gcd, ka, kb, x, y)
    }
  } ensuring(res => gcd(a, b, res))

  def divisorsDivideGCD(a: BigInt, b: BigInt, r: Result,
                    d1: BigInt, ka1: BigInt, kb1: BigInt): Unit = {
    require(gcd(a, b, r) && a == ka1*d1 && b == kb1*d1)
    assert(r.ka * r.x + r.kb * r.y == BigInt(1))
    assert(r.gcd * r.ka * r.x + r.gcd * r.kb * r.y == r.gcd)
    assert(r.gcd * r.ka == a)
    assert(r.gcd * r.kb == b)
    assert(a * r.x + b * r.y == r.gcd)
    assert(ka1*d1 * r.x + kb1*d1 * r.y == r.gcd)
  } ensuring(_ => r.gcd == (ka1*r.x + kb1*r.y)*d1)

  def positiveMultiple(a: BigInt, b: BigInt, c: BigInt): Unit = {
    require(a == b * c && a > 0 && c > 0 && b >= 1)
    ()
  } ensuring(_ => a >= c)

  def gcdIsGreatest(a: BigInt, b: BigInt, r: Result,
                    d1: BigInt, ka1: BigInt, kb1: BigInt): Unit = {
    require(gcd(a, b, r) && a == ka1*d1 && b == kb1*d1 && r.gcd > 0 && d1 > 0)
    divisorsDivideGCD(a, b, r, d1, ka1, kb1)
    positiveMultiple(r.gcd, ka1*r.x + kb1*r.y, d1)
    assert(ka1*r.x + kb1*r.y >= 1)
  } ensuring(_ => r.gcd >= d1)
}
