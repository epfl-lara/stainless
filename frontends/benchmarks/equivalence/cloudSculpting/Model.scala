import stainless.lang._
import stainless.collection._

// This tests the auxiliary function matching when argument must be permuted to succeed equivalence checking.
object Model {
  // "cloud scuplting" because does nothing useful (not only that, but also burns fuel...)
  def sculpteurDeNuage[A, B, C](a: A, b: B, c: C, fuel: BigInt, i1: BigInt, i2: BigInt, i3: BigInt, a2b: A => B, b2c: B => C, c2a: C => A): (BigInt, BigInt, BigInt) = {
    require(fuel >= 0)
    leVraiSculpteurDeNuage(a, b, c, fuel, i1, i2, i3, a2b, b2c, c2a)
  }

  def leVraiSculpteurDeNuage[A, B, C](a: A, b: B, c: C, fuel: BigInt, i1: BigInt, i2: BigInt, i3: BigInt, a2b: A => B, b2c: B => C, c2a: C => A): (BigInt, BigInt, BigInt) = {
    require(fuel >= 0)
    decreases(fuel)
    if (fuel == 0) (i1, i2, i3)
    else {
      val (ii1, ii2, ii3) = mixmash(i1, i2, i3)
      leVraiSculpteurDeNuage(c2a(c), a2b(a), b2c(b), fuel - 1, ii1, ii2, ii3, a2b, b2c, c2a)
    }
  }

  def mixmash(i1: BigInt, i2: BigInt, i3: BigInt): (BigInt, BigInt, BigInt) = (i2 - 1, i3 + i2, i1)
}