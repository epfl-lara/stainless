import stainless.lang._
import stainless.collection._

object Candidate {
  def sculpteurDeNuage[A, B, C](a: A, b: B, c: C, fuel: BigInt, i1: BigInt, i2: BigInt, i3: BigInt, a2b: A => B, b2c: B => C, c2a: C => A): (BigInt, BigInt, BigInt) = {
    require(fuel >= 0)
    leVraiSculpteurDeNuage(b2c, b, c, fuel, a2b, i2, a, i3, i1, c2a)
  }

  def leVraiSculpteurDeNuage[A, B, C](b2c: B => C, b: B, c: C, fuel: BigInt, a2b: A => B, i2: BigInt, a: A, i3: BigInt, i1: BigInt, c2a: C => A): (BigInt, BigInt, BigInt)= {
    require(fuel >= 0)
    decreases(fuel)
    if (fuel == 0) (i1, i2, i3)
    else {
      val (ii1, ii2, ii3) = mixmash(i2, i3, i1)
      leVraiSculpteurDeNuage(b2c, a2b(a), b2c(b), fuel - 1, a2b, ii2, c2a(c), ii3, ii1, c2a)
    }
  }

  def mixmash(i2: BigInt, i3: BigInt, i1: BigInt): (BigInt, BigInt, BigInt) = {
    decreases(if (i2 <= 0) -i2 else i2)
    if (i2 == 0) (-1, i3, i1)
    else if (i2 > 0) {
      val (r1, r2, r3) = mixmash(i2 - 1, i3 + 1, i1)
      (r1 + 1, r2, r3)
    } else {
      val (r1, r2, r3) = mixmash(i2 + 1, i3 - 1, i1)
      (r1 - 1, r2, r3)
    }
  }
}