
import stainless.math._

object NaturalBuiltin {

  def test = {
    assert(Nat.`0` + Nat.`0` == Nat.`0`)
    assert(Nat.`0` + Nat.`1` == Nat.`1`)
  }

  def test2(n: Nat) = {
    assert(Nat.`0` + n == n)
    assert(n + Nat.`0` == n)
  }

  def test3(n: Nat) = {
    assert(Nat.`1` * n == n)
    assert(n * Nat.`1` == n)
  }

  def test4(n: Nat) = {
    assert(Nat.`0` * n == Nat.`0`)
    assert(n * Nat.`0` == Nat.`0`)
  }
}
