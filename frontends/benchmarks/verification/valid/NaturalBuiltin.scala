
import stainless.math._

object NaturalBuiltin {

  def test = {
    assert(Nat.Zero + Nat.Zero == Nat.Zero)
    assert(Nat.Zero + Nat.One == Nat.One)
  }

  def test2(n: Nat) = {
    assert(Nat.Zero + n == n)
    assert(n + Nat.Zero == n)
  }

  def test3(n: Nat) = {
    assert(Nat.One * n == n)
    assert(n * Nat.One == n)
  }

  def test4(n: Nat) = {
    assert(Nat.Zero * n == Nat.Zero)
    assert(n * Nat.Zero == Nat.Zero)
  }

}
