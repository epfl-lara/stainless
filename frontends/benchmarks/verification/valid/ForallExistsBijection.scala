import stainless.lang.{ghost => ghostExpr}
import stainless.lang.Quantifiers.*
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.Ensures.*
import stainless.lang.unfold

object ForallExistsBijection:
  def ff(x: BigInt) = x + 1
  def gg(x: BigInt) = x - 1

  val bijectionBigIntBigInt = {
    ghostExpr{
      assert({
        unfold(Forall((x: BigInt) => ff(gg(x)) == x))
        Forall((x: BigInt) => ff(gg(x)) == x)
      })
      assert({
        unfold(Forall((x: BigInt) => gg(ff(x)) == x))
        Forall((x: BigInt) => gg(ff(x)) == x)
      })
      unfold(validInj(ff, gg))
      unfold(validInj(gg, ff))
    }
    Bijection[BigInt, BigInt](ff, gg)
  }

end ForallExistsBijection
  