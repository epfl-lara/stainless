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
        unfold(partialInverse(ff, gg))
        partialInverse(ff, gg)
      })
      assert({
        unfold(partialInverse(gg, ff))
        partialInverse(gg, ff)
      })
    }
    Bijection[BigInt, BigInt](ff, gg)
  }

end ForallExistsBijection
  