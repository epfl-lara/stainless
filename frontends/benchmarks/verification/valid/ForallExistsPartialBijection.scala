import stainless.lang.{ghost => ghostExpr}
import stainless.lang.Quantifiers.*
import stainless.annotation.*
import stainless.lang.StaticChecks.*
import stainless.lang.Ensures.*
import stainless.lang.unfold
import stainless.lang.Option
import stainless.lang.Some
import stainless.lang.None
import stainless.collection.List
import stainless.collection.Cons
import stainless.collection.Nil

object ForallExistsPartialBijection:
  trait TokenValue
  case class PositiveInt(i: BigInt) extends TokenValue
  case class StringValue(s: List[Char]) extends TokenValue

  def ff(b: BigInt): Option[TokenValue] = {
    if b >= 0 then
      Some(PositiveInt(b))
    else
      None()
  }

  def gg(t: TokenValue) : Option[BigInt] = {
    t match {
      case PositiveInt(i) => Some(i)
      case _ => None()
    }
  }

  val partialBijectionTokenValue = {
    ghostExpr{
      assert({
        unfold(semiPartialInverseBody(ff, gg))
        semiPartialInverseBody(ff, gg)
      })
      assert({
        unfold(semiPartialInverseBody(gg, ff))
        semiPartialInverseBody(gg, ff)
      })
      unfold(semiPartialInverse(ff, gg))
      unfold(semiPartialInverse(gg, ff))
    }
    PartialBijection[BigInt, TokenValue](ff, gg)
  }

end ForallExistsPartialBijection
