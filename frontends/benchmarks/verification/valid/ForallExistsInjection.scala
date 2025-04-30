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

object ForallExistsInjection:
  trait TokenValue
  case class PositiveInt(i: BigInt) extends TokenValue
  case class StringValue(s: List[Char]) extends TokenValue

  def ff(b: BigInt): TokenValue = PositiveInt(b)

  def gg(t: TokenValue) : BigInt = {
    t match {
      case PositiveInt(i) => i
      case _ => -1
    }
  }

  val injectionTokenValue = {
    ghostExpr{
      assert({
        unfold(semiInverseBody(gg, ff))
        semiInverseBody(gg, ff)
      })
      unfold(semiInverse(gg, ff))
    }
    Injection[BigInt, TokenValue](ff, gg)
  }

end ForallExistsInjection
