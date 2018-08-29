import inox._
import inox.trees._
import inox.trees.dsl._

import stainless.annotation._
import stainless.collection._
import stainless.math._
import stainless.lang._

object Abs {

  	val integerAbs: FunDef = mkFunDef(FreshIdentifier("integerAbs"))()(_ => (
    Seq("x" :: IntegerType()), IntegerType(), { case Seq(x) =>
      if_ (x >= E(BigInt(0))) {
        x
      } else_ {
        -x
      }
    }))

  def test(x: BigInt) = {
    integerAbs(IntegerLiteral(5))
  }

}

