package bigIntTypeAlias
import stainless.annotation.ignore
import stainless.lang._

object O:
  type Neg = {v: BigInt with v < 0}

  def x: Neg = BigInt(0).asInstanceOf[Neg]