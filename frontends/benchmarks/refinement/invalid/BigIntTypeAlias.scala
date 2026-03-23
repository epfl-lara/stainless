package bigIntTypeAlias
import stainless.annotation.ignore
import stainless.lang._

object O:
  type Neg = {v: BigInt with v < 0}

  def x: Neg = BigInt(0).ck


extension [T](x: T)
  @ignore
  inline def ck[TT] = x.asInstanceOf[TT]