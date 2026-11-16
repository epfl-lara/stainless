import stainless.annotation.*
import stainless.lang.*

object i1771:

  @opaque
  def f(b: BigInt): Any = {
    require(b >= 0)
    b
  }.ensuring(res => res >= 0)

  def g(b: BigInt): BigInt = {
    require(b >= 0)
    f(b).asInstanceOf[BigInt]
  }.ensuring(res => res >= 0)

  def t(b: BigInt): (BigInt, Any) = {
    (b, b)
  }.ensuring(res => res._2 == b)
