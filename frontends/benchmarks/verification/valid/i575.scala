import stainless.annotation.*
import stainless.collection.*

object i575:

  @extern
  def assume(b: Boolean): Unit = {
    ??? : Unit
  } ensuring (_ => b)

  def f(l: List[BigInt], b: Boolean): Unit =
    if b then 0
    else assume(false)

    assert(b)
