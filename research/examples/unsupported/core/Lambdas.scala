import stainless.lang._

object Lambdas {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f: Unit = {
    val a = Box(1)
    val h = Holder(a)
    val c = Box(2)
    val set = (_: Unit) => { h.b = c }
    val get = (_: Unit) => h.b
    val id = (x: Box) => x

    set(())
    val d = h.b
    val e = get(())
    val k = id(a)

    assert(d.value == 2)
    assert(e.value == 2)
    assert(k.value == 1)
  }
}
