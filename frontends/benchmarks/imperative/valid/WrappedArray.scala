object WrappingArray {

  case class A(var x: Int)
  case class Wrap(ar: Array[A])

  def getA(w: Wrap, i: Int): A = {
    require(0 <= i && i < w.ar.length)
    w.ar(i)
  }

  def reset(a: A): Unit = { a.x = 0 }
  def set(a: A, v: Int): Unit = { a.x = v }

  def test(w: Wrap, i: Int): Unit = {
    require(0 < i && i < w.ar.length)
    reset(getA(w, 0))
    set(getA(w, i), 100)
    assert(w.ar(0).x == 0)
    assert(w.ar(i).x == 100)
    reset(getA(w, i))
    assert(w.ar(i).x == 0)
  }
}
