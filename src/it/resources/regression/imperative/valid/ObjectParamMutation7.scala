import stainless.lang._

object ObjectParamMutation7 {

  case class A(a: Int, var x: BigInt, var y: BigInt, var z: BigInt)

  def inc(a: A): Unit = {
    require(a.x >= 0 && a.y >= 0 && a.z >= 0)
    a.x += 1
    a.y += 1
    a.z += 1
  } ensuring(_ => a.x == old(a).x + 1 && a.y == old(a).y + 1 && a.z == old(a).z + 1)

  def f(): A = {
    val a = A(0, 0, 0, 0)
    inc(a); inc(a); inc(a)
    a
  } ensuring(res => res.x == res.y && res.y == res.z && res.z == 3)

}
