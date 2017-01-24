import stainless.lang._
import stainless.annotation._

object ArrayParamMutation7 {

  def f(i: BigInt)(implicit world: Array[BigInt]): BigInt = {
    require(world.length == 3)

    world(1) += 1 //global counter of f

    val res = i*i
    world(0) = res
    res
  }

  @pure
  def mainProgram(): Unit = {

    implicit val world: Array[BigInt] = Array(0,0,0)

    f(1)
    assert(world(0) == 1)
    f(2)
    assert(world(0) == 4)
    f(4)
    assert(world(0) == 16)

    assert(world(1) == 3)
  }

}
