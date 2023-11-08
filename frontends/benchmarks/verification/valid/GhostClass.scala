import stainless.annotation._
import stainless.lang.{ghost => ghostExpr, _}

object GhostClass {

  @ghost
  def ghostFn(x: BigInt): BigInt = x

  @ghost
  case class MyGhostClass(i: BigInt) {
    // ghostMethod is treated as @ghost even though not explicitly
    // annotated as so due to the class being ghost
    def ghostMethod(x: BigInt): BigInt = ghostFn(x + i).ensuring(_ == x + i)
  }

  @ghost
  def createGhostClass(i: BigInt): MyGhostClass = MyGhostClass(i).ensuring(_.i == i)

  def useInGhost(i: BigInt): BigInt = {
    @ghost val mgc = MyGhostClass(i)
    ghostExpr {
      val ii = mgc.ghostMethod(2 * i)
      assert(ii == mgc.i + 2 * i)
    }
    3 * i
  }
}