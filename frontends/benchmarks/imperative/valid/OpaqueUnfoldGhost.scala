import stainless.lang.{ghost => ghostExpr, _}
import stainless.proof._
import stainless.annotation._
import StaticChecks._

object OpaqueMutation2 {
  case class Box(var cnt: BigInt) {
    @opaque
    @ghost
    @pure
    def valid: Boolean = cnt > 0 // Invariant that is hidden from the outside

    def operation(): Unit = {
      require({
        unfold(valid)
        valid
      })
      unfold(
        valid
      ) // Shouldn't be consider to be ghost, even with a ghost argument
      assert(cnt > 0)
      cnt += 1
      assert(cnt > 0)
    }.ensuring(_ => unfold(valid) valid)
  }
}
