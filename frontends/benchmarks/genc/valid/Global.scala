import stainless.annotation._
import stainless.io._

object Global {

  @cCode.global
  case class GlobalState(
    val data: Array[Int] = Array.fill(100)(0),
    var stable: Boolean = true,
    var x: Int = 5,
    var y: Int = 7,
  ) {
    require(
      data.length == 100 && (
        !stable || (
          0 <= x && x <= 100 &&
          0 <= y && y <= 100 &&
          x + y == 12
        )
      )
    )
  }

  def move()(implicit state: GlobalState): Unit = {
    require(state.stable && state.y > 0)
    state.stable = false
    state.x += 1
    state.y -= 1
    state.data(state.y) = 1
    state.stable = true
    if (state.y > 0) move()
  }.ensuring(_ => state.stable)

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state: State = newState
    implicit val gs: GlobalState = GlobalState()
    StdOut.print(gs.x)
    StdOut.print(gs.y)
    move()
    StdOut.print(gs.data(6))
    StdOut.print(gs.data(7))
    StdOut.print(gs.x)
    StdOut.println(gs.y)
  }

}
