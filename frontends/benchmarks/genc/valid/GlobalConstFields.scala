import stainless.annotation._
import stainless.io._

// `val` fields of `@cCode.global` classes are emitted as `const` globals, and constants used in
// the initial values of global fields are inlined (C requires constant expressions there).
object GlobalConstFields {

  val Start: Int = 3

  @cCode.global
  case class GlobalState(
    var count: Int = Start,
    val limit: Int = 10,
  ) {
    require(0 <= count && count <= limit)
  }

  def step()(implicit state: GlobalState): Unit = {
    require(state.count < state.limit)
    state.count += 1
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state: State = newState
    implicit val gs: GlobalState = GlobalState()
    step()
    step()
    StdOut.print(gs.count)
    StdOut.println(gs.limit)
  }

}
