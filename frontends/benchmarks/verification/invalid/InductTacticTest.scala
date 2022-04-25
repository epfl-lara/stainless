import stainless.collection._
import stainless.annotation._

object InductTacticTest {
  case class SharedState(val rqs:BigInt => List[BigInt]);

  @induct
  def isTree(s:SharedState, content:List[BigInt], id:BigInt):Boolean = {
    require(content.forall(e => e < id && e >= 0))
    content match {
      case Nil() => true
      case Cons(t, ts) =>
        isTree(s, ts, id) && isTree(s, s.rqs(t), t)
    }
  }
}
