import stainless.lang._
import stainless.util.Random
import stainless.collection._
import stainless.lang._
import scala.Any
import stainless.annotation._
import stainless.proof._

object QuantifierUnification {
  case class SchedEntity(val id:BigInt, val state: BigInt, val quanta: BigInt, val core:BigInt, val load: BigInt, val rq:List[BigInt]);

  case class Core(val current: Option[BigInt], val ready: BigInt);
  case class SharedState(
    val progress:BigInt,
    val cores:List[BigInt],
    val states:BigInt => Core,
    val entities:BigInt => SchedEntity) {
      require(forall((id:BigInt) => entities(id).rq.forall(e => entities(e).id < entities(id).id && entities(e).id >= 0)))
    }

  def test(s:SharedState, id:BigInt):Boolean = {
    s.entities(id).rq.forall(e => s.entities(e).id < s.entities(id).id && s.entities(e).id >= 0)
  }.holds;
}
