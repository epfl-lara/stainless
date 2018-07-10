// Need `--partial-eval-vc` flag

import stainless.lang._
import stainless.annotation._
import stainless.collection._

object kv {

  sealed abstract class Label
  object Label {
    case class Get(key: String)                extends Label
    case class Put(key: String, value: String) extends Label
  }

  sealed abstract class Op
  case class Pure(value: Option[String])                     extends Op
  case class Get(key: String, next: Option[String] => Op)    extends Op
  case class Put(key: String, value: String, next: () => Op) extends Op

  def get(key: String)(next: Option[String] => Op): Op    = Get(key, next)
  def put(key: String, value: String)(next: () => Op): Op = Put(key, value, next)
  def pure(value: Option[String]): Op                     = Pure(value)

  @partialEval
  def interpret(op: Op)(kv: Map[String, String], trace: List[Label], fuel: BigInt): (Option[String], List[Label]) = {
    require(fuel >= 0)
    decreases(fuel)

    op match {
      case Pure(value) =>
        (value, trace)

      case Get(key, next) if fuel > 0 =>
        interpret(next(kv.get(key)))(
          kv,
          Label.Get(key) :: trace,
          fuel - 1
      )

      case Put(key, value, next) if fuel > 0 =>
        interpret(next())(
          kv.updated(key, value),
          Label.Put(key, value) :: trace,
          fuel - 1
       )

      case _ =>
        (None(), trace)
    }
  }

  val program = put("foo", "bar") { () =>
    put("toto", "tata") { () =>
      get("foo") { foo =>
        pure(foo)
      }
    }
  }

  def result(map: Map[String, String], init: List[Label], fuel: BigInt) = {
    require(fuel > 10)
    interpret(program)(map, init, fuel)
  } ensuring { res => res match {
    case (res, trace) => prop(res, trace)
  }}

  @inline
  def prop(res: Option[String], trace: List[Label]) = {
    res == Some("bar") &&
    trace.take(3) == List(
      Label.Get("foo"),
      Label.Put("toto", "tata"),
      Label.Put("foo", "bar")
    )
  }

}
