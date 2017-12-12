import stainless.collection._
import stainless.lang._
import stainless.annotation._

import scala.language.postfixOps

object Term {

  case class Task(tick: BigInt) {
    require(tick >= 0)
  }

  case class Core(tasks: Task, current: Option[BigInt])


  def insertBack(): Core = Core(Task(0), None())


  def looping(c: Core): Core = {
    c.current match {
      case Some(_) => looping(c)
      case None() => insertBack()
    }
  }

  @extern
  def main(args: Array[String]): Unit = {
    looping(Core(Task(0), Some(0)))
  }

}
