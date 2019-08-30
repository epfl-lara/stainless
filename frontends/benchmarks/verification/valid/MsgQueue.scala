
import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.collection._
import stainless.annotation._

import java.util.ArrayDeque

object MessageQueue {

  case class MsgQueue[A](
    @extern @pure
    queue: ArrayDeque[A],
    @ghost
    var msgs: List[A]
  ) {
    def put(msg: A): Unit = {
      msgs = msg :: msgs
      _put(msg)
    }

    @extern @pure
    private def _put(msg: A): Unit = {
      queue.addFirst(msg)
    }

    def take(): Option[A] = {
      val result = _take()
      msgs = msgs.tailOption.getOrElse(Nil())
      result
    } ensuring { res =>
      res == old(this).msgs.headOption
    }

    @extern @pure
    private def _take(): Option[A] = {
      Option(queue.pollFirst())
    } ensuring { res =>
      res == msgs.headOption
    }

    @extern @pure
    def isEmpty: Boolean = {
      queue.size() == 0
    } ensuring { res =>
      res == msgs.isEmpty
    }
  }

  object MsgQueue {
    @extern @pure
    def empty[A]: MsgQueue[A] = {
      MsgQueue(new ArrayDeque(), Nil())
    } ensuring { res =>
      res.isEmpty && res.msgs.isEmpty
    }
  }

  def test(queue: MsgQueue[String]) = {
    require(queue.isEmpty)

    queue.put("World")
    queue.put("Hello")

    assert(!queue.isEmpty)

    val a = queue.take()
    assert(a == Some("Hello"))

    val b = queue.take()
    assert(b == Some("World"))
    assert(queue.isEmpty)

    val c = queue.take()
    assert(!c.isDefined)
  }

}
