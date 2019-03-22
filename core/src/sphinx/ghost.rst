.. _ghost:

Ghost State
===========

Introduction
------------

.. code-block:: scala

  import stainless.lang._
  import stainless.collection._
  import stainless.annotation._

  import java.util.concurrent.ConcurrentLinkedDeque

  case class MsgQueue[A](
    @extern queue: ConcurrentLinkedDeque[A],
    @ghost var msgs: List[A]
  ) {
    def put(msg: A): Unit = {
      msgs = msg :: msgs
      _put(msg)
    }

    @extern
    private def _put(msg: A): Unit = {
      queue.addFirst(msg)
    }

    def take(): Option[A] = {
      msgs = msgs match {
        case Nil() => Nil()
        case Cons(_, tail) => tail
      }

      _take()
    } ensuring { _ == old(msgs).headOption }

    @extern
    private def _take(): Option[A] = {
      Option(queue.pollFirst())
    } ensuring { res => res == msgs.headOption }
  }

  object MsgQueue {
    @extern @pure
    def empty[A]: MsgQueue[A] = {
      MsgQueue(new ConcurrentLinkedDeque(), Nil())
    }
  }
