.. _ghost:

Ghost Context
=============

Introduction
------------

When verifying code, one often needs to introduce lemmas, auxiliary functions,
additional fields and parameters, and contracts, whose only function is to specify
and prove that some properties are satisfied by the program.

.. code-block:: scala

  import stainless.lang._
  import stainless.lang.collection._
  import stainless.lang.annotation._

  def isSorted(list: List[BigInt]): Boolean = list match {
    case Nil()                            => true
    case Cons(_, Nil())                   => true
    case Cons(x1, Cons(x2, _)) if x1 > x2 => false
    case Cons(_, xs)                      => isSorted(xs)
  }

  def sort(list: List[BigInt]): List[BigInt] = {
    /* ... */
  } ensuring { res =>
    res.contents == list.contents &&
    isSorted(res) &&
    res.size == l.size
  }

One can alleviate this issue by adding the following import:


.. code-block:: scala

  import stainless.lang.StaticChecks._


Ghost annotation
----------------

Correctness check
-----------------

As part of the verification pipeline, Stainless will check that it never
encounters a *ghost expression* outside of a *ghost context*. Should
the check fail, verification will fail and compilation will be aborted.

A *ghost expression* is any of:

- Call to a ghost method
- Selection of a ghost field
- Instantiation of a ghost class
- Reference to a ghost variable

A *ghost context* as any of:

- Body of a ghost method
- Argument to a ghost parameter (method or class constructor)
- Assignment to a ghost variable
- Anywhere where a value of type ``Unit`` is expected

Ghost expression elimination
----------------------------

If the correctness check described in the previous section succeeds, the sbt plugin
will then proceed to eliminate ghost methods and expressions from the programs.

Case study
----------

.. code-block:: scala

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

    def test = {
      val queue = MsgQueue.empty[String]

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
