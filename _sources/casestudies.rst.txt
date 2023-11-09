.. _casestudies:

Case Studies
============

Case Study #1: Proving invariants of actor systems
--------------------------------------------------

Actor system model
~~~~~~~~~~~~~~~~~~

Our model is loosely based on the modern definition of object-based actor systems,
and attempts to provide an idiomatic Scala API in the style of the Akka actor library.

In this framework, each actor is addressed by a reference, through which other actors
can asynchronously send messages. Each actor has an associated behavior, which holds
the state of the actor, if any, and determines

a) the operations which will be performed upon receiving a message
b) what is the next behavior to associate with its reference

A behavior can thus be seen as a data type holding some immutable values representing
the state, and a method which takes in a message, performs some computation which might
involve sending messages to other actors, and finally returns a new behavior.

State at the actor level is thus effectively handled in a functional way, by returning
a new behavior which holds the updated state. An actor system maintains a collection
of one-way channels (inboxes) between any two actors in the system.

An inbox is an ordered list of messages awaiting delivery, the head of the list being
the next message to deliver.

The system drives the execution by non-deterministically
picking a non-empty inbox, taking the first message of the list, and invoking the message
handler of the behavior associated with the destination reference.

It then collects the messages to send, and appends them to the appropriate inboxes,
and update the destination actor’s behavior with the behavior returned by the message handler.

Actor system implementation
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Imports
^^^^^^^

.. code-block:: scala

  import stainless.lang._
  import stainless.collection._
  import stainless.annotation._

Message
^^^^^^^

In our framework, messages are modeled as constructors of the abstract class ``Msg``.

.. code-block:: scala

  abstract class Msg

Actor reference
^^^^^^^^^^^^^^^

Each actor is associated with a persistent reference, modeled as instances of the case class ``ActorRef``.
Each reference has a name, and an underlying Akka ``akka.actor.ActorRef``, marked as extern and pure (see Section :doc:`wrap` for more information about extern fields).

.. code-block:: scala

  case class ActorRef(
    name: String,
    @extern @pure
    underlying: akka.actor.ActorRef
  ) {

    @inline
    def !(msg: Msg)(implicit ctx: ActorContext): Unit = {
      ctx.send(this, msg)
    }
  }

Actor Context
^^^^^^^^^^^^^

When a message is delivered to an actor, the latter is provided with a context, which holds a reference to itself, and a mutable list of messages to send. We mark this list as ghost to avoid having to persist in memory the list of all messages sent through the context.

.. code-block:: scala

  case class ActorContext(
    self: ActorRef,
    @ghost
    var toSend: List[(ActorRef, Msg)] = Nil()
  ) {

    def send(to: ActorRef, msg: Msg): Unit = {
      toSend = (to, msg) :: toSend

      sendUnderlying(to, msg)
    }

    @extern @pure
    private def sendUnderlying(to: ActorRef, msg: Msg): Unit = {
      to.underlying ! msg
    }
  }

Behavior
^^^^^^^^

A behavior specifies both the current state of an actor, and how this one should process the next incoming message. In our framework, these are modeled as a subclass of the abstract class ``Behavior``, which defines a single abstract method ``processMsg``, to be overridden for each defined behavior.

Using the provided ``ActorContext``, the implementation of the ``processMsg`` method can both access its own reference, and send messages. It is also required to return a new ``Behavior`` for handling subsequent messages.

.. code-block:: scala

  sealed abstract class Behavior {
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior
  }

Actor System
^^^^^^^^^^^^

The state of the actor system at a given point in time is modeled as a case class, holding the behavior associated with each actor reference, and the list of in-flight messages between any two actors.

It provides a ``step`` method which, whengiven two ``ActorRef``, will deliver the next message (if any) in the corresponding channel.

Because the ``ActorSystem`` class is only used to model and prove properties about the underlying actor system, we mark the whole class as ghost in order to drop it from the resulting program.

.. code-block:: scala

  @ghost
  case class ActorSystem(
    behaviors: CMap[ActorRef, Behavior],
    inboxes: CMap[(ActorRef, ActorRef), List[Msg]]
  ) {

    def step(from: ActorRef, to: ActorRef): ActorSystem = {
      inboxes(from -> to) match {
        case Nil() =>
          this

        case Cons(msg, msgs) =>
          val (newBehavior, toSend) = deliverMessage(to, msg)

          val newBehaviors = behaviors.updated(to, newBehavior)
          val newInboxes = toSend.foldLeft(inboxes.updated(from -> to, msgs)) {
            case (acc, (dest, m)) => acc.updated(to -> dest, m :: acc(to -> dest))
          }

          ActorSystem(newBehaviors, newInboxes)
      }
    }

    private def deliverMessage(actor: ActorRef, msg: Msg): (Behavior, List[(ActorRef, Msg)]) = {
      val behavior = behaviors(actor)

      val ctx = ActorContext(actor, Nil())
      val nextBehavior = behavior.processMsg(msg)(ctx)

      (nextBehavior, ctx.toSend)
    }
  }

Building a replicated counter
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: scala

  @extern
  def noSender = akka.actor.ActorRef.noSender

  val Primary = ActorRef("primary", noSender)
  val Backup  = ActorRef("backup", noSender)

  case object Inc extends Msg

  case class Counter(value: BigInt) {
    require(value >= 0)

    def increment: Counter = Counter(value + 1)

    def <=(that: Counter): Boolean = this.value <= that.value
  }

  case class PrimBehav(backup: ActorRef, counter: Counter) extends Behavior {
    require(backup.name == "backup")

    override
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
      case Inc =>
        backup ! Inc
        PrimBehav(backup, counter.increment)

      case _ => this
    }
  }

  case class BackBehav(counter: Counter) extends Behavior {

    override
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
      case Inc =>
        BackBehav(counter.increment)

      case _ => this
    }
  }

Proving preservation of an invariant
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

After having defined an actor system with our framework, one might want to verify that this system preserves some invariant between each step of its execution. That is to say, given an invariant ``inv: ActorSystem → Boolean``, for any ``ActorSystem`` `s` and any two ``ActorRef`` `n` and `m`, if ``inv(s)`` holds, then ``inv(s.step(n, m))`` should hold as well. In other words:

:math:`\forall s: \texttt{ActorSystem}, n, m: \texttt{ActorRef}. \texttt{inv}(s) \implies \texttt{inv}(s.\texttt{step}(n, m))`

We note that, because we are essentially doing a proof by induction over execution steps here, one needs also to ensure the invariant holds for some initial system. We show these two properties below:

.. code-block:: scala

  @ghost
  def invariant(s: ActorSystem): Boolean = {
    s.inboxes(Primary -> Primary).isEmpty &&
    s.inboxes(Backup -> Primary).isEmpty &&
    s.inboxes(Backup -> Backup).isEmpty &&
    s.inboxes(Primary -> Backup).forall(_ == Inc) && {
      (s.behaviors(Primary), s.behaviors(Backup)) match {
        case (PrimBehav(_, p), BackBehav(b)) =>
          p.value == b.value + s.inboxes(Primary -> Backup).length

        case _ => false
      }
    }
  }

  @ghost
  def initialSystem = ActorSystem(
    behaviors = CMap({
      case `Primary` => PrimBehav(Counter(0))
      case `Backup`  => BackBehav(Counter(0))
    }),
    inboxes = CMap(_ => List())
  )

  @ghost
  def initialInv = invariant(initialSystem).holds

  @ghost
  def validRef(ref: ActorRef): Boolean = ref == Primary || ref == Backup

  @ghost
  def theorem(s: ActorSystem, from: ActorRef, to: ActorRef): Boolean = {
    require(invariant(s) && validRef(from) && validRef(to))
    val newSystem = s.step(from, to)
    invariant(newSystem)
  }.holds

Running the system with Akka
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: scala

    @ignore
    class ActorWrapper(initialBehavior: Behavior) extends akka.actor.Actor with akka.actor.ActorLogging {

      private def handler(behavior: Behavior): PartialFunction[Any, Unit] = {
        case msg: Msg =>
          val me = ActorRef(context.self.path.name, context.self)
          val ctx = ActorContext(me, Nil())
          val newBehavior = behavior.processMsg(msg)(ctx)

          log.info(s"Received: $msg, becoming $newBehavior")
          context.become(handler(newBehavior), discardOld = true)
      }

      def receive = handler(initialBehavior)
    }

.. code-block:: scala

  @ignore
  def main(args: Array[String]): Unit = {
    val initCounter = Counter(0)

    val system = akka.actor.ActorSystem("Counter")

    val backupRef = ActorRef(
      "backup",
      system.actorOf(
        akka.actor.Props(new ActorWrapper(BackBehav(initCounter))),
        name = "backup"
      )
    )

    val primaryRef = ActorRef(
      "primary",
      system.actorOf(
        akka.actor.Props(new ActorWrapper(PrimBehav(backupRef, initCounter))),
        name = "primary"
      )
    )

    implicit val ctx = ActorContext(primaryRef, Nil())

    import system.dispatcher
    import scala.concurrent.duration._
    system.scheduler.schedule(500.millis, 1000.millis) {
      primaryRef ! Inc
    }
  }
