// Disabled as it requires having Akka on the classpath.

object Actors {
  def disabled = assert(true)
}

// import stainless.lang._
// import stainless.collection._
// import stainless.annotation._

// object actors {

//   abstract class Msg

//   sealed abstract class Behavior {
//     def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior
//   }

//   case class ActorRef(
//     name: String,
//     @extern @pure
//     underlying: akka.actor.ActorRef
//   ) {

//     @inline
//     def !(msg: Msg)(implicit ctx: ActorContext): Unit = {
//       ctx.send(this, msg)
//     }
//   }

//   case class ActorContext(
//     self: ActorRef,
//     @ghost
//     var toSend: List[(ActorRef, Msg)] = Nil()
//   ) {

//     def send(to: ActorRef, msg: Msg): Unit = {
//       toSend = (to, msg) :: toSend
//       sendUnderlying(to, msg)
//     }

//     @extern @pure
//     private def sendUnderlying(to: ActorRef, msg: Msg): Unit = {
//       to.underlying ! msg
//     }
//   }

//   @ghost
//   case class ActorSystem(
//     behaviors: CMap[ActorRef, Behavior],
//     inboxes: CMap[(ActorRef, ActorRef), List[Msg]]
//   ) {

//     def step(from: ActorRef, to: ActorRef): ActorSystem = {
//       inboxes(from -> to) match {
//         case Nil() =>
//           this

//         case Cons(msg, msgs) =>
//           val (newBehavior, toSend) = deliverMessage(to, msg)

//           val newBehaviors = behaviors.updated(to, newBehavior)
//           val newInboxes = toSend.foldLeft(inboxes.updated(from -> to, msgs)) {
//             case (acc, (dest, m)) => acc.updated(to -> dest, m :: acc(to -> dest))
//           }

//           ActorSystem(newBehaviors, newInboxes)
//       }
//     }

//     def deliverMessage(actor: ActorRef, msg: Msg): (Behavior, List[(ActorRef, Msg)]) = {
//       val behavior = behaviors(actor)

//       val ctx = ActorContext(actor, Nil())
//       val nextBehavior = behavior.processMsg(msg)(ctx)

//       (nextBehavior, ctx.toSend)
//     }
//   }

//   @ignore
//   class ActorWrapper(initialBehavior: Behavior) extends akka.actor.Actor with akka.actor.ActorLogging {

//     private def handler(behavior: Behavior): PartialFunction[Any, Unit] = {
//       case msg: Msg =>
//         val me = ActorRef(context.self.path.name, context.self)
//         val ctx = ActorContext(me, Nil())
//         val newBehavior = behavior.processMsg(msg)(ctx)

//         log.info(s"Received: $msg, becoming $newBehavior")
//         context.become(handler(newBehavior), discardOld = true)
//     }

//     def receive = handler(initialBehavior)
//   }

//   case class PrimBehav(backup: ActorRef, counter: Counter) extends Behavior {
//     require(backup.name == "backup")

//     override
//     def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
//       case Inc() =>
//         backup ! Inc()
//         PrimBehav(backup, counter.increment)

//       case _ => this
//     }
//   }

//   case class BackBehav(counter: Counter) extends Behavior {

//     override
//     def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
//       case Inc() =>
//         BackBehav(counter.increment)

//       case _ => this
//     }
//   }

//   @extern
//   def noSender = akka.actor.ActorRef.noSender

//   val Primary = ActorRef("primary", noSender)
//   val Backup  = ActorRef("backup", noSender)

//   case class Inc() extends Msg

//   case class Counter(value: BigInt) {
//     require(value >= 0)

//     def increment: Counter = Counter(value + 1)

//     def <=(that: Counter): Boolean = this.value <= that.value
//   }

//   @ghost
//   def invariant(s: ActorSystem): Boolean = {
//     s.inboxes(Primary -> Primary).isEmpty &&
//     s.inboxes(Backup -> Primary).isEmpty &&
//     s.inboxes(Backup -> Backup).isEmpty &&
//     s.inboxes(Primary -> Backup).forall(_ == Inc()) && {
//       (s.behaviors(Primary), s.behaviors(Backup)) match {
//         case (PrimBehav(_, p), BackBehav(b)) =>
//           p.value == b.value + s.inboxes(Primary -> Backup).length

//         case _ => false
//       }
//     }
//   }

//   def validRef(ref: ActorRef): Boolean = ref == Primary || ref == Backup

//   @ghost
//   def theorem(s: ActorSystem, from: ActorRef, to: ActorRef): Boolean = {
//     require(invariant(s) && validRef(from) && validRef(to))
//     val newSystem = s.step(from, to)
//     invariant(newSystem)
//   }.holds

//   @ignore
//   def main(args: Array[String]): Unit = {
//     val initCounter = Counter(0)

//     val system = akka.actor.ActorSystem("Counter")

//     val backupRef = ActorRef(
//       "backup",
//       system.actorOf(
//         akka.actor.Props(new ActorWrapper(BackBehav(initCounter))),
//         name = "backup"
//       )
//     )

//     val primaryRef = ActorRef(
//       "primary",
//       system.actorOf(
//         akka.actor.Props(new ActorWrapper(PrimBehav(backupRef, initCounter))),
//         name = "primary"
//       )
//     )

//     implicit val ctx = ActorContext(primaryRef, Nil())

//     import system.dispatcher
//     import scala.concurrent.duration._
//     system.scheduler.schedule(500.millis, 1000.millis) {
//       primaryRef ! Inc()
//     }
//   }

// }
