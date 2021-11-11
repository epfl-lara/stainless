import stainless.lang._
import stainless.collection._
import stainless.annotation._

object Counter {

  import Actors._

  case class PrimBehav(backup: ActorRef, counter: Counter) extends Behavior {
    require(backup.name == "backup")

    override
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
      case Inc() =>
        backup ! Inc()
        PrimBehav(backup, counter.increment)

      case _ => this
    }
  }

  case class BackBehav(counter: Counter) extends Behavior {

    override
    def processMsg(msg: Msg)(implicit ctx: ActorContext): Behavior = msg match {
      case Inc() =>
        BackBehav(counter.increment)

      case _ => this
    }
  }

  @extern @pure
  def noSender = akka.actor.ActorRef.noSender

  val Primary = ActorRef("primary", noSender)
  val Backup  = ActorRef("backup", noSender)

  case class Inc() extends Msg

  case class Counter(value: BigInt) {
    require(value >= 0)

    def increment: Counter = Counter(value + 1)

    def <=(that: Counter): Boolean = this.value <= that.value
  }

  @ghost
  def invariant(s: ActorSystem): Boolean = {
    s.inboxes(Primary -> Primary).isEmpty &&
    s.inboxes(Backup -> Primary).isEmpty &&
    s.inboxes(Backup -> Backup).isEmpty &&
    s.inboxes(Primary -> Backup).forall(_ == Inc()) && {
      (s.behaviors(Primary), s.behaviors(Backup)) match {
        case (PrimBehav(_, p), BackBehav(b)) =>
          p.value == b.value + s.inboxes(Primary -> Backup).length

        case _ => false
      }
    }
  }

  def validRef(ref: ActorRef): Boolean = ref == Primary || ref == Backup

  @ghost
  def theorem(s: ActorSystem, from: ActorRef, to: ActorRef): Boolean = {
    require(invariant(s) && validRef(from) && validRef(to))
    val newSystem = s.step(from, to)
    invariant(newSystem)
  }.holds

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

    implicit val ctx: ActorContext = ActorContext(primaryRef, Nil())

    import system.dispatcher
    import scala.concurrent.duration._
    system.scheduler.schedule(500.millis, 1000.millis) {
      primaryRef ! Inc()
    }
  }

}