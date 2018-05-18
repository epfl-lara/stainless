
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object split {

  sealed abstract class P
  case object Alice   extends P;
  case object Bob     extends P;
  case object Charlie extends P;

  case class S(who: P, amount: BigInt)

  val spent = List(
    S(Alice   ,     0),
    // S(Bob     ,  3000),
    S(Charlie ,  4000)
  )

  @partialEval
  val all = spent.map(_.who)

  @partialEval
  val pairs = {
    for {
      a <- all
      b <- all
    } yield (a, b)
  } filter { case (a, b) => a != b }

  @partialEval val total     = spent.foldLeft(BigInt(0)) { case (acc, S(_, a)) => acc + a }
  @partialEval val perPerson = total / spent.length
  @partialEval val diff      = spent map { case S(w, a) => S(w, perPerson - a) }
  @partialEval val pos       = diff.filter(_.amount >= 0)
  @partialEval val neg       = diff.filter(_.amount < 0)
  @partialEval val posTotal  = pos.map(_.amount).foldLeft(BigInt(0))(_ + _)
  @partialEval val negTotal  = neg.map(_.amount).foldLeft(BigInt(0))(_ + _)

  type Transfers = List[((P, P), BigInt)]

  def posConstraints(transfers: Transfers): Boolean = {
    val cnstrs = pos map { case S(n, a) =>
      val out = from(n, transfers).map(_._2).foldLeft(BigInt(0))(_ + _)
      fuzEq(out, a)
    }
    cnstrs.foldLeft(true)(_ && _)
  }

  def negConstraints(transfers: Transfers): Boolean = {
    val cnstrs = neg map { case S(n, a) =>
      val inc = to(n, transfers).map(_._2).foldLeft(BigInt(0))(_ + _)
      fuzEq(-inc, a)
    }
    cnstrs.foldLeft(true)(_ && _)
  }

  def theorem(transfers: Transfers): Boolean = {
    val sum = transfers.map(_._2).foldLeft(BigInt(0))(_ + _)

    transfers.length == pairs.length &&
    pairs.forall { pair => transfers.exists(_._1 == pair) } &&
    sum == posTotal &&
    transfers.map(_._1).forall { case (p, q) => p != q } &&
    transfers.forall { case ((p, q), pqa) =>
      val qpa = transfers.find(_._1 == (q, p)).map(_._2)
      qpa.isDefined && (qpa.get == 0 || pqa == 0) && (pqa > 0 || qpa.get > 0)
    } && posConstraints(transfers) && negConstraints(transfers)
  } ensuring { !_ }

  def fuzEq(a: BigInt, b: BigInt): Boolean = {
    a >= b - 50 && a <= b + 50
  }

  def from(n: P, pps: Transfers): Transfers = {
    pps.filter { case ((p, _), _) => p == n }
  }

  def to(n: P, pps: Transfers): Transfers = {
    pps.filter { case ((_, q), _) => q == n }
  }

}
