package withOrb

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import invariant._

// Higher-order API
sealed abstract class List {

  def size: BigInt = (this match {
    case Nil() => BigInt(0)
    case Cons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def length = size

  /**
   * A function that is the sum of time taken by 'f' when applied over the elements of the list.
   * Note: here `f` can update state.
   */
  def listTime(f: BigInt => BigInt): BigInt = {
    this match {
      case Nil() => BigInt(0)
      case Cons(x, t) =>
        1 + time(f(x)) +
        (f(x) match {
          case _ => t.listTime(f)
        })
    }
  } ensuring(_ >= 0)

  def map(f: BigInt => BigInt): List = { this match {
    case Nil() => Nil()
    case Cons(h, t) => Cons(f(h), t.map(f))
  }} ensuring {
    val in = inSt
    steps <= ? * (listTime(f) in in) + ?
  }

  /*def foldLeft(z: BigInt)(f: (BigInt,BigInt) => BigInt): BigInt = this match {
    case Nil() => z
    case Cons(h,t) => t.foldLeft(f(z,h))(f)
  }

  def scanLeft(z: BigInt)(f: (BigInt,BigInt) => BigInt): List = { this match {
    case Nil() => z :: Nil()
    case Cons(h,t) => z :: t.scanLeft(f(z,h))(f)
  }} ensuring { !_.isEmpty }

  def flatMap(f: BigInt => List): List =
    ListOps.flatten(this map f)

  def filter(p: BigInt => Boolean): List[BigInt] = { this match {
    case Nil() => Nil[BigInt]()
    case Cons(h, t) if p(h) => Cons(h, t.filter(p))
    case Cons(_, t) => t.filter(p)
  }} ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  def groupBy(f: BigInt => BigInt): Map[BigInt, List[BigInt]] = this match {
    case Nil() => Map.empty[BigInt, List[BigInt]]
    case Cons(h, t) =>
      val key: BigInt = f(h)
      val rest: Map[BigInt, List[BigInt]] = t.groupBy(f)
      val prev: List[BigInt] = if (rest isDefinedAt key) rest(key) else Nil[BigInt]()
      (rest ++ Map((key, h :: prev))) : Map[BigInt, List[BigInt]]
  }*/
}

case class Cons(h: BigInt, t: List) extends List

case class Nil() extends List

object Client {

  def id(x: BigInt): BigInt = x

  /**
   * listTime reduces to size when given a constant function
   */
  @induct
  def listTimeLemma(l: List, f: BigInt => BigInt): Boolean = {
    require(f.is(id _))
    l.listTime(f) <= 2* l.size
  }

  def client(l: List) = {
    require(listTimeLemma(l, id _))
    l.map(id _)
  } ensuring(_ => steps <= ? * l.size + ?)
}