/* Copyright 2009-2022 EPFL, Lausanne */

package stainless
package collection

import scala.collection.immutable.{List => ScalaList}

import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.annotation._

@library
@isabelle.typ(name = "List.list")
sealed abstract class List[T] {

  @isabelle.function(term = "Int.int o List.length")
  def size: BigInt = (this match {
    case Nil() => BigInt(0)
    case Cons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def length = size

  def isize : Int = (this match {
    case Nil() => 0
    case Cons(h, t) => {
      val tSize = t.isize
      if (tSize == Int.MaxValue) tSize
      else 1 + tSize
    }
  }) ensuring(res => 0 <= res && res <= Int.MaxValue)

  @isabelle.function(term = "List.list.set")
  def content: Set[T] = this match {
    case Nil() => Set()
    case Cons(h, t) => Set(h) ++ t.content
  }

  @isabelle.function(term = "List.member")
  def contains(v: T): Boolean = (this match {
    case Cons(h, t) => h == v || t.contains(v)
    case Nil() => false
  }) ensuring { _ == (content contains v) }

  @isabelle.function(term = "List.append")
  def ++(that: List[T]): List[T] = (this match {
    case Nil() => that
    case Cons(x, xs) => Cons(x, xs ++ that)
  }) ensuring { res =>
    (res.content == this.content ++ that.content) &&
    (res.size == this.size + that.size) &&
    (that != Nil[T]() || res == this)
  }

  def head: T = {
    require(this != Nil[T]())
    val Cons(h, _) = this: @unchecked // Be quiet!
    h
  }

  def tail: List[T] = {
    require(this != Nil[T]())
    val Cons(_, t) = this: @unchecked
    t
  }

  @isabelle.fullBody
  def apply(index: BigInt): T = {
    require(0 <= index && index < size)
    if (index == BigInt(0)) {
      head
    } else {
      tail(index-1)
    }
  }.ensuring(contains)

  def iapply(index: Int): T = {
    require(0 <= index && index < isize)
    if (index == 0) {
      head
    } else {
      tail.iapply(index-1)
    }
  }.ensuring(contains)

  @isabelle.function(term = "%xs x. x # xs")
  def ::(t:T): List[T] = Cons(t, this)

  @isabelle.function(term = "%xs x. xs @ [x]")
  def :+(t:T): List[T] = {
    this match {
      case Nil() => Cons(t, this)
      case Cons(x, xs) => Cons(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)) && res == this ++ Cons(t, Nil[T]()))

  @isabelle.function(term = "List.rev")
  def reverse: List[T] = {
    this match {
      case Nil() => this
      case Cons(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: BigInt): List[T] = { (this, i) match {
    case (Nil(), _) => Nil[T]()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        Nil[T]()
      } else {
        Cons(h, t.take(i-1))
      }
  }} ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         BigInt(0)
      else if (i >= this.size) this.size
      else                     i
    ))
  }

  def itake(i: Int): List[T] = {
    require(0 <= i)
    (this, i) match {
      case (Nil(), _) => Nil[T]()
      case (Cons(h, t), i) =>
        if (i <= 0) {
          Nil[T]()
        } else {
          Cons(h, t.itake(i-1))
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.isize == (
       if      (i == 0)         0
       else if (i >= isize)     isize
       else                     i
     ))
  }

  def drop(i: BigInt): List[T] = { (this, i) match {
    case (Nil(), _) => Nil[T]()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        Cons[T](h, t)
      } else {
        t.drop(i-1)
      }
  }} ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         this.size
      else if (i >= this.size) BigInt(0)
      else                     this.size - i
    ))
  }

  def idrop(i: Int): List[T] = {
    require(0 <= i)
    (this, i) match {
      case (Nil(), _) => Nil[T]()
      case (Cons(h, t), i) =>
        if (i <= 0) {
          Cons[T](h, t)
        } else {
          t.idrop(i-1)
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content)
  }

  def slice(from: BigInt, to: BigInt): List[T] = {
    require(0 <= from && from <= to && to <= size)
    drop(from).take(to-from)
  }

  def islice(from: Int, to: Int): List[T] = {
    require(0 <= from && from <= to && to <= isize)
    // idrop(from).itake(to-from)
    this match {
      case Nil() => Nil[T]()
      case Cons(h, t) =>
        if (to == 0) Nil[T]()
        else {
          if (from == 0) {
            Cons[T](h, t.islice(0, to - 1))
          } else {
            t.islice(from - 1, to - 1)
          }
        }
    }
  } ensuring { res =>
    res.content.subsetOf(content) && res.isize == to - from
  }

  def replace(from: T, to: T): List[T] = { this match {
    case Nil() => Nil[T]()
    case Cons(h, t) =>
      val r = t.replace(from, to)
      if (h == from) {
        Cons(to, r)
      } else {
        Cons(h, r)
      }
  }} ensuring { (res: List[T]) =>
    res.size == this.size &&
    res.content == (
      (this.content -- Set(from)) ++
      (if (this.content contains from) Set(to) else Set[T]())
    )
  }

  private def chunk0(s: BigInt, l: List[T], acc: List[T], res: List[List[T]], s0: BigInt): List[List[T]] = {
    require(s > 0 && s0 >= 0)
    l match {
      case Nil() =>
        if (acc.size > 0) {
          res :+ acc
        } else {
          res
        }
      case Cons(h, t) =>
        if (s0 == BigInt(0)) {
          chunk0(s, t, Cons(h, Nil()), res :+ acc, s-1)
        } else {
          chunk0(s, t, acc :+ h, res, s0-1)
        }
    }
  }

  def chunks(s: BigInt): List[List[T]] = {
    require(s > 0)

    chunk0(s, this, Nil(), Nil(), s)
  }

  @isabelle.function(term = "List.zip")
  def zip[B](that: List[B]): List[(T, B)] = { (this, that) match {
    case (Cons(h1, t1), Cons(h2, t2)) =>
      Cons((h1, h2), t1.zip(t2))
    case _ =>
      Nil[(T, B)]()
  }} ensuring { _.size == (
    if (this.size <= that.size) this.size else that.size
  )}

  @isabelle.function(term = "%xs x. removeAll x xs")
  def -(e: T): List[T] = { this match {
    case Cons(h, t) =>
      if (e == h) {
        t - e
      } else {
        Cons(h, t - e)
      }
    case Nil() =>
      Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- Set(e)
  }

  def --(that: List[T]): List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        t -- that
      } else {
        Cons(h, t -- that)
      }
    case Nil() =>
      Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- that.content
  }

  def &(that: List[T]): List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        Cons(h, t & that)
      } else {
        t & that
      }
    case Nil() =>
      Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == (this.content & that.content)
  }

  def padTo(s: BigInt, e: T): List[T] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil(), s) =>
      Cons(e, Nil().padTo(s-1, e))
    case (Cons(h, t), s) =>
      Cons(h, t.padTo(s-1, e))
  }} ensuring { res =>
    if (s <= this.size)
      res == this
    else
      res.size == s &&
      res.content == this.content ++ Set(e)
  }

  def indexOf(elem: T): BigInt = { this match {
    case Nil() => BigInt(-1)
    case Cons(h, t) if h == elem => BigInt(0)
    case Cons(h, t) =>
      val rec = t.indexOf(elem)
      if (rec == BigInt(-1)) BigInt(-1)
      else rec + 1
  }} ensuring { res =>
    (res >= 0) == content.contains(elem) &&
    res < size
  }

  def init: List[T] = {
    require(!isEmpty)
    (this : @unchecked) match {
      case Cons(h, Nil()) =>
        Nil[T]()
      case Cons(h, t) =>
        Cons[T](h, t.init)
    }
  } ensuring ( (r: List[T]) =>
    r.size == this.size - 1 &&
    r.content.subsetOf(this.content)
  )

  def last: T = {
    require(!isEmpty)
    (this : @unchecked) match {
      case Cons(h, Nil()) => h
      case Cons(_, t) => t.last
    }
  } ensuring { this.contains _ }

  def lastOption: Option[T] = { this match {
    case Cons(h, t) =>
      t.lastOption.orElse(Some(h))
    case Nil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def headOption: Option[T] = { this match {
    case Cons(h, t) =>
      Some(h)
    case Nil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def tailOption: Option[List[T]] = { this match {
    case Cons(h, t) =>
      Some(t)
    case Nil() =>
      None[List[T]]()
  }} ensuring { _.isDefined != this.isEmpty }

  def unique: List[T] = this match {
    case Nil() => Nil()
    case Cons(h, t) =>
      Cons(h, t.unique - h)
  }

  def splitAt(e: T): List[List[T]] =  split(Cons(e, Nil()))

  def split(seps: List[T]): List[List[T]] = this match {
    case Cons(h, t) =>
      if (seps.contains(h)) {
        Cons(Nil(), t.split(seps))
      } else {
        val r = t.split(seps)
        Cons(Cons(h, r.head), r.tail)
      }
    case Nil() =>
      Cons(Nil(), Nil())
  }

  def evenSplit: (List[T], List[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def splitAtIndex(index: BigInt) : (List[T], List[T]) = { this match {
    case Nil() => (Nil[T](), Nil[T]())
    case Cons(h, rest) =>
      if (index <= BigInt(0)) {
        (Nil[T](), this)
      } else {
        val (left,right) = rest.splitAtIndex(index - 1)
        (Cons[T](h,left), right)
      }
  }} ensuring { (res:(List[T],List[T])) =>
    res._1 ++ res._2 == this &&
    res._1 == take(index) && res._2 == drop(index)
  }

  def updated(i: BigInt, y: T): List[T] = {
    require(0 <= i && i < this.size)
    (this: @unchecked) match {
      case Cons(x, tail) if i == 0 =>
        Cons[T](y, tail)
      case Cons(x, tail) =>
        Cons[T](x, tail.updated(i - 1, y))
    }
  }.ensuring(res => res.size == this.size && res(i) == y)

  def iupdated(i: Int, y: T): List[T] = {
    require(0 <= i && i < isize)
    (this: @unchecked) match {
      case Cons(x, tail) if i == 0 =>
        Cons[T](y, tail)
      case Cons(x, tail) =>
        Cons[T](x, tail.iupdated(i - 1, y))
    }
  }

  private def insertAtImpl(pos: BigInt, l: List[T]): List[T] = {
    require(0 <= pos && pos <= size)
    if(pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.insertAtImpl(pos-1, l))
        case Nil() =>
          l
      }
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def insertAt(pos: BigInt, l: List[T]): List[T] = {
    require(-pos <= size && pos <= size)
    if(pos < 0) {
      insertAtImpl(size + pos, l)
    } else {
      insertAtImpl(pos, l)
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def insertAt(pos: BigInt, e: T): List[T] = {
    require(-pos <= size && pos <= size)
    insertAt(pos, Cons[T](e, Nil()))
  } ensuring { res =>
    res.size == this.size + 1 &&
    res.content == this.content ++ Set(e)
  }

  private def replaceAtImpl(pos: BigInt, l: List[T]): List[T] = {
    require(0 <= pos && pos <= size)
    if (pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.replaceAtImpl(pos-1, l))
        case Nil() =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def replaceAt(pos: BigInt, l: List[T]): List[T] = {
    require(-pos <= size && pos <= size)
    if(pos < 0) {
      replaceAtImpl(size + pos, l)
    } else {
      replaceAtImpl(pos, l)
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def rotate(s: BigInt): List[T] = {
    if (isEmpty) {
      Nil[T]()
    } else {
      drop(s mod size) ++ take(s mod size)
    }
  } ensuring { res =>
    res.size == this.size
  }

  @isabelle.function(term = "List.null")
  def isEmpty = this match {
    case Nil() => true
    case _ => false
  }

  def nonEmpty = !isEmpty

  // Higher-order API
  @isabelle.function(term = "%xs f. List.list.map f xs")
  def map[R](f: T => R): List[R] = { this match {
    case Nil() => Nil[R]()
    case Cons(h, t) => f(h) :: t.map(f)
  }} ensuring { _.size == this.size }

  @isabelle.function(term = "%bs a f. List.foldl f a bs")
  def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
    case Nil() => z
    case Cons(h,t) => t.foldLeft(f(z,h))(f)
  }

  @isabelle.function(term = "%as b f. List.foldr f as b")
  def foldRight[R](z: R)(f: (T,R) => R): R = this match {
    case Nil() => z
    case Cons(h, t) => f(h, t.foldRight(z)(f))
  }

  def scanLeft[R](z: R)(f: (R,T) => R): List[R] = { this match {
    case Nil() => z :: Nil()
    case Cons(h,t) => z :: t.scanLeft(f(z,h))(f)
  }} ensuring { !_.isEmpty }

  def scanRight[R](z: R)(f: (T,R) => R): List[R] = { this match {
    case Nil() => z :: Nil[R]()
    case Cons(h, t) =>
      val rest@Cons(h1,_) = t.scanRight(z)(f): @unchecked
      f(h, h1) :: rest
  }} ensuring { !_.isEmpty }

  @isabelle.function(term = "List.bind")
  def flatMap[R](f: T => List[R]): List[R] = this match {
    case Nil() => Nil()
    case Cons(h, t) => f(h) ++ t.flatMap(f)
  }

  def filter(p: T => Boolean): List[T] = { this match {
    case Nil() => Nil[T]()
    case Cons(h, t) if p(h) => Cons(h, t.filter(p))
    case Cons(_, t) => t.filter(p)
  }} ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  def filterNot(p: T => Boolean): List[T] =
    filter(!p(_)) ensuring { res =>
      res.size <= this.size &&
      res.content.subsetOf(this.content) &&
      res.forall(!p(_))
    }

  def partition(p: T => Boolean): (List[T], List[T]) = { this match {
    case Nil() => (Nil[T](), Nil[T]())
    case Cons(h, t) =>
      val (l1, l2) = t.partition(p)
      if (p(h)) (h :: l1, l2)
      else      (l1, h :: l2)
  }} ensuring { res =>
    res._1 == filter(p) &&
    res._2 == filterNot(p)
  }

  // In case we implement for-comprehensions
  def withFilter(p: T => Boolean): List[T] = {
    filter(p)
  } ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  @isabelle.function(term = "%xs P. List.list_all P xs")
  def forall(p: T => Boolean): Boolean = this match {
    case Nil() => true
    case Cons(h, t) => p(h) && t.forall(p)
  }

  @isabelle.function(term = "%xs P. List.list_ex P xs")
  def exists(p: T => Boolean) = !forall(!p(_))

  @isabelle.function(term = "%xs P. List.find P xs")
  def find(p: T => Boolean): Option[T] = { this match {
    case Nil() => None[T]()
    case Cons(h, t) => if (p(h)) Some(h) else t.find(p)
  }} ensuring { res => res match {
    case Some(r) => (content contains r) && p(r)
    case None() => true
  }}

  def groupBy[R](f: T => R): Map[R, List[T]] = this match {
    case Nil() => Map.empty[R, List[T]]
    case Cons(h, t) =>
      val key: R = f(h)
      val rest: Map[R, List[T]] = t.groupBy(f)
      val prev: List[T] = if (rest isDefinedAt key) rest(key) else Nil[T]()
      (rest ++ Map((key, h :: prev))) : Map[R, List[T]]
  }

  def takeWhile(p: T => Boolean): List[T] = { this match {
    case Cons(h,t) if p(h) => Cons(h, t.takeWhile(p))
    case _ => Nil[T]()
  }} ensuring { res =>
    (res forall p) &&
    (res.size <= this.size) &&
    (res.content subsetOf this.content)
  }

  def dropWhile(p: T => Boolean): List[T] = { this match {
    case Cons(h,t) if p(h) => t.dropWhile(p)
    case _ => this
  }} ensuring { res =>
    (res.size <= this.size) &&
    (res.content subsetOf this.content) &&
    (res.isEmpty || !p(res.head))
  }

  def count(p: T => Boolean): BigInt = { this match {
    case Nil() => BigInt(0)
    case Cons(h, t) =>
      (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
  }} ensuring {
    _ == this.filter(p).size
  }

  def indexWhere(p: T => Boolean): BigInt = { this match {
    case Nil() => BigInt(-1)
    case Cons(h, _) if p(h) => BigInt(0)
    case Cons(_, t) =>
      val rec = t.indexWhere(p)
      if (rec >= 0) rec + BigInt(1)
      else BigInt(-1)
  }} ensuring {
    _ >= BigInt(0) == (this exists p)
  }

  // Translation to other collections

  def toSet: Set[T] = foldLeft(Set[T]()){
    case (current, next) => current ++ Set(next)
  }

  @extern @pure
  def toScala: ScalaList[T] = foldRight(ScalaList.empty[T])(_ :: _)
}

@library
@isabelle.constructor(name = "List.list.Cons")
case class Cons[T](h: T, t: List[T]) extends List[T]

@library
@isabelle.constructor(name = "List.list.Nil")
case class Nil[T]() extends List[T]

object List {
  @ignore
  def apply[T](elems: T*): List[T] = {
    var l: List[T] = Nil[T]()
    for (e <- elems) {
      l = Cons(e, l)
    }
    l.reverse
  }

  @library
  def empty[T]: List[T] = Nil[T]()

  @library @extern @pure
  def fromScala[A](list: ScalaList[A]): List[A] = {
    list.foldRight(List.empty[A])(_ :: _)
  }

  @library
  def fill[T](n: BigInt)(x: T) : List[T] = {
    if (n <= 0) Nil[T]()
    else Cons[T](x, fill[T](n-1)(x))
  } ensuring(res => (res.content == (if (n <= BigInt(0)) Set.empty[T] else Set(x))) &&
                    res.size == (if (n <= BigInt(0)) BigInt(0) else n))

  /* Range from start (inclusive) to until (exclusive) */
  @library
  def range(start: BigInt, until: BigInt): List[BigInt] = {
    require(start <= until)
    decreases(until - start)
    if(until <= start) Nil[BigInt]() else Cons(start, range(start + 1, until))
  } ensuring{(res: List[BigInt]) => res.size == until - start }

  @library
  def mkString[A](l: List[A], mid: String, f: A => String) = {
    def rec(l: List[A]): String = l match {
      case Nil() => ""
      case Cons(a, b) => mid + f(a) + rec(b)
    }
    l match {
      case Nil() => ""
      case Cons(a, b) => f(a) + rec(b)
    }
  }
}

// 'Cons' Extractor
object :: {
  @library
  def unapply[A](l: List[A]): Option[(A, List[A])] = l match {
    case Nil() => None()
    case Cons(x, xs) => Some((x, xs))
  }
}