package stainless
package covcollection

import scala.collection.immutable.{List => ScalaList}

import stainless.lang.{Option => _, Some => _, None => _, _}
import stainless.lang.StaticChecks._
import stainless.collection.{List => InvList, Nil => InvNil, Cons => InvCons, _}
import stainless.annotation.{wrapping => _, _}
import stainless.proof._
import stainless.math._

@library
sealed abstract class List[+T] {
  def bsize: BigInt = (this match {
    case Nil => BigInt(0)
    case h :: t => 1 + t.bsize
  }) ensuring (_ >= 0)

  def blength: BigInt = bsize

  def size: Int = {
    this match {
      case Nil => 0
      case h :: t =>
        val tLen = t.size
        if (tLen == Int.MaxValue) tLen
        else 1 + tLen
    }
  } ensuring(res => 0 <= res && res <= Int.MaxValue)

  def length: Int = size

  def content[TT >: T]: Set[TT] = this match {
    case Nil => Set[TT]()
    case h :: t => Set[TT](h) ++ t.content[TT]
  }

  def contains[TT >: T](v: TT): Boolean = (this match {
    case h :: t => h == v || t.contains(v)
    case Nil => false
  }) ensuring { _ == (content contains v) }

  def ++[TT >: T](that: List[TT]): List[TT] = {
    this match {
      case Nil => that
      case x :: xs => x :: (xs ++ that)
    }
  }.ensuring { res =>
    (res.content[TT] == this.content[TT] ++ that.content[TT]) &&
      (res.bsize == this.bsize + that.bsize) &&
      (res.size == (if (wrapping(this.size + that.size) < 0) Int.MaxValue else wrapping(this.size + that.size))) &&
      (that != Nil || res == this)
  }

  def head: T = {
    require(this != Nil)
    val h :: _ = this: @unchecked
    h
  }

  def tail: List[T] = {
    require(this != Nil)
    val _ :: t = this: @unchecked
    t
  }

  def bapply(index: BigInt): T = {
    require(0 <= index && index < bsize)
    decreases(index)
    if (index == BigInt(0)) {
      head
    } else {
      tail.bapply(index-1)
    }
  }.ensuring(contains(_))

  def apply(index: Int): T = {
    require(0 <= index && index < size)
    decreases(index)
    if (index == 0) {
      head
    } else {
      tail(index-1)
    }
  }.ensuring(contains(_))

  def :: [TT >: T](elem: TT): List[TT] = new ::(elem, this)

  def :+[TT >: T](t: TT): List[TT] = {
    this match {
      case Nil => t :: this
      case x :: xs => x :: (xs :+ t)
    }
  } ensuring(res =>
    (res.bsize == bsize + 1) &&
      (res.size == (if (wrapping(this.size + 1) < 0) Int.MaxValue else wrapping(this.size + 1))) &&
      (res.content == content ++ Set(t)) &&
      res == this ++ (t :: Nil)
    )

  def reverse: List[T] = {
    this match {
      case Nil => this
      case x :: xs => xs.reverse :+ x
    }
  } ensuring (res =>
    (res.size == size) &&
      (res.bsize == bsize) &&
      (res.content == content)
    )

  def btake(i: BigInt): List[T] = {
    require(0 <= i)
    decreases(i)
    (this, i) match {
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= BigInt(0)) {
          Nil
        } else {
          h :: t.btake(i-1)
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.bsize == (
      if      (i <= 0)         BigInt(0)
      else if (i >= bsize) bsize
      else                     i
      ))
  }

  def take(i: Int): List[T] = {
    require(0 <= i)
    decreases(i)
    (this, i) match {
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= 0) {
          Nil
        } else {
          h :: t.take(i-1)
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i == 0)         0
      else if (i >= size)      size
      else                     i
      ))
  }

  def bdrop(i: BigInt): List[T] = {
    require(0 <= i)
    decreases(i)
    (this, i) match {
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= BigInt(0)) {
          h :: t
        } else {
          t.bdrop(i-1)
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.bsize == (
      if      (i <= 0)          this.bsize
      else if (i >= this.bsize) BigInt(0)
      else                      this.bsize - i
      ))
  }

  def drop(i: Int): List[T] = {
    require(0 <= i)
    decreases(i)
    (this, i) match {
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= 0) {
          h :: t
        } else {
          t.drop(i-1)
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content)
  }

  def bslice(from: BigInt, to: BigInt): List[T] = {
    require(0 <= from && from <= to && to <= bsize)
    bdrop(from).btake(to-from)
  }

  def slice(from: Int, to: Int): List[T] = {
    require(0 <= from && from <= to && to <= size)
    this match {
      case Nil => Nil
      case h :: t =>
        if (to == 0) Nil
        else {
          if (from == 0) {
            h :: t.slice(0, to - 1)
          } else {
            t.slice(from - 1, to - 1)
          }
        }
    }
  } ensuring { res =>
    res.content.subsetOf(content) && res.size == to - from
  }

  def replace[TT >: T](from: TT, to: TT): List[TT] = { this match {
    case Nil => Nil
    case h :: t =>
      val r = t.replace(from, to)
      if (h == from) {
        to :: r
      } else {
        h :: r
      }
  }} ensuring { (res: List[TT]) =>
    res.size == this.size &&
      res.bsize == this.bsize &&
      res.content[TT] == (
        (this.content -- Set(from)) ++
          (if (this.content contains from) Set(to) else Set[TT]())
        )
  }

  private def bchunk0[TT >: T](s: BigInt, l: List[TT], acc: List[TT], res: List[List[TT]], s0: BigInt): List[List[TT]] = {
    require(s > 0 && s0 >= 0)
    l match {
      case Nil =>
        if (acc.size > 0) {
          res :+ acc
        } else {
          res
        }
      case h :: t =>
        if (s0 == BigInt(0)) {
          bchunk0(s, t, h :: Nil, res :+ acc, s-1)
        } else {
          bchunk0(s, t, acc :+ h, res, s0-1)
        }
    }
  }

  def bchunks(s: BigInt): List[List[T]] = {
    require(s > 0)
    bchunk0(s, this, Nil, Nil, s)
  }

  def zip[B](that: List[B]): List[(T, B)] = {
    decreases(this)
    (this, that) match {
      case (h1 :: t1, h2 :: t2) =>
        (h1, h2) :: t1.zip(t2)
      case _ =>
        Nil
    }
  } ensuring { res =>
    res.size == (if (this.size <= that.size) this.size else that.size) &&
      res.bsize == (if (this.bsize <= that.bsize) this.bsize else that.bsize)
  }

  def -[TT >: T](e: TT): List[TT] = { this match {
    case h :: t =>
      if (e == h) {
        t - e
      } else {
        h :: (t - e)
      }
    case Nil => Nil
  }} ensuring { res =>
    res.size <= this.size &&
      res.bsize <= this.bsize &&
      res.content[TT] == this.content[TT] -- Set(e)
  }

  def --[TT >: T](that: List[TT]): List[TT] = { this match {
    case h :: t =>
      if (that.contains(h)) {
        t -- that
      } else {
        h :: (t -- that)
      }
    case Nil => Nil
  }} ensuring { res =>
    res.size <= this.size &&
      res.bsize <= this.bsize &&
      res.content[TT] == this.content[TT] -- that.content[TT]
  }

  def &[TT >: T](that: List[TT]): List[TT] = { this match {
    case h :: t =>
      if (that.contains(h)) {
        h :: (t & that)
      } else {
        t & that
      }
    case Nil => Nil
  }} ensuring { res =>
    res.size <= this.size &&
      res.bsize <= this.bsize &&
      res.content[TT] == (this.content[TT] & that.content[TT])
  }

  def bpadTo[TT >: T](s: BigInt, e: TT): List[TT] = {
    decreases(max(s, 0))
    (this, s) match {
      case (_, s) if s <= 0 =>
        this
      case (Nil, s) =>
        e :: (Nil: List[T]).bpadTo(s-1, e)
      case (h :: t, s) =>
        h :: t.bpadTo(s-1, e)
    }
  } ensuring { res =>
    if (s <= this.bsize)
      res == this
    else
      res.bsize == s &&
        res.content[TT] == this.content[TT] ++ Set(e)
  }

  def indexOf[TT >: T](elem: TT): Int = {
    this match {
      case Nil => -1
      case h :: t if h == elem => 0
      case h :: t =>
        val rec = t.indexOf(elem)
        if (rec == -1) -1
        else if (rec == Int.MaxValue) Int.MaxValue
        else rec + 1
    }
  } ensuring { res =>
    (res >= 0) == content.contains(elem) &&
    res <= size
  }

  def bindexOf[TT >: T](elem: TT): BigInt = { this match {
    case Nil => BigInt(-1)
    case h :: t if h == elem => BigInt(0)
    case h :: t =>
      val rec = t.bindexOf(elem)
      if (rec == BigInt(-1)) BigInt(-1)
      else rec + 1
  }} ensuring { res =>
    (res >= 0) == content.contains(elem) &&
    res < bsize
  }

  def init: List[T] = {
    require(!isEmpty)
    (this : @unchecked) match {
      case h :: Nil =>
        Nil
      case h :: t =>
        h :: t.init
    }
  } ensuring ( (r: List[T]) =>
    r.size <= this.size &&
      r.bsize == this.bsize - 1 &&
      r.content.subsetOf(this.content)
    )

  def last: T = {
    require(!isEmpty)
    (this : @unchecked) match {
      case h :: Nil => h
      case _ :: t => t.last
    }
  } ensuring { this.contains[T](_) }

  def lastOption: Option[T] = { this match {
    case h :: t =>
      t.lastOption.orElse(Some(h))
    case Nil =>
      None
  }} ensuring { _.isDefined != this.isEmpty }

  def headOption: Option[T] = { this match {
    case h :: t =>
      Some(h)
    case Nil =>
      None
  }} ensuring { _.isDefined != this.isEmpty }


  def tailOption: Option[List[T]] = { this match {
    case h :: t =>
      Some(t)
    case Nil =>
      None
  }} ensuring { _.isDefined != this.isEmpty }

  def unique: List[T] = this match {
    case Nil => Nil
    case h :: t =>
      h :: (t.unique - h)
  }

  def splitAtElem[TT >: T](e: TT): List[List[TT]] =  splitElem(e :: Nil)

  def splitElem[TT >: T](seps: List[TT]): List[List[TT]] = this match {
    case h :: t =>
      if (seps.contains(h)) {
        Nil :: t.splitElem(seps)
      } else {
        val r = t.splitElem(seps)
        (h :: r.head) :: r.tail
      }
    case Nil =>
      Nil :: Nil
  }

  def evenSplit: (List[T], List[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def bsplitAt(index: BigInt) : (List[T], List[T]) = {
    require(0 <= index && index < bsize)
    this match {
      case Nil => (Nil, Nil)
      case h :: rest =>
        if (index <= BigInt(0)) {
          (Nil, this)
        } else {
          val (left,right) = rest.bsplitAt(index - 1)
          (h :: left, right)
        }
    }
  } ensuring { (res: (List[T],List[T])) =>
    res._1 ++ res._2 == this &&
      res._1 == btake(index) && res._2 == bdrop(index)
  }

  def bupdated[TT >: T](i: BigInt, y: TT): List[TT] = {
    require(0 <= i && i < bsize)
    (this: @unchecked) match {
      case x :: tail if i == 0 =>
        y :: tail
      case x :: tail =>
        x :: tail.bupdated(i - 1, y)
    }
  }

  def updated[TT >: T](i: Int, y: TT): List[TT] = {
    require(0 <= i && i < size)
    (this: @unchecked) match {
      case x :: tail if i == 0 =>
        y :: tail
      case x :: tail =>
        x :: tail.updated(i - 1, y)
    }
  }

  private def binsertAtImpl[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
    require(0 <= pos && pos <= bsize)
    decreases(pos)
    if(pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case h :: t =>
          h :: t.binsertAtImpl(pos-1, l)
        case Nil =>
          l
      }
    }
  } ensuring { res =>
    res.size == (if (wrapping(this.size + l.size) < 0) Int.MaxValue else wrapping(this.size + l.size)) &&
      res.bsize == this.bsize + l.bsize &&
      res.content == this.content ++ l.content
  }

  def binsertAt[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
    require(-pos <= bsize && pos <= bsize)
    if(pos < 0) {
      binsertAtImpl(bsize + pos, l)
    } else {
      binsertAtImpl(pos, l)
    }
  } ensuring { res =>
    res.size == (if (wrapping(this.size + l.size) < 0) Int.MaxValue else wrapping(this.size + l.size)) &&
      res.bsize == this.bsize + l.bsize &&
      res.content == this.content ++ l.content
  }

  def binsertAt[TT >: T](pos: BigInt, e: TT): List[TT] = {
    require(-pos <= bsize && pos <= bsize)
    binsertAt(pos, e :: Nil)
  } ensuring { res =>
    res.size == (if (wrapping(this.size + 1) < 0) Int.MaxValue else wrapping(this.size + 1)) &&
      res.bsize == this.bsize + 1 &&
      res.content == this.content ++ Set(e)
  }

  private def breplaceAtImpl[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
    require(0 <= pos && pos <= bsize)
    decreases(pos)
    if (pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case h :: t =>
          h :: t.breplaceAtImpl(pos-1, l)
        case Nil =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def breplaceAt[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
    require(-pos <= bsize && pos <= bsize)
    if(pos < 0) {
      breplaceAtImpl(bsize + pos, l)
    } else {
      breplaceAtImpl(pos, l)
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def brotate(s: BigInt): List[T] = {
    if (isEmpty) {
      Nil
    } else {
      bdrop(s mod bsize) ++ btake(s mod bsize)
    }
  } ensuring { res =>
    res.bsize == this.bsize
  }

  def isEmpty: Boolean = this match {
    case Nil => true
    case _ => false
  }

  def nonEmpty: Boolean = !isEmpty

  // Higher-order API
  def map[R](f: T => R): List[R] = { this match {
    case Nil => Nil
    case h :: t => f(h) :: t.map(f)
  }} ensuring { _.size == this.size }

  def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
    case Nil => z
    case h :: t => t.foldLeft(f(z,h))(f)
  }

  def foldRight[R](z: R)(f: (T,R) => R): R = this match {
    case Nil => z
    case h :: t => f(h, t.foldRight(z)(f))
  }

  def scanLeft[R](z: R)(f: (R,T) => R): List[R] = { this match {
    case Nil => z :: Nil
    case h :: t => z :: t.scanLeft(f(z,h))(f)
  }} ensuring { !_.isEmpty }

  def scanRight[R](z: R)(f: (T,R) => R): List[R] = { this match {
    case Nil => z :: Nil
    case h :: t =>
      val rest@(h1 :: _) = t.scanRight(z)(f): @unchecked
      f(h, h1) :: rest
  }} ensuring { !_.isEmpty }

  def flatMap[R](f: T => List[R]): List[R] =
    ListOps.flatten(this map f)

  def filter(p: T => Boolean): List[T] = { this match {
    case Nil => Nil
    case h :: t if p(h) => h :: t.filter(p)
    case _ :: t => t.filter(p)
  }} ensuring { res =>
    res.size <= this.size &&
      res.bsize <= this.bsize &&
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
    case Nil => (Nil, Nil)
    case h :: t =>
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
      res.bsize <= this.bsize &&
      res.content.subsetOf(this.content) &&
      res.forall(p)
  }

  def forall(p: T => Boolean): Boolean = this match {
    case Nil => true
    case h :: t => p(h) && t.forall(p)
  }

  def exists(p: T => Boolean): Boolean = !forall(!p(_))

  def find(p: T => Boolean): Option[T] = { this match {
    case Nil => None
    case h :: t => if (p(h)) Some(h) else t.find(p)
  }} ensuring { res => res match {
    case Some(r) => (content contains r) && p(r)
    case None => true
  }}

  def groupBy[TT >: T, R](f: TT => R): Map[R, List[TT]] = this match {
    case Nil => Map.empty[R, List[TT]]
    case h :: t =>
      val key: R = f(h)
      val rest: Map[R, List[TT]] = t.groupBy(f)
      val prev: List[TT] = if (rest isDefinedAt key) rest(key) else Nil
      (rest ++ Map((key, h :: prev))) : Map[R, List[TT]]
  }

  def takeWhile(p: T => Boolean): List[T] = { this match {
    case h :: t if p(h) => h :: t.takeWhile(p)
    case _ => Nil
  }} ensuring { res =>
    (res forall p) &&
      (res.size <= this.size) &&
      (res.bsize <= this.bsize) &&
      (res.content subsetOf this.content)
  }

  def dropWhile(p: T => Boolean): List[T] = { this match {
    case h :: t if p(h) => t.dropWhile(p)
    case _ => this
  }} ensuring { res =>
    (res.size <= this.size) &&
      (res.bsize <= this.bsize) &&
      (res.content subsetOf this.content) &&
      (res.isEmpty || !p(res.head))
  }

  def count(p: T => Boolean): Int = {
    this match {
      case Nil => 0
      case h :: t =>
        val r = t.count(p)
        if (r == Int.MaxValue) Int.MaxValue
        else r + (if (p(h)) 1 else 0)
    }
  } ensuring {
    _ == this.filter(p).size
  }

  def bcount(p: T => Boolean): BigInt = { this match {
    case Nil => BigInt(0)
    case h :: t =>
      (if (p(h)) BigInt(1) else BigInt(0)) + t.bcount(p)
  }} ensuring {
    _ == this.filter(p).bsize
  }

  def indexWhere(p: T => Boolean): Int = {
    this match {
      case Nil => -1
      case h :: _ if p(h) => 0
      case _ :: t =>
        val rec = t.indexWhere(p)
        if (rec == Int.MaxValue) Int.MaxValue
        else if (rec >= 0) rec + 1
        else -1
    }
  } ensuring {
    _ >= 0 == (this exists p)
  }

  def bindexWhere(p: T => Boolean): BigInt = { this match {
    case Nil => BigInt(-1)
    case h :: _ if p(h) => BigInt(0)
    case _ :: t =>
      val rec = t.bindexWhere(p)
      if (rec >= 0) rec + BigInt(1)
      else BigInt(-1)
  }} ensuring {
    _ >= BigInt(0) == (this exists p)
  }

  // Translation to other collections
  def toSet[TT >: T]: Set[TT] = foldLeft(Set[TT]()){
    case (current, next) => current ++ Set[TT](next)
  }

  def toInvariantList[TT >: T]: InvList[TT] = foldRight(InvNil[TT](): InvList[TT])(_ :: _)

  @extern @pure
  def toScala: ScalaList[T] = foldRight(ScalaList.empty[T])(_ :: _)
}

@library
case object Nil extends List[Nothing]

@library
final case class ::[+A](first: A, next: List[A]) extends List[A]

object List {
  @ignore
  def apply[T](elems: T*): List[T] = {
    var l: List[T] = Nil
    for (e <- elems) {
      l = e :: l
    }
    l.reverse
  }

  @library
  def empty[T]: List[T] = Nil

  @library
  @extern @pure
  def fromScala[A](list: ScalaList[A]): List[A] = {
    list.foldRight(List.empty[A])(_ :: _)
  }

  @library
  def fill[T](n: Int)(x: T) : List[T] = {
    decreases(max(n, 0))
    if (n <= 0) Nil
    else x :: fill[T](n-1)(x)
  } ensuring(res => (res.content[T] == (if (n <= 0) Set.empty[T] else Set(x))) &&
    res.size == (if (n <= 0) 0 else n))

  @library
  def bfill[T](n: BigInt)(x: T) : List[T] = {
    decreases(max(n, 0))
    if (n <= 0) Nil
    else x :: bfill[T](n-1)(x)
  } ensuring(res => (res.content[T] == (if (n <= BigInt(0)) Set.empty[T] else Set(x))) &&
    res.bsize == (if (n <= BigInt(0)) BigInt(0) else n))

  /* Range from start (inclusive) to until (exclusive) */
  @library
  def range(start: Int, until: Int): List[Int] = {
    require(start <= until)
    require(wrapping(until - start) >= 0)
    decreases(until - start)
    if(until <= start) Nil else start :: range(start + 1, until)
  } ensuring{(res: List[Int]) => res.size == until - start }

  @library
  def brange(start: BigInt, until: BigInt): List[BigInt] = {
    require(start <= until)
    decreases(until - start)
    if(until <= start) Nil else start :: brange(start + 1, until)
  } ensuring{(res: List[BigInt]) => res.bsize == until - start }

  @library
  def mkString[A](l: List[A], mid: String, f: A => String) = {
    def rec(l: List[A]): String = l match {
      case Nil => ""
      case a :: b => mid + f(a) + rec(b)
    }
    l match {
      case Nil => ""
      case a :: b => f(a) + rec(b)
    }
  }

  @library
  implicit class ListBigIntOps(l: List[BigInt]) {
    def sum: BigInt = ListOps.sum(l)
    def sorted: List[BigInt] = ListOps.sorted(l)
    def isSorted: Boolean = ListOps.isSorted(l)
  }

  @library
  implicit class FlattenableList[A](l: List[List[A]]) {
    def flatten: List[A] = ListOps.flatten(l)
  }

  @library
  implicit class ToMapOps[K, V](l: List[(K, V)]) {
    def toMap: Map[K, V] = ListOps.toMap(l)
  }
}

@library
object ListOps {
  def flatten[T](ls: List[List[T]]): List[T] = ls match {
    case h :: t => h ++ flatten(t)
    case Nil => Nil
  }

  def isSorted(ls: List[BigInt]): Boolean = ls match {
    case Nil => true
    case _ :: Nil => true
    case h1 :: h2 :: _ if h1 > h2 => false
    case _ :: t => isSorted(t)
  }

  def sorted(ls: List[BigInt]): List[BigInt] = { ls match {
    case h :: t => sortedIns(sorted(t), h)
    case Nil => Nil
  }} ensuring(isSorted)

  private def sortedIns(ls: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(ls))
    ls match {
      case Nil =>
        v :: Nil
      case h :: t =>
        if (v <= h) {
          v :: ls
        } else {
          h :: sortedIns(t, v)
        }
    }
  } ensuring { res => isSorted(res) }

  def sum(l: List[BigInt]): BigInt = l.foldLeft(BigInt(0))(_ + _)

  def toMap[K, V](l: List[(K, V)]): Map[K, V] = l.foldLeft(Map[K, V]()){
    case (current, (k, v)) => current ++ Map(k -> v)
  }

  def noDuplicate[T](l: List[T]): Boolean = l match {
    case Nil => true
    case h :: t => !t.contains(h) && noDuplicate(t)
  }
}

import ListOps._

@library
object ListSpecs {

  def snocIndex[T](l: List[T], t: T, i: BigInt): Boolean = {
    require(0 <= i && i < l.bsize + 1)
    decreases(l)
    l match {
      case Nil => true
      case x :: xs => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }
    ((l :+ t).bapply(i) == (if (i < l.bsize) l.bapply(i) else t))
  }.holds

  def consIndex[T](h: T, t: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < t.bsize + 1)
    decreases(t)
    check(t.isEmpty || i == 0 || consIndex(h, t.tail, i-1))
    (h :: t).bapply(i) == (if (i == 0) h else t.bapply(i - 1))
  }.holds

  def reverseIndex[T](l: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.bsize)
    decreases(l)
    l match {
      case Nil => true
      case x :: xs =>
        snocIndex(xs.reverse, x, i) &&
          (if (i < xs.bsize) consIndex(x, xs, l.bsize - 1 - i) && reverseIndex[T](xs, i) else true)
    }
    l.reverse.bapply(i) == l.bapply(l.bsize - 1 - i)
  }.holds

  def snocLast[T](l: List[T], x: T): Boolean = {
    decreases(l)

    l match {
      case Nil => true
      case y :: ys => {
        ((y :: ys) :+ x).last   ==| trivial         |
          (y :: (ys :+ x)).last   ==| trivial         |
          (ys :+ x).last          ==| snocLast(ys, x) |
          x
      }.qed
    }

    ((l :+ x).last == x)
  }.holds

  def headReverseLast[T](l: List[T]): Boolean = {
    require (!l.isEmpty)
    (l.head == l.reverse.last)
  }.holds because {
    val x :: xs = l: @unchecked;
    {
      (x :: xs).head           ==| trivial                 |
        x                        ==| snocLast(xs.reverse, x) |
        (xs.reverse :+ x).last   ==| trivial                 |
        (x :: xs).reverse.last
    }.qed
  }

  def appendIndex[T](l1: List[T], l2: List[T], i: BigInt): Boolean = {
    require(0 <= i && i < l1.bsize + l2.bsize)
    decreases(l1)
    l1 match {
      case Nil => true
      case x :: xs =>
        (i != BigInt(0)) ==> appendIndex[T](xs, l2, i - 1)
    }
    (l1 ++ l2).bapply(i) == (if (i < l1.bsize) l1.bapply(i) else l2.bapply(i - l1.bsize))
  }.holds

  def appendAssoc[T](@induct l1: List[T], l2: List[T], l3: List[T]): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  }.holds

  def rightUnitAppend[T](@induct l1: List[T]): Boolean = {
    l1 ++ Nil == l1
  }.holds

  // This follows immediately from the definition of `++` but we
  // include it here anyway for completeness.
  def leftUnitAppend[T](l1: List[T]): Boolean = {
    Nil ++ l1 == l1
  }.holds

  def snocIsAppend[T](l: List[T], t: T): Boolean = {
    decreases(l)
    l match {
      case Nil => true
      case x :: xs => snocIsAppend(xs,t)
    }
    (l :+ t) == l ++ (t :: Nil)
  }.holds

  def snocAfterAppend[T](l1: List[T], l2: List[T], t: T): Boolean = {
    decreases(l1)
    l1 match {
      case Nil => true
      case x :: xs => snocAfterAppend(xs,l2,t)
    }
    (l1 ++ l2) :+ t == l1 ++ (l2 :+ t)
  }.holds

  def snocReverse[T](l: List[T], t: T): Boolean = {
    decreases(l)
    l match {
      case Nil => true
      case x :: xs => snocReverse(xs,t)
    }
    (l :+ t).reverse == t :: l.reverse
  }.holds

  def reverseReverse[T](l: List[T]): Boolean = {
    decreases(l)
    l match {
      case Nil       => trivial
      case x :: xs => {
        (xs.reverse :+ x).reverse ==| snocReverse[T](xs.reverse, x) |
          x :: xs.reverse.reverse   ==| reverseReverse[T](xs)         |
          (x :: xs)
      }.qed
    }
    l.reverse.reverse == l
  }.holds

  def reverseAppend[T](l1: List[T], l2: List[T]): Boolean = {
    decreases(l1)
    l1 match {
      case Nil => {
        (Nil ++ l2).reverse         ==| trivial                     |
          l2.reverse                    ==| rightUnitAppend(l2.reverse) |
          l2.reverse ++ Nil           ==| trivial                     |
          l2.reverse ++ Nil.reverse
      }.qed
      case x :: xs => {
        ((x :: xs) ++ l2).reverse         ==| trivial               |
          (x :: (xs ++ l2)).reverse         ==| trivial               |
          (xs ++ l2).reverse :+ x           ==| reverseAppend(xs, l2) |
          (l2.reverse ++ xs.reverse) :+ x   ==|
            snocAfterAppend(l2.reverse, xs.reverse, x)                |
          l2.reverse ++ (xs.reverse :+ x)   ==| trivial               |
          l2.reverse ++ (x :: xs).reverse
      }.qed
    }
    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse
  }.holds

  def snocFoldRight[A, B](xs: List[A], y: A, z: B, f: (A, B) => B): Boolean = {
    decreases(xs)
    xs match {
      case Nil => true
      case x :: xs => snocFoldRight(xs, y, z, f)
    }
    (xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f)
  }.holds

  def folds[A, B](xs: List[A], z: B, f: (B, A) => B): Boolean = {
    decreases(xs)
    val f2 = (x: A, z: B) => f(z, x)
    ( xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2) ) because {
      xs match {
        case Nil => true
        case x :: xs => {
          (x :: xs).foldLeft(z)(f)              ==| trivial               |
            xs.foldLeft(f(z, x))(f)               ==| folds(xs, f(z, x), f) |
            xs.reverse.foldRight(f(z, x))(f2)     ==| trivial               |
            xs.reverse.foldRight(f2(x, z))(f2)    ==|
              snocFoldRight(xs.reverse, x, z, f2)                           |
            (xs.reverse :+ x).foldRight(z)(f2)    ==| trivial               |
            (x :: xs).reverse.foldRight(z)(f2)
        }.qed
      }
    }
  }.holds

  def scanVsFoldLeft[A, B](l: List[A], z: B, f: (B, A) => B): Boolean = {
    decreases(l)
    l match {
      case Nil => true
      case x :: xs => scanVsFoldLeft(xs, f(z, x), f)
    }
    ( l.scanLeft(z)(f).last == l.foldLeft(z)(f) )
  }.holds

  def scanVsFoldRight[A,B](@induct l: List[A], z: B, f: (A,B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  def appendContent[A](l1: List[A], l2: List[A]) = {
    l1.content ++ l2.content == (l1 ++ l2).content
  }.holds

  def flattenPreservesContent[T](ls: List[List[T]]): Boolean = {
    decreases(ls)
    val f: (List[T], Set[T]) => Set[T] = _.content ++ _
    ( flatten(ls).content[T] == ls.foldRight(Set[T]())(f) ) because {
      ls match {
        case Nil => true
        case h :: t => {
          flatten(h :: t).content                     ==| trivial                       |
            (h ++ flatten(t)).content                   ==| appendContent(h, flatten(t))  |
            h.content ++ flatten(t).content             ==| flattenPreservesContent(t)    |
            h.content ++ t.foldRight(Set[T]())(f)       ==| trivial                       |
            f(h, Set[T]()) ++ t.foldRight(Set[T]())(f)  ==| trivial                       |
            (h :: t).foldRight(Set[T]())(f)
        }.qed
      }
    }
  }.holds

  // A lemma about `append` and `updated`
  def appendUpdate[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.bsize + l2.bsize)
    decreases(l1)

    l1 match {
      case Nil => true
      case x :: xs => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }

    // lemma
    ((l1 ++ l2).bupdated(i, y) == (
      if (i < l1.bsize)
        l1.bupdated(i, y) ++ l2
      else
        l1 ++ l2.bupdated(i - l1.bsize, y)))
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T](l1: List[T], l2: List[T], n: BigInt): Boolean = {
    require(n >= 0)
    decreases(l1)
    l1 match {
      case Nil => true
      case x :: xs => if (n == 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }
    // lemma
    ((l1 ++ l2).btake(n) == (
      if (n < l1.bsize) l1.btake(n)
      else if (n > l1.bsize) l1 ++ l2.btake(n - l1.bsize)
      else l1)) &&
      ((l1 ++ l2).bdrop(n) == (
        if (n < l1.bsize) l1.bdrop(n) ++ l2
        else if (n > l1.bsize) l2.bdrop(n - l1.bsize)
        else l2))
  }.holds
  /*
  // A lemma about `append` and `insertAt`
  def appendInsert[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.bsize + l2.bsize)
    decreases(l1)

    l1 match {
      case Nil => true
      case x :: xs =>
        if (i == 0) true
        else {
          appendInsert[T](xs, l2, i - 1, y)
          check(
            (xs ++ l2).binsertAt(i - 1, y) == (
              if (i - 1 < xs.bsize) xs.binsertAt(i - 1, y) ++ l2
              else xs ++ l2.binsertAt(i - xs.bsize - 1, y))
          )
        }
    }

    // lemma
    (l1 ++ l2).binsertAt(i, y) == (
      if (i < l1.bsize) l1.binsertAt(i, y) ++ l2
      else l1 ++ l2.binsertAt(i - l1.bsize, y))
  }.holds
  */
  /** A way to apply the forall axiom */
  def applyForAll[T](l: List[T], i: BigInt, p: T => Boolean): Boolean = {
    require(i >= 0 && i < l.bsize && l.forall(p))
    decreases(l)

    l match {
      case Nil => trivial
      case head :: tail => if(i == 0) p(head) else applyForAll(l.tail, i - 1, p)
    }

    p(l.bapply(i))
  }.holds

  def listFilterValidProp[A](l: List[A], p: A => Boolean, f: A => Boolean): Unit = {
    require(l.forall(p))
    l match {
      case Nil =>
      case x :: xs =>
        assert(xs.forall(p))
        listFilterValidProp(xs, p, f)
    }
  }.ensuring(_ => l.filter(f).forall(p))

  def listAppendValidProp[A](l: List[A], as: List[A], p: A => Boolean): Unit = {
    require(l.forall(p) && as.forall(p))
    as match {
      case Nil => ()
      case x :: xs =>
        assert(xs.forall(p))
        listAppendValidProp(l, xs, p)
    }
  }.ensuring(_ => (as ++ l).forall(p))

  @opaque
  def mapPred[A,B](l: List[A], f: A => B, p: B => Boolean): Unit = {
    require(l.forall(a => p(f(a))))
    l match {
      case Nil => ()
      case x :: xs =>
        assert(xs.forall(a => p(f(a))))
        mapPred(xs, f, p)
    }
  }.ensuring(_ => l.map(f).forall(p))

  @opaque
  def subsetContains[T](l1: List[T], l2: List[T]): Unit = {
    require(l1.content.subsetOf(l2.content))
    l1 match {
      case Nil => ()
      case x :: xs =>
        assert(xs.content.subsetOf(l2.content))
        subsetContains(xs, l2)
    }
  }.ensuring(_ => l1.forall(l2.contains[T]))

  @inline
  def noDuplicate[T](l: List[T]): Boolean = ListOps.noDuplicate(l)

  @opaque
  def forallContained[T](l: List[T], p: T => Boolean, x: T): Unit = {
    require(l.forall(p) && l.contains(x))
    decreases(l.bsize)
    if (!l.isEmpty && l.tail.contains(x))
      forallContained(l.tail, p, x)

  }.ensuring(_ => p(x))

  @opaque
  def subsetContained[T](l1: List[T], l2: List[T], x: T): Unit = {
    require(l1.forall(l2.contains[T]) && l1.contains(x))
    forallContained(l1, l2.contains[T], x)
  }.ensuring(_ =>
    l2.contains(x)
  )

  def subseq[T](l1: List[T], l2: List[T]): Boolean = {
    decreases(l2.bsize)
    (l1, l2) match {
      case (Nil, _) => true
      case (x :: xs, y :: ys) =>
        (x == y && subseq(xs, ys)) ||
          subseq(l1, ys)
      case _ => false
    }
  }

  def subseqTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subseq(l1, l2))
    decreases(l2.bsize)

    (l1, l2) match {
      case (x :: xs, y :: ys) =>
        if (subseq(l1, ys))
          subseqTail(l1, ys)
        else if (!xs.isEmpty)
          subseqTail(xs, ys)
      case _ =>
        ()
    }

  }.ensuring(_ =>
    subseq(l1.tail, l2)
  )

  @opaque
  def subseqContains[T](l1: List[T], l2: List[T], t: T): Unit = {
    require(subseq(l1, l2) && l1.contains(t))
    decreases(l2.bsize)
    (l1, l2) match {
      case (x :: xs, y :: ys) =>
        if (subseq(l1, ys))
          subseqContains(l1, ys, t)
        else if (x != t)
          subseqContains(xs, ys, t)
      case _ =>
        ()
    }

  }.ensuring(_ =>
    l2.contains(t)
  )

  @opaque
  def subseqNotContains[T](l1: List[T], l2: List[T], t: T): Unit = {
    require(subseq(l1, l2) && !l2.contains(t))
    decreases(l1)
    if (l1.contains(t))
      subseqContains(l1, l2, t)

  }.ensuring(_ =>
    !l1.contains(t)
  )

  @opaque
  def noDuplicateSubseq[T](l1: List[T], l2: List[T]): Unit = {
    decreases(l2.bsize)
    require(subseq(l1, l2) && noDuplicate(l2))

    (l1, l2) match {
      case (Nil, _) =>
        ()
      case (x :: xs, y :: ys) =>
        if (subseq(l1, ys)) {
          noDuplicateSubseq(l1, ys)
          check(noDuplicate(l1))
          ()
        } else {
          assert(x == y)
          noDuplicateSubseq(xs, ys)
          assert(noDuplicate(xs))
          assert(subseq(xs, ys))
          assert(!ys.contains(x))
          subseqNotContains(xs, ys, x)
          check(noDuplicate(l1))
          ()
        }
      case _ =>
        ()
    }
  }.ensuring(_ =>
    noDuplicate(l1)
  )

  @opaque
  def mapSubseq[A, B](l1: List[A], l2: List[A], f: A => B): Unit = {
    decreases(l2.bsize)
    require(subseq(l1, l2))

    (l1, l2) match {
      case (x :: xs, y :: ys) =>
        if (subseq(l1, ys))
          mapSubseq(l1, ys, f)
        else
          mapSubseq(xs, ys, f)
      case _ =>
        ()
    }

  }.ensuring(_ => subseq(l1.map(f), l2.map(f)))

  @opaque
  def filterSubseq[A](@induct l: List[A], p: A => Boolean): Unit = {

  }.ensuring(_ => subseq(l.filter(p), l))

  @opaque
  def noDuplicateMapFilter[A, B](l: List[A], p: A => Boolean, f: A => B): Unit = {
    require(noDuplicate(l.map(f)))

    filterSubseq(l, p)
    mapSubseq(l.filter(p), l, f)
    noDuplicateSubseq(l.filter(p).map(f), l.map(f))

  }.ensuring(_ =>
    noDuplicate(l.filter(p).map(f))
  )

  @opaque
  def filterMapNotIn[A, B](@induct l: List[(A, B)], a: A): Unit = {

  }.ensuring(_ =>
    !l.filter(_._1 != a).map(_._1).contains(a)
  )

  @opaque
  def containedTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l2.isEmpty && l1.forall(l2.tail.contains[T]))
    l1 match {
      case Nil => ()
      case x :: xs =>
        assert(xs.forall(l2.tail.contains[T]))
        containedTail(xs, l2)
    }
  }.ensuring(_ =>
    l1.forall(l2.contains[T])
  )

  @opaque
  def subsetRefl[T](l: List[T]): Unit = {
    decreases(l.bsize)
    if (!l.isEmpty) {
      subsetRefl(l.tail)
      containedTail(l.tail, l)
    }
  }.ensuring(_ =>
    l.forall(l.contains[T])
  )

  @opaque
  def forallContainsSubset[T](l1: List[T], l2: List[T]): Unit = {
    require(l1.forall(l2.contains[T]))
    decreases(l1)
    if (!l1.isEmpty) {
      forallContainsSubset(l1.tail, l2) // gives us:
      assert(l1.tail.content.subsetOf(l2.content))
    }
  }.ensuring(_ =>
    l1.content.subsetOf(l2.content)
  )

}