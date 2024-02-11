package stainless
package covcollection

import scala.collection.immutable.{List => ScalaList}

import stainless.lang.{Option => _, Some => _, None => _, _}
import stainless.lang.StaticChecks._
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

  def flatMap[R](f: T => List[R]): List[R] = this match {
    case Nil => Nil
    case h :: t => f(h) ++ t.flatMap(f)
  }

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
}