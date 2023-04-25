package stainless
package covcollection

import scala.collection.immutable.{List => ScalaList}

import stainless.lang.{Option => _, Some => _, None => _, _}
import stainless.lang.StaticChecks._
import stainless.collection.{List => InvList, Nil => InvNil, Cons => InvCons, _}
import stainless.annotation._
import stainless.proof._

@library
sealed abstract class List[+T] {
  def size: BigInt = (this match {
    case Nil => BigInt(0)
    case h :: t => 1 + t.size
  }) ensuring (_ >= 0)

  def length: BigInt = size

  def isize: Int = {
    this match {
      case Nil => 0
      case h :: t =>
        val tLen = t.isize
        if (tLen == Int.MaxValue) tLen
        else 1 + tLen
    }
  } ensuring(res => 0 <= res && res <= Int.MaxValue)

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
    (res.size == this.size + that.size) &&
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

  def apply(index: BigInt): T = {
    require(0 <= index && index < size)
    if (index == BigInt(0)) {
      head
    } else {
      tail(index-1)
    }
  }

  def iapply(index: Int): T = {
    require(0 <= index && index < isize)
    if (index == 0) {
      head
    } else {
      tail.iapply(index-1)
    }
  }

  def :: [TT >: T](elem: TT): List[TT] = new ::(elem, this)

  def :+[TT >: T](t: TT): List[TT] = {
    this match {
      case Nil => t :: this
      case x :: xs => x :: (xs :+ t)
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)) && res == this ++ (t :: Nil))

  def reverse: List[T] = {
    this match {
      case Nil => this
      case x :: xs => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: BigInt): List[T] = { (this, i) match {
    case (Nil, _) => Nil
    case (h :: t, i) =>
      if (i <= BigInt(0)) {
        Nil
      } else {
        h :: t.take(i-1)
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
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= 0) {
          Nil
        } else {
          h :: t.itake(i-1)
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
    case (Nil, _) => Nil
    case (h :: t, i) =>
      if (i <= BigInt(0)) {
        h :: t
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
      case (Nil, _) => Nil
      case (h :: t, i) =>
        if (i <= 0) {
          h :: t
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
      case Nil => Nil
      case h :: t =>
        if (to == 0) Nil
        else {
          if (from == 0) {
            h :: t.islice(0, to - 1)
          } else {
            t.islice(from - 1, to - 1)
          }
        }
    }
  } ensuring { res =>
    res.content.subsetOf(content) && res.isize == to - from
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
    res.content[TT] == (
      (this.content -- Set(from)) ++
      (if (this.content contains from) Set(to) else Set[TT]())
    )
  }

  private def chunk0[TT >: T](s: BigInt, l: List[TT], acc: List[TT], res: List[List[TT]], s0: BigInt): List[List[TT]] = {
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
          chunk0(s, t, h :: Nil, res :+ acc, s-1)
        } else {
          chunk0(s, t, acc :+ h, res, s0-1)
        }
    }
  }

  def chunks(s: BigInt): List[List[T]] = {
    require(s > 0)
    chunk0(s, this, Nil, Nil, s)
  }

  def zip[B](that: List[B]): List[(T, B)] = { (this, that) match {
    case (h1 :: t1, h2 :: t2) =>
      (h1, h2) :: t1.zip(t2)
    case _ =>
      Nil
  }} ensuring { _.size == (
    if (this.size <= that.size) this.size else that.size
  )}

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
    res.content[TT] == (this.content[TT] & that.content[TT])
  }

  def padTo[TT >: T](s: BigInt, e: TT): List[TT] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil, s) =>
      e :: (Nil: List[T]).padTo(s-1, e)
    case (h :: t, s) =>
      h :: t.padTo(s-1, e)
  }} ensuring { res =>
    if (s <= this.size)
      res == this
    else
      res.size == s &&
      res.content[TT] == this.content[TT] ++ Set(e)
  }

  def indexOf[TT >: T](elem: TT): BigInt = { this match {
    case Nil => BigInt(-1)
    case h :: t if h == elem => BigInt(0)
    case h :: t =>
      val rec = t.indexOf(elem)
      if (rec == BigInt(-1)) BigInt(-1)
      else rec + 1
  }} ensuring { res =>
    (res >= 0) == content.contains(elem)
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
    r.size == this.size - 1 &&
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

  def splitAt[TT >: T](e: TT): List[List[TT]] =  split(e :: Nil)

  def split[TT >: T](seps: List[TT]): List[List[TT]] = this match {
    case h :: t =>
      if (seps.contains(h)) {
        Nil :: t.split(seps)
      } else {
        val r = t.split(seps)
        (h :: r.head) :: r.tail
      }
    case Nil =>
      Nil :: Nil
  }

  def evenSplit: (List[T], List[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def splitAtIndex(index: BigInt) : (List[T], List[T]) = { this match {
    case Nil => (Nil, Nil)
    case h :: rest =>
      if (index <= BigInt(0)) {
        (Nil, this)
      } else {
        val (left,right) = rest.splitAtIndex(index - 1)
        (h :: left, right)
      }
  }} ensuring { (res: (List[T],List[T])) =>
    res._1 ++ res._2 == this &&
    res._1 == take(index) && res._2 == drop(index)
  }

  def updated[TT >: T](i: BigInt, y: TT): List[TT] = {
    require(0 <= i && i < this.size)
    (this: @unchecked) match {
      case x :: tail if i == 0 =>
        y :: tail
      case x :: tail =>
        x :: tail.updated(i - 1, y)
    }
  }

  def iupdated[TT >: T](i: Int, y: TT): List[TT] = {
    require(0 <= i && i < isize)
    (this: @unchecked) match {
      case x :: tail if i == 0 =>
        y :: tail
      case x :: tail =>
        x :: tail.iupdated(i - 1, y)
    }
  }

  private def insertAtImpl[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
    require(0 <= pos && pos <= size)
    if(pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case h :: t =>
          h :: t.insertAtImpl(pos-1, l)
        case Nil =>
          l
      }
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def insertAt[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
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

  def insertAt[TT >: T](pos: BigInt, e: TT): List[TT] = {
    require(-pos <= size && pos <= size)
    insertAt(pos, e :: Nil)
  } ensuring { res =>
    res.size == this.size + 1 &&
    res.content == this.content ++ Set(e)
  }

  private def replaceAtImpl[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
    require(0 <= pos && pos <= size)
    if (pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case h :: t =>
          h :: t.replaceAtImpl(pos-1, l)
        case Nil =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def replaceAt[TT >: T](pos: BigInt, l: List[TT]): List[TT] = {
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
      Nil
    } else {
      drop(s mod size) ++ take(s mod size)
    }
  } ensuring { res =>
    res.size == this.size
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
    (res.content subsetOf this.content)
  }

  def dropWhile(p: T => Boolean): List[T] = { this match {
    case h :: t if p(h) => t.dropWhile(p)
    case _ => this
  }} ensuring { res =>
    (res.size <= this.size) &&
    (res.content subsetOf this.content) &&
    (res.isEmpty || !p(res.head))
  }

  def count(p: T => Boolean): BigInt = { this match {
    case Nil => BigInt(0)
    case h :: t =>
      (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
  }} ensuring {
    _ == this.filter(p).size
  }

  def indexWhere(p: T => Boolean): BigInt = { this match {
    case Nil => BigInt(-1)
    case h :: _ if p(h) => BigInt(0)
    case _ :: t =>
      val rec = t.indexWhere(p)
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
  def fill[T](n: BigInt)(x: T) : List[T] = {
    if (n <= 0) Nil
    else x :: fill[T](n-1)(x)
  } ensuring(res => (res.content[T] == (if (n <= BigInt(0)) Set.empty[T] else Set(x))) &&
                    res.size == (if (n <= BigInt(0)) BigInt(0) else n))

  /* Range from start (inclusive) to until (exclusive) */
  @library
  def range(start: BigInt, until: BigInt): List[BigInt] = {
    require(start <= until)
    decreases(until - start)
    if(until <= start) Nil else start :: range(start + 1, until)
  } ensuring{(res: List[BigInt]) => res.size == until - start }

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
