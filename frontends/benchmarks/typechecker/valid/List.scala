import stainless._
import stainless.lang._
import stainless.annotation._
import stainless.math._
import stainless.proof._

sealed abstract class LList[T] {

  def size: BigInt = {
    decreases(this)
    this match {
      case LNil() => BigInt(0)
      case LCons(h, t) => 1 + t.size
    }
  } ensuring (_ >= 0)

  def length = size

  def content: Set[T] = {
    decreases(this)
    this match {
      case LNil() => Set()
      case LCons(h, t) => Set(h) ++ t.content
    }
  }

  def contains(v: T): Boolean = {
    decreases(this)
    this match {
      case LCons(h, t) => h == v || t.contains(v)
      case LNil() => false
    }
  } ensuring { _ == (content contains v) }

  def ++(that: LList[T]): LList[T] = {
    decreases(this)
    this match {
      case LNil() => that
      case LCons(x, xs) => LCons(x, xs ++ that)
    }
  } ensuring { res =>
    (res.content == this.content ++ that.content) &&
    (res.size == this.size + that.size) &&
    (that != LNil[T]() || res == this)
  }

  def head: T = {
    require(this != LNil[T]())
    val LCons(h, _) = this
    h
  }

  def tail: LList[T] = {
    require(this != LNil[T]())
    val LCons(_, t) = this
    t
  }

  def apply(index: BigInt): T = {
    require(0 <= index && index < size)
    decreases(this)
    if (index == BigInt(0)) {
      head
    } else {
      tail(index-1)
    }
  }

  def ::(t:T): LList[T] = LCons(t, this)

  def :+(t:T): LList[T] = {
    decreases(this)
    this match {
      case LNil() => LCons(t, this)
      case LCons(x, xs) => LCons(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def reverse: LList[T] = {
    decreases(this)
    this match {
      case LNil() => this
      case LCons(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: BigInt): LList[T] = {
    decreases(this)
    (this, i) match {
      case (LNil(), _) => LNil[T]()
      case (LCons(h, t), i) =>
        if (i <= BigInt(0)) {
          LNil[T]()
        } else {
          LCons(h, t.take(i-1))
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         BigInt(0)
      else if (i >= this.size) this.size
      else                     i
    ))
  }

  def drop(i: BigInt): LList[T] = {
    decreases(this)
    (this, i) match {
      case (LNil(), _) => LNil[T]()
      case (LCons(h, t), i) =>
        if (i <= BigInt(0)) {
          LCons[T](h, t)
        } else {
          t.drop(i-1)
        }
    }
  } ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         this.size
      else if (i >= this.size) BigInt(0)
      else                     this.size - i
    ))
  }

  def slice(from: BigInt, to: BigInt): LList[T] = {
    require(0 <= from && from <= to && to <= size)
    drop(from).take(to-from)
  }

  def replace(from: T, to: T): LList[T] = {
    decreases(this)
    this match {
      case LNil() => LNil[T]()
      case LCons(h, t) =>
        val r = t.replace(from, to)
        if (h == from) {
          LCons(to, r)
        } else {
          LCons(h, r)
        }
    }
  } ensuring { (res: LList[T]) =>
    res.size == this.size &&
    res.content == (
      (this.content -- Set(from)) ++
      (if (this.content contains from) Set(to) else Set[T]())
    )
  }

  private def chunk0(s: BigInt, l: LList[T], acc: LList[T], res: LList[LList[T]], s0: BigInt): LList[LList[T]] = {
    require(s > 0 && s0 >= 0)
    decreases(l)
    l match {
      case LNil() =>
        if (acc.size > 0) {
          res :+ acc
        } else {
          res
        }
      case LCons(h, t) =>
        if (s0 == BigInt(0)) {
          chunk0(s, t, LCons(h, LNil()), res :+ acc, s-1)
        } else {
          chunk0(s, t, acc :+ h, res, s0-1)
        }
    }
  }

  def chunks(s: BigInt): LList[LList[T]] = {
    require(s > 0)

    chunk0(s, this, LNil(), LNil(), s)
  }

  def zip[B](that: LList[B]): LList[(T, B)] = {
    decreases(this)
    (this, that) match {
      case (LCons(h1, t1), LCons(h2, t2)) =>
        LCons((h1, h2), t1.zip(t2))
      case _ =>
        LNil[(T, B)]()
    }
  } ensuring { _.size == (
    if (this.size <= that.size) this.size else that.size
  )}

  def -(e: T): LList[T] = {
    decreases(this)
    this match {
      case LCons(h, t) =>
        if (e == h) {
          t - e
        } else {
          LCons(h, t - e)
        }
      case LNil() =>
        LNil[T]()
    }
  } ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- Set(e)
  }

  def --(that: LList[T]): LList[T] = {
    decreases(this)
    this match {
      case LCons(h, t) =>
        if (that.contains(h)) {
          t -- that
        } else {
          LCons(h, t -- that)
        }
      case LNil() =>
        LNil[T]()
    }
  } ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- that.content
  }

  def &(that: LList[T]): LList[T] = {
    decreases(this)
    this match {
      case LCons(h, t) =>
        if (that.contains(h)) {
          LCons(h, t & that)
        } else {
          t & that
        }
      case LNil() =>
        LNil[T]()
    }
  } ensuring { res =>
    res.size <= this.size &&
    res.content == (this.content & that.content)
  }

  def padTo(s: BigInt, e: T): LList[T] = {
    decreases(if (s > 0) s else BigInt(0))
    (this, s) match {
      case (_, s) if s <= 0 =>
        this
      case (LNil(), s) =>
        LCons(e, LNil().padTo(s-1, e))
      case (LCons(h, t), s) =>
        LCons(h, t.padTo(s-1, e))
    }
  } ensuring { res =>
    if (s <= this.size)
      res == this
    else
      res.size == s &&
      res.content == this.content ++ Set(e)
  }

  def indexOf(elem: T): BigInt = {
    decreases(this)
    this match {
      case LNil() => BigInt(-1)
      case LCons(h, t) if h == elem => BigInt(0)
      case LCons(h, t) =>
        val rec = t.indexOf(elem)
        if (rec == BigInt(-1)) BigInt(-1)
        else rec + 1
    }
  } ensuring { res =>
    (res >= 0) == content.contains(elem)
  }

  def init: LList[T] = {
    require(!isEmpty)
    decreases(this)
    (this : @unchecked) match {
      case LCons(h, LNil()) =>
        LNil[T]()
      case LCons(h, t) =>
        LCons[T](h, t.init)
    }
  } ensuring ( (r: LList[T]) =>
    r.size == this.size - 1 &&
    r.content.subsetOf(this.content)
  )

  def last: T = {
    require(!isEmpty)
    decreases(this)
    (this : @unchecked) match {
      case LCons(h, LNil()) => h
      case LCons(_, t) => t.last
    }
  } ensuring { this.contains _ }

  def lastOption: Option[T] = {
    decreases(this)
    this match {
      case LCons(h, t) =>
        t.lastOption.orElse(Some(h))
      case LNil() =>
        None[T]()
    }
  } ensuring { _.isDefined != this.isEmpty }

  def headOption: Option[T] = { this match {
    case LCons(h, t) =>
      Some(h)
    case LNil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def tailOption: Option[LList[T]] = { this match {
    case LCons(h, t) =>
      Some(t)
    case LNil() =>
      None[LList[T]]()
  }} ensuring { _.isDefined != this.isEmpty }

  def unique: LList[T] = {
    decreases(this)
    this match {
      case LNil() => LNil()
      case LCons(h, t) =>
        LCons(h, t.unique - h)
    }
  }

  def splitAt(e: T): LList[LList[T]] =  split(LCons(e, LNil()))

  def split(seps: LList[T]): LList[LList[T]] = {
    decreases(this)
    this match {
      case LCons(h, t) =>
        if (seps.contains(h)) {
          LCons(LNil(), t.split(seps))
        } else {
          val r = t.split(seps)
          LCons(LCons(h, r.head), r.tail)
        }
      case LNil() =>
        LCons(LNil(), LNil())
    }
  }

  def evenSplit: (LList[T], LList[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def splitAtIndex(index: BigInt) : (LList[T], LList[T]) = {
    decreases(this)
    this match {
      case LNil() => (LNil[T](), LNil[T]())
      case LCons(h, rest) => {
        if (index <= BigInt(0)) {
          (LNil[T](), this)
        } else {
          val (left,right) = rest.splitAtIndex(index - 1)
          (LCons[T](h,left), right)
        }
      }
    }
  } ensuring { (res:(LList[T],LList[T])) =>
    res._1 ++ res._2 == this &&
    res._1 == take(index) && res._2 == drop(index)
  }

  def updated(i: BigInt, y: T): LList[T] = {
    require(0 <= i && i < this.size)
    decreases(this)
    this match {
      case LCons(x, tail) if i == 0 =>
        LCons[T](y, tail)
      case LCons(x, tail) =>
        LCons[T](x, tail.updated(i - 1, y))
    }
  }

  private def insertAtImpl(pos: BigInt, l: LList[T]): LList[T] = {
    require(0 <= pos && pos <= size)
    decreases(pos)
    if(pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case LCons(h, t) =>
          LCons(h, t.insertAtImpl(pos-1, l))
        case LNil() =>
          l
      }
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def insertAt(pos: BigInt, l: LList[T]): LList[T] = {
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

  def insertAt(pos: BigInt, e: T): LList[T] = {
    require(-pos <= size && pos <= size)
    insertAt(pos, LCons[T](e, LNil()))
  } ensuring { res =>
    res.size == this.size + 1 &&
    res.content == this.content ++ Set(e)
  }

  private def replaceAtImpl(pos: BigInt, l: LList[T]): LList[T] = {
    require(0 <= pos && pos <= size)
    decreases(pos)
    if (pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case LCons(h, t) =>
          LCons(h, t.replaceAtImpl(pos-1, l))
        case LNil() =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def replaceAt(pos: BigInt, l: LList[T]): LList[T] = {
    require(-pos <= size && pos <= size)
    if(pos < 0) {
      replaceAtImpl(size + pos, l)
    } else {
      replaceAtImpl(pos, l)
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def rotate(s: BigInt): LList[T] = {
    if (isEmpty) {
      LNil[T]()
    } else {
      drop(s mod size) ++ take(s mod size)
    }
  } ensuring { res =>
    res.size == this.size
  }

  def isEmpty = this match {
    case LNil() => true
    case _ => false
  }

  def nonEmpty = !isEmpty

  // Higher-order API
  def map[R](f: T => R): LList[R] = {
    decreases(this)
    this match {
      case LNil() => LNil[R]()
      case LCons(h, t) => f(h) :: t.map(f)
    }
  } ensuring { _.size == this.size }

  def foldLeft[R](z: R)(f: (R,T) => R): R = {
    decreases(this)
    this match {
      case LNil() => z
      case LCons(h,t) => t.foldLeft(f(z,h))(f)
    }
  }

  def foldRight[R](z: R)(f: (T,R) => R): R = {
    decreases(this)
    this match {
      case LNil() => z
      case LCons(h, t) => f(h, t.foldRight(z)(f))
    }
  }

  def scanLeft[R](z: R)(f: (R,T) => R): LList[R] = {
    decreases(this)
    this match {
      case LNil() => z :: LNil()
      case LCons(h,t) => z :: t.scanLeft(f(z,h))(f)
    }
  } ensuring { !_.isEmpty }

  def scanRight[R](z: R)(f: (T,R) => R): LList[R] = {
    decreases(this)
      this match {
        case LNil() => z :: LNil[R]()
        case LCons(h, t) =>
          val rest@LCons(h1,_) = t.scanRight(z)(f)
          f(h, h1) :: rest
      }
    } ensuring { !_.isEmpty }

  def flatMap[R](f: T => LList[R]): LList[R] =
    LListOps.flatten(this map f)

  def filter(p: T => Boolean): LList[T] = {
    decreases(this)
    this match {
      case LNil() => LNil[T]()
      case LCons(h, t) if p(h) => LCons(h, t.filter(p))
      case LCons(_, t) => t.filter(p)
    }
  } ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  def filterNot(p: T => Boolean): LList[T] =
    filter(!p(_)) ensuring { res =>
      res.size <= this.size &&
      res.content.subsetOf(this.content) &&
      res.forall(!p(_))
    }

  def partition(p: T => Boolean): (LList[T], LList[T]) = {
    decreases(this)
    this match {
      case LNil() => (LNil[T](), LNil[T]())
      case LCons(h, t) =>
        val (l1, l2) = t.partition(p)
        if (p(h)) (h :: l1, l2)
        else      (l1, h :: l2)
    }
  } ensuring { res =>
    res._1 == filter(p) &&
    res._2 == filterNot(p)
  }

  @induct
  def partitionMultiplicity(p: T => Boolean, x: T): Boolean = {
    val (l1, l2) = partition(p)
    count(_ == x) == l1.count(_ == x) + l2.count(_ == x)
  }.holds

  @induct
  def partitionMultiplicity2(p: T => Boolean, p2: T => Boolean): Boolean = {
    val (l1, l2) = partition(p)
    count(p2) == l1.count(p2) + l2.count(p2)
  }.holds

  // In case we implement for-comprehensions
  def withFilter(p: T => Boolean) = filter(p)

  def forall(p: T => Boolean): Boolean = {
    decreases(this)
    this match {
      case LNil() => true
      case LCons(h, t) => p(h) && t.forall(p)
    }
  }

  def exists(p: T => Boolean) = !forall(!p(_))

  def find(p: T => Boolean): Option[T] = {
    decreases(this)
    this match {
      case LNil() => None[T]()
      case LCons(h, t) => if (p(h)) Some(h) else t.find(p)
    }
  } ensuring { res => res match {
    case Some(r) => (content contains r) && p(r)
    case None() => true
  }}

  def groupBy[R](f: T => R): Map[R, LList[T]] = {
    decreases(this)
    this match {
      case LNil() => Map.empty[R, LList[T]]
      case LCons(h, t) =>
        val key: R = f(h)
        val rest: Map[R, LList[T]] = t.groupBy(f)
        val prev: LList[T] = if (rest isDefinedAt key) rest(key) else LNil[T]()
        (rest ++ Map((key, h :: prev))) : Map[R, LList[T]]
    }
  }

  def takeWhile(p: T => Boolean): LList[T] = {
    decreases(this)
    this match {
      case LCons(h,t) if p(h) => LCons(h, t.takeWhile(p))
      case _ => LNil[T]()
    }
  } ensuring { res =>
    (res forall p) &&
    (res.size <= this.size) &&
    (res.content subsetOf this.content)
  }

  def dropWhile(p: T => Boolean): LList[T] = {
    decreases(this)
    this match {
      case LCons(h,t) if p(h) => t.dropWhile(p)
      case _ => this
    }
  } ensuring { res =>
    (res.size <= this.size) &&
    (res.content subsetOf this.content) &&
    (res.isEmpty || !p(res.head))
  }

  def count(p: T => Boolean): BigInt = {
    decreases(this)
    this match {
      case LNil() => BigInt(0)
      case LCons(h, t) =>
        (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
    }
  } ensuring {
    _ == this.filter(p).size
  }

  def indexWhere(p: T => Boolean): BigInt = {
    decreases(this)
    this match {
      case LNil() => BigInt(-1)
      case LCons(h, _) if p(h) => BigInt(0)
      case LCons(_, t) =>
        val rec = t.indexWhere(p)
        if (rec >= 0) rec + BigInt(1)
        else BigInt(-1)
    }
  } ensuring {
    _ >= BigInt(0) == (this exists p)
  }


  // Translation to other collections
  def toSet: Set[T] = foldLeft(Set[T]()){
    case (current, next) => current ++ Set(next)
  }
}

case class LCons[T](h: T, t: LList[T]) extends LList[T]

case class LNil[T]() extends LList[T]

object LList {
  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def fill[T](n: BigInt)(x: T) : LList[T] = {
    decreases(max(n, 0))
    if (n <= 0) LNil[T]()
    else LCons[T](x, fill[T](n-1)(x))
  } ensuring { res =>
    (res.content == (if (n <= BigInt(0)) Set.empty[T] else Set(x))) &&
    res.size == (if (n <= BigInt(0)) BigInt(0) else n)
  }

  /* Range from start (inclusive) to until (exclusive) */
  def range(start: BigInt, until: BigInt): LList[BigInt] = {
    require(start <= until)
    decreases(until - start)
    if(until <= start) LNil[BigInt]() else LCons(start, range(start + 1, until))
  } ensuring{(res: LList[BigInt]) => res.size == until - start }

  def mkString[A](l: LList[A], mid: String, f: A => String) = {
    def rec(l: LList[A]): String = {
      decreases(l)
      l match {
        case LNil() => ""
        case LCons(a, b) => mid + f(a) + rec(b)
      }
    }
    l match {
      case LNil() => ""
      case LCons(a, b) => f(a) + rec(b)
    }
  }
}

object LListOps {
  def flatten[T](ls: LList[LList[T]]): LList[T] = {
    decreases(ls)
    ls match {
      case LCons(h, t) => h ++ flatten(t)
      case LNil() => LNil()
    }
  }

  def isSorted(ls: LList[BigInt]): Boolean = {
    decreases(ls)
    ls match {
      case LNil() => true
      case LCons(_, LNil()) => true
      case LCons(h1, LCons(h2, _)) if(h1 > h2) => false
      case LCons(_, t) => isSorted(t)
    }
  }

  def sorted(ls: LList[BigInt]): LList[BigInt] = {
    decreases(ls)
    ls match {
      case LCons(h, t) => sortedIns(sorted(t), h)
      case LNil() => LNil[BigInt]()
    }
  } ensuring { isSorted _ }

  private def sortedIns(ls: LList[BigInt], v: BigInt): LList[BigInt] = {
    require(isSorted(ls))
    decreases(ls)
    ls match {
      case LNil() => LCons(v, LNil())
      case LCons(h, t) =>
        if (v <= h) {
          LCons(v, ls)
        } else {
          LCons(h, sortedIns(t, v))
        }
    }
  } ensuring { res => isSorted(res) && res.content == ls.content + v }

  def toMap[K, V](l: LList[(K, V)]): Map[K, V] = l.foldLeft(Map[K, V]()){
    case (current, (k, v)) => current ++ Map(k -> v)
  }
}

// 'LCons' Extractor
object :: {
  def unapply[A](l: LList[A]): Option[(A, LList[A])] = l match {
    case LNil() => None()
    case LCons(x, xs) => Some((x, xs))
  }
}


import LListOps._

object LListSpecs {
  def snocIndex[T](l: LList[T], t: T, i: BigInt): Boolean = {
    require(0 <= i && i < l.size + 1)
    decreases(l)
    l match {
      case LNil() => true
      case LCons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
  }.holds

  def consIndex[T](h: T, t: LList[T], i: BigInt): Boolean = {
    require(0 <= i && i < t.size + 1)
    decreases(t)
    check(t.isEmpty || i == 0 || consIndex(h, t.tail, i-1))
    (h :: t).apply(i) == (if (i == 0) h else t.apply(i - 1))
  }.holds

  def reverseIndex[T](l: LList[T], i: BigInt): Boolean = {
    require(0 <= i && i < l.size)
    decreases(l)
    l match {
      case LNil() => true
      case LCons(x,xs) =>
        snocIndex(xs.reverse, x, i) &&
        (if (i < xs.size) consIndex(x, xs, l.size - 1 - i) && reverseIndex[T](xs, i) else true)
    }
    l.reverse.apply(i) == l.apply(l.size - 1 - i)
  }.holds

  def snocLast[T](l: LList[T], x: T): Boolean = {
    decreases(l)

    l match {
      case LNil() => true
      case LCons(y, ys) => {
        ((y :: ys) :+ x).last   ==| trivial         |
        (y :: (ys :+ x)).last   ==| trivial         |
        (ys :+ x).last          ==| snocLast(ys, x) |
        x
      }.qed
    }

    ((l :+ x).last == x)
  }.holds

  def headReverseLast[T](l: LList[T]): Boolean = {
    require (!l.isEmpty)
    (l.head == l.reverse.last)
  }.holds because {
    val LCons(x, xs) = l;
    {
      (x :: xs).head           ==| trivial                 |
      x                        ==| snocLast(xs.reverse, x) |
      (xs.reverse :+ x).last   ==| trivial                 |
      (x :: xs).reverse.last
    }.qed
  }

  def appendIndex[T](l1: LList[T], l2: LList[T], i: BigInt): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    decreases(l1)
    l1 match {
      case LNil() => true
      case LCons(x,xs) =>
        (i != BigInt(0)) ==> appendIndex[T](xs, l2, i - 1)
    }
    (l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size))
  }.holds

  @induct
  def appendAssoc[T](l1: LList[T], l2: LList[T], l3: LList[T]): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  }.holds

  @induct
  def rightUnitAppend[T](l1: LList[T]): Boolean = {
    l1 ++ LNil() == l1
  }.holds

  // This follows immediately from the definition of `++` but we
  // include it here anyway for completeness.
  def leftUnitAppend[T](l1: LList[T]): Boolean = {
    LNil() ++ l1 == l1
  }.holds

  def snocIsAppend[T](l: LList[T], t: T): Boolean = {
    decreases(l)
    l match {
      case LNil() => true
      case LCons(x,xs) => snocIsAppend(xs,t)
    }
    (l :+ t) == l ++ LCons[T](t, LNil())
  }.holds

  def snocAfterAppend[T](l1: LList[T], l2: LList[T], t: T): Boolean = {
    decreases(l1)
    l1 match {
      case LNil() => true
      case LCons(x,xs) => snocAfterAppend(xs,l2,t)
    }
    (l1 ++ l2) :+ t == l1 ++ (l2 :+ t)
  }.holds

  def snocReverse[T](l: LList[T], t: T): Boolean = {
    decreases(l)
    l match {
      case LNil() => true
      case LCons(x,xs) => snocReverse(xs,t)
    }
    (l :+ t).reverse == LCons(t, l.reverse)
  }.holds

  def reverseReverse[T](l: LList[T]): Boolean = {
    decreases(l)
    l match {
      case LNil()       => trivial
      case LCons(x, xs) => {
        (xs.reverse :+ x).reverse ==| snocReverse[T](xs.reverse, x) |
        x :: xs.reverse.reverse   ==| reverseReverse[T](xs)         |
        (x :: xs)
      }.qed
    }
    l.reverse.reverse == l
  }.holds

  def reverseAppend[T](l1: LList[T], l2: LList[T]): Boolean = {
    decreases(l1)
    l1 match {
      case LNil() => {
        (LNil() ++ l2).reverse         ==| trivial                     |
        l2.reverse                    ==| rightUnitAppend(l2.reverse) |
        l2.reverse ++ LNil()           ==| trivial                     |
        l2.reverse ++ LNil().reverse
      }.qed
      case LCons(x, xs) => {
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

  def snocFoldRight[A, B](xs: LList[A], y: A, z: B, f: (A, B) => B): Boolean = {
    decreases(xs)
    xs match {
      case LNil() => true
      case LCons(x, xs) => snocFoldRight(xs, y, z, f)
    }
    (xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f)
  }.holds

  def folds[A, B](xs: LList[A], z: B, f: (B, A) => B): Boolean = {
    decreases(xs)
    val f2 = (x: A, z: B) => f(z, x)
    ( xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2) ) because {
      xs match {
        case LNil() => true
        case LCons(x, xs) => {
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

  def scanVsFoldLeft[A, B](l: LList[A], z: B, f: (B, A) => B): Boolean = {
    decreases(l)
    l match {
      case LNil() => true
      case LCons(x, xs) => scanVsFoldLeft(xs, f(z, x), f)
    }
    ( l.scanLeft(z)(f).last == l.foldLeft(z)(f) )
  }.holds

  @induct
  def scanVsFoldRight[A,B](l: LList[A], z: B, f: (A,B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  def appendContent[A](l1: LList[A], l2: LList[A]) = {
    l1.content ++ l2.content == (l1 ++ l2).content
  }.holds

  def flattenPreservesContent[T](ls: LList[LList[T]]): Boolean = {
    decreases(ls)
    val f: (LList[T], Set[T]) => Set[T] = _.content ++ _
    ( flatten(ls).content == ls.foldRight(Set[T]())(f) ) because {
      ls match {
        case LNil() => true
        case LCons(h, t) => {
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
  def appendUpdate[T](l1: LList[T], l2: LList[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    decreases(l1)

    l1 match {
      case LNil() => true
      case LCons(x, xs) => if (i == 0) true else appendUpdate[T](xs, l2, i - 1, y)
    }

    // lemma
    ((l1 ++ l2).updated(i, y) == (
      if (i < l1.size)
        l1.updated(i, y) ++ l2
      else
        l1 ++ l2.updated(i - l1.size, y)))
  }.holds

  // a lemma about `append`, `take` and `drop`
  def appendTakeDrop[T](l1: LList[T], l2: LList[T], n: BigInt): Boolean = {
    decreases(l1)
    l1 match {
      case LNil() => true
      case LCons(x, xs) => if (n <= 0) true else appendTakeDrop[T](xs, l2, n - 1)
    }
    // lemma
    ((l1 ++ l2).take(n) == (
      if (n < l1.size) l1.take(n)
      else if (n > l1.size) l1 ++ l2.take(n - l1.size)
      else l1)) &&
      ((l1 ++ l2).drop(n) == (
        if (n < l1.size) l1.drop(n) ++ l2
        else if (n > l1.size) l2.drop(n - l1.size)
        else l2))
  }.holds

  // A lemma about `append` and `insertAt`
  def appendInsert[T](l1: LList[T], l2: LList[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    decreases(l1)

    l1 match {
      case LNil() => true
      case LCons(x, xs) => if (i == 0) true else appendInsert[T](xs, l2, i - 1, y)
    }

    // lemma
    (l1 ++ l2).insertAt(i, y) == (
      if (i < l1.size) l1.insertAt(i, y) ++ l2
      else l1 ++ l2.insertAt(i - l1.size, y))
  }.holds

  /** A way to apply the forall axiom */
  def applyForAll[T](l: LList[T], i: BigInt, p: T => Boolean): Boolean = {
    require(i >= 0 && i < l.length && l.forall(p))
    decreases(l)

    l match {
      case LNil() => trivial
      case LCons(head, tail) => if(i == 0) p(head) else applyForAll(l.tail, i - 1, p)
    }

    p(l(i))
  }.holds
}
