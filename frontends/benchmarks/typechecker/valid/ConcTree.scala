package conctrees
// By Ravi Kandhadai Madhavan @ LARA, EPFL. (c) EPFL

import stainless.collection._
import stainless.lang._
import ListSpecs._
import stainless.annotation._

object ConcTrees {

  @inline
  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  sealed abstract class Conc[T] {

    def isEmpty: Boolean = {
      this == Empty[T]()
    }

    def isLeaf: Boolean = {
      this match {
        case Empty()   => true
        case Single(_) => true
        case _         => false
      }
    }

    @inline
    def valid: Boolean = {
      decreases(this, 1)
      concInv && balanced
    }

    /**
     * (a) left and right trees of conc node should be non-empty
     * (b) they cannot be append nodes
     */
    def concInv: Boolean = {
      decreases(this, 0)
      this match {
        case CC(l, r) =>
          !l.isEmpty && !r.isEmpty &&
            l.concInv && r.concInv
        case _ => true
      }
    }

    def balanced: Boolean = {
      decreases(this, 0)
      this match {
        case CC(l, r) =>
          l.level - r.level >= -1 && l.level - r.level <= 1 &&
            l.balanced && r.balanced
        case _ => true
      }
    }

    val level: BigInt = {
      decreases(this)
      (this match {
        case Empty()   => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)

    val size: BigInt = {
      decreases(this)
      (this match {
        case Empty()   => 0
        case Single(x) => 1
        case CC(l, r) =>
          l.size + r.size
      }): BigInt
    } ensuring (_ >= 0)

    def toList: List[T] = {
      decreases(this)
      this match {
        case Empty()   => Nil[T]()
        case Single(x) => Cons(x, Nil[T]())
        case CC(l, r) =>
          l.toList ++ r.toList // note: left elements precede the right elements in the list
      }
    } ensuring (res => res.size == this.size)
  }

  case class Empty[T]() extends Conc[T]
  case class Single[T](x: T) extends Conc[T]
  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]

  /*class Chunk(val array: Array[T], val size: Int, val k: Int) extends Leaf[T] {
    def level = 0
    override def toString = s"Chunk(${array.mkString("", ", ", "")}; $size; $k)"
  }*/

  def lookup[T](xs: Conc[T], i: BigInt): T = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    decreases(xs)
    xs match {
      case Single(x) => x
      case CC(l, r) =>
        if (i < l.size) lookup(l, i)
        else lookup(r, i - l.size)
    }
  } ensuring (res =>
    // axiom instantiation
    instAppendIndexAxiom(xs, i) &&
      res == xs.toList(i)) // lookup time is linear in the height

  def instAppendIndexAxiom[T](xs: Conc[T], i: BigInt): Boolean = {
    require(0 <= i && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case _ => true
    }
  }.holds

  def update[T](xs: Conc[T], i: BigInt, y: T): Conc[T] = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    decreases(xs)
    xs match {
      case Single(x) => Single(y)
      case CC(l, r) =>
        if (i < l.size) CC(update(l, i, y), r)
        else CC(l, update(r, i - l.size, y))
    }
  } ensuring (res => instAppendUpdateAxiom(xs, i, y) && // an auxiliary axiom instantiation
    res.level == xs.level && // heights of the input and output trees are equal
    res.valid && // tree invariants are preserved
    res.toList == xs.toList.updated(i, y)) // update time is linear in the height of the tree

  def instAppendUpdateAxiom[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  /**
   * A generic concat that applies to general concTrees
   */
  //  def concat[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
  //    require(xs.valid && ys.valid)
  //    concatNormalized(normalize(xs), normalize(ys))
  //  }

  def concatNonEmpty[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid && !xs.isEmpty && !ys.isEmpty)
    decreases(xs,ys)
    val diff = ys.level - xs.level
    if (diff >= -1 && diff <= 1) CC(xs, ys)
    else if (diff < -1) { // ys is smaller than xs
      xs match {
        case CC(l, r) =>
          if (l.level >= r.level)
            CC(l, concatNonEmpty(r, ys))
          else {
            r match {
              case CC(rl, rr) =>
                val nrr = concatNonEmpty(rr, ys)
                if (nrr.level == xs.level - 3)
                  CC(l, CC(rl, nrr))
                else
                  CC(CC(l, rl), nrr)
            }
          }
      }
    } else ys match {
      case CC(l, r) =>
        if (r.level >= l.level)
          CC(concatNonEmpty(xs, l), r)
        else {
          l match {
            case CC(ll, lr) =>
              val nll = concatNonEmpty(xs, ll)
              if (nll.level == ys.level - 3)
                CC(CC(nll, lr), r)
              else
                CC(nll, CC(lr, r))
          }
        }
    }
  } ensuring (res =>
    res.level <= max(xs.level, ys.level) + 1 && // height invariants
      res.level >= max(xs.level, ys.level) &&
      res.valid &&
      appendAssocInst(xs, ys) && // instantiation of an axiom
      concatCorrectness(res, xs, ys)) // time bounds

  def appendAssocInst[T](xs: Conc[T], ys: Conc[T]): Boolean = {
    (xs match {
      case CC(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList) && //instantiation of associativity of concatenation
          (r match {
            case CC(rl, rr) =>
              appendAssoc(rl.toList, rr.toList, ys.toList) &&
                appendAssoc(l.toList, rl.toList, rr.toList ++ ys.toList)
            case _ => true
          })
      case _ => true
    }) &&
      (ys match {
        case CC(l, r) =>
          appendAssoc(xs.toList, l.toList, r.toList) &&
            (l match {
              case CC(ll, lr) =>
                appendAssoc(xs.toList, ll.toList, lr.toList) &&
                  appendAssoc(xs.toList ++ ll.toList, lr.toList, r.toList)
              case _ => true
            })
        case _ => true
      })
  }.holds

  /**
   * This concat applies only to normalized trees.
   * This prevents concat from being recursive
   */
  def concatNormalized[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid)
    (xs, ys) match {
      case (xs, Empty()) => xs
      case (Empty(), ys) => ys
      case _             => concatNonEmpty(xs, ys)
    }
  } ensuring (res => res.valid && // tree invariants
    res.level <= max(xs.level, ys.level) + 1 && // height invariants
    res.level >= max(xs.level, ys.level) &&
    concatCorrectness(res, xs, ys))

  def concatCorrectness[T](res: Conc[T], xs: Conc[T], ys: Conc[T]): Boolean =
    (res.toList == xs.toList ++ ys.toList)

  def insert[T](xs: Conc[T], i: BigInt, y: T): Conc[T] = {
    require(xs.valid && i >= 0 && i <= xs.size) //note the precondition
    decreases(xs)
    xs match {
      case Empty() => Single(y)
      case Single(x) =>
        if (i == 0) CC(Single(y), xs)
        else CC(xs, Single(y))
      case CC(l, r) =>
        if (i < l.size)
          concatNonEmpty(insert(l, i, y), r)
        else
          concatNonEmpty(l, insert(r, i - l.size, y))
    }
  } ensuring (res =>
    res.valid && // tree invariants
      res.level - xs.level <= 1 && res.level >= xs.level && // height of the output tree is at most 1 greater than that of the input tree
      !res.isEmpty &&
      insertAppendAxiomInst(xs, i, y) && // instantiation of an axiom
      res.toList == insertAtIndex(xs.toList, i, y))

  /**
   * Using a different version of insert than of the library
   * because the library implementation in unnecessarily complicated.
   * TODO: update the code to use the library instead ?
   */
  def insertAtIndex[T](l: List[T], i: BigInt, y: T): List[T] = {
    require(0 <= i && i <= l.size)
    decreases(l)
    l match {
      case Nil() =>
        Cons[T](y, Nil())
      case Cons(x, tail) =>
        if (i == 0) Cons[T](y, l)
        else Cons[T](x, insertAtIndex(tail, i - 1, y))
    }
  }

  // A lemma about `append` and `insertAtIndex`
  def appendInsertIndex[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    decreases(l1)
    (l1 match {
      case Nil()       => true
      case Cons(x, xs) => if (i == 0) true else appendInsertIndex[T](xs, l2, i - 1, y)
    }) &&
      // lemma
      (insertAtIndex((l1 ++ l2), i, y) == (
        if (i < l1.size) insertAtIndex(l1, i, y) ++ l2
        else l1 ++ insertAtIndex(l2, (i - l1.size), y)))
  }.holds

  def insertAppendAxiomInst[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i <= xs.size)
    xs match {
      case CC(l, r) => appendInsertIndex(l.toList, r.toList, i, y)
      case _        => true
    }
  }.holds

  def split[T](xs: Conc[T], n: BigInt): (Conc[T], Conc[T]) = {
    require(xs.valid)
    decreases(xs)
    xs match {
      case Empty() => (Empty[T](), Empty[T]())
      case s @ Single(x) =>
        if (n <= 0) (Empty[T](), s) //a minor fix
        else (s, Empty[T]())
      case CC(l, r) =>
        if (n < l.size) {
          val (ll, lr) = split(l, n)
          (ll, concatNormalized(lr, r))
        } else if (n > l.size) {
          val (rl, rr) = split(r, n - l.size)
          (concatNormalized(l, rl), rr)
        } else {
          (l, r)
        }
    }
  } ensuring (res => res._1.valid && res._2.valid && // tree invariants are preserved
    xs.level >= res._1.level && xs.level >= res._2.level && // height bounds of the resulting tree
    instSplitAxiom(xs, n) && // instantiation of an axiom
    splitCorrectness(res, xs, n))

  def splitCorrectness[T](r: (Conc[T], Conc[T]), xs: Conc[T], n: BigInt): Boolean = {
    r._1.toList == xs.toList.take(n) && r._2.toList == xs.toList.drop(n)
  }

  def instSplitAxiom[T](xs: Conc[T], n: BigInt): Boolean = {
    xs match {
      case CC(l, r) =>
        appendTakeDrop(l.toList, r.toList, n)
      case _ => true
    }
  }.holds
}
