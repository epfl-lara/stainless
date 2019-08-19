// By Ravi Kandhadai Madhavan @ LARA, EPFL. (c) EPFL

package stainless.collection

import stainless.collection._
import stainless.lang._
import stainless.proof._
import stainless.lang.StaticChecks._
import ListSpecs._
import stainless.annotation._
import stainless.algebra._

@library
object ConcRope {
  def max(x: BigInt, y: BigInt): BigInt = if (x >= y) x else y
  def abs(x: BigInt): BigInt = if (x < 0) -x else x

  @library
  object Conc {

    def flatten[T](xs: Conc[Conc[T]]): Conc[T] = {
      require(xs.forall(c => c.valid))
      xs match {
        case Empty() => Empty[T]()
        case Single(x) => normalize(x)
        case CC(left, right) => flatten(left) ++ flatten(right)
        case Append(left, right) => flatten(left) ++ flatten(right)
      }
    } ensuring (res => res.valid && res.isNormalized)

    def empty[T]: Conc[T] = Empty[T]()

    def fromList[T](xs: List[T]): Conc[T] = { xs match {
      case Nil() => Empty[T]()
      case y :: ys => y :: fromList(ys)
    }} ensuring { res => res.toList == xs &&
      res.size == xs.size &&
      res.content == xs.content &&
      res.valid &&
      res.isNormalized
    }

    def fromListReversed[T](xs: List[T]): Conc[T] = {
      xs match {
        case Nil() => Empty[T]()
        case Cons(y, ys) => append(fromListReversed(ys), y)
      }
    } ensuring (res => res.valid &&
      res.content == xs.content &&
      res.size == xs.size &&
      (res.toList == xs.reverse) because lemma_fromListReversed(xs))
  }

  @library
  sealed abstract class Conc[T] {
    import Conc._

    def isEmpty: Boolean = {
      this == Empty[T]()
    }

    def isLeaf: Boolean = {
      this match {
        case Empty() => true
        case Single(_) => true
        case _ => false
      }
    }

    def isNormalized: Boolean = this match {
      case Append(_, _) => false
      case _ => true
    }

    def valid: Boolean = {
      concInv && balanced && appendInv
    }

    /**
     * (a) left and right trees of conc node should be non-empty
     * (b) they cannot be append nodes
     */
    def concInv: Boolean = this match {
      case CC(l, r) =>
        !l.isEmpty && !r.isEmpty &&
          l.isNormalized && r.isNormalized &&
          l.concInv && r.concInv
      case _ => true
    }

    def balanced: Boolean = {
      this match {
        case CC(l, r) =>
          l.level - r.level >= -1 && l.level - r.level <= 1 &&
            l.balanced && r.balanced
        case _ => true
      }
    }

    /**
     * (a) Right subtree of an append node is not an append node
     * (b) If the tree is of the form a@Append(b@Append(_,_),_) then
     * 		a.right.level < b.right.level
     * (c) left and right are not empty
     */
    def appendInv: Boolean = this match {
      case Append(l, r) =>
        !l.isEmpty && !r.isEmpty &&
          l.valid && r.valid &&
          r.isNormalized &&
          (l match {
            case Append(_, lr) =>
              lr.level > r.level
            case _ =>
              l.level > r.level
          })
      case _ => true
    }

    val level: BigInt = {
      (this match {
        case Empty() => 0
        case Single(x) => 0
        case CC(l, r) =>
          1 + max(l.level, r.level)
        case Append(l, r) =>
          1 + max(l.level, r.level)
      }): BigInt
    } ensuring (_ >= 0)

    val size: BigInt = {
      (this match {
        case Empty() => 0
        case Single(x) => 1
        case CC(l, r) =>
          l.size + r.size
        case Append(l, r) =>
          l.size + r.size
      }): BigInt
    } ensuring (_ >= 0)

    def toList: List[T] = {
      this match {
        case Empty() => Nil[T]()
        case Single(x) => Cons(x, Nil[T]())
        case CC(l, r) =>
          l.toList ++ r.toList // note: left elements precede the right elements in the list
        case Append(l, r) =>
          l.toList ++ r.toList
      }
    } ensuring (res => res.size == this.size && res.content == content)

    def toSet: Set[T] = content

    def content: Set[T] = this match {
      case Empty() => Set[T]()
      case Single(x) => Set(x)
      case CC(left, right) => left.content ++ right.content
      case Append(left, right) => left.content ++ right.content
    }

    def apply(i: BigInt): T = {
      require(this.valid && !this.isEmpty && i >= 0 && i < this.size)
      lookup(this, i)
    } ensuring (res =>  instAppendIndexAxiom(this, i) &&  // an auxiliary axiom instantiation that required for the proof
      res == this.toList(i))

    def :+(x: T) = {
      require(valid)
      append(this, x)
    } ensuring (res => res.valid && //conctree invariants
      res.toList == this.toList ++ Cons(x, Nil[T]()) && //correctness
      res.level <= this.level + 1
    )

    def ::(x: T) = {
      require(valid && isNormalized)
      insert(this, 0, x)
    } ensuring (res => insertAppendAxiomInst(this, 0, x) && // instantiation of an axiom
      res.valid && res.isNormalized && // tree invariants
      res.level - this.level <= 1 && res.level >= this.level && // height of the output tree is at most 1 greater than that of the input tree
      res.toList == x :: this.toList // correctness
      )

    def head: T = {
      require(this.valid && !this.isEmpty && this.size > 0)
      this(0)
    } ensuring ( res => res == this(0) &&
      res == this.toList(0))

    def headOption: Option[T] = {
      require(this.valid)
      if(this.size == 0)
        None[T]()
      else
        Some(this(0))
    } ensuring ( res => if(this.size == 0)
                          res == None[T]()
                        else
                          res == Some[T](this(0)) && res == Some[T](this.toList(0)))

    def ++(that: Conc[T]): Conc[T] = {
      require(this.valid && that.valid)
      concat(this, that)
    } ensuring (res => res.valid && // tree invariants
      res.level <= max(normalize(this).level, normalize(that).level) + 1 && // height invariants
      res.level >= max(normalize(this).level, normalize(that).level) &&
      (res.toList == this.toList ++ that.toList) && // correctness
      res.isNormalized //auxiliary properties
      )

    def map[R](f: T => R): Conc[R] = { this match {
      case Empty() => Empty[R]()
      case Single(x) => Single(f(x))
      case CC(left, right) => CC(left.map(f), right.map(f))
      case Append(left, right) => Append(left.map(f), right.map(f))
    }} ensuring { _.size == this.size }

    def foldMap[R](f: T => R)(implicit M: Monoid[R]): R = { this match {
      case Empty() => M.identity
      case Single(x) => f(x)
      case CC(left, right) => M.combine(left.foldMap(f), right.foldMap(f))
      case Append(left, right) => M.combine(left.foldMap(f), right.foldMap(f))
    }}

    def foldLeft[R](z: R)(f: (R, T) => R): R = { this match {
      case Empty() => z
      case Single(x) => f(z, x)
      case CC(left, right) => {
        val leftFold = left.foldLeft(z)(f)
        right.foldLeft(leftFold)(f)
      }
      case Append(left, right) => {
        val leftFold = left.foldLeft(z)(f)
        right.foldLeft(leftFold)(f)
      }
    }}

    def foldRight[R](z: R)(f: (T, R) => R): R = { this match {
      case Empty() => z
      case Single(x) => f(x, z)
      case CC(left, right) => {
        val rightFold = right.foldRight(z)(f)
        left.foldRight(rightFold)(f)
      }
      case Append(left, right) => {
        val rightFold = right.foldRight(z)(f)
        left.foldRight(rightFold)(f)
      }
    }}

    // Could there be a better way?
    // Rather than requiring that the function gives us only valid ConcRope, we could maybe 'sanitize' the produced ConcRopes
    // Because maybe this is too restrictive
    def flatMap[R](f: T => Conc[R]): Conc[R] = {
      require(map(f).forall(c => c.valid))

      this match {
        case Empty() => Empty[R]()
        case Single(x) => normalize(f(x))
        case CC(left, right) => left.flatMap(f) ++ right.flatMap(f)
        case Append(left, right) => left.flatMap(f) ++ right.flatMap(f)
      }
    } ensuring (res => res.valid && res.isNormalized)

    def forall(p: T => Boolean): Boolean = { this match {
      case Empty() => true
      case Single(x) => p(x)
      case CC(left, right) => left.forall(p) && right.forall(p)
      case Append(left, right) => left.forall(p) && right.forall(p)
    }}

    def exists(p: T => Boolean): Boolean = !forall(!p(_))

    def contains(v: T): Boolean = { this match {
      case Empty() => false
      case Single(x) => v == x
      case CC(left, right) => left.contains(v) || right.contains(v)
      case Append(left, right) => left.contains(v) || right.contains(v)
    }} ensuring { res => res == (content contains v) && res == (toList contains v) }

    def find(p: T => Boolean): Option[T] = { this match {
      case Empty() => None[T]()
      case Single(x) if p(x) => Some(x)
      case Single(x) => None[T]()
      case CC(left, right) => {
        val l = left.find(p)
        if(l.isEmpty)
          right.find(p)
        else
          l
      }
      case Append(left, right) => {
        val l = left.find(p)
        if(l.isEmpty)
          right.find(p)
        else
          l
      }
    }} ensuring { res => res match {
      case Some(t) => (content contains t) && p(t)
      case None() => true
    }}
  }

  @library
  case class Empty[T]() extends Conc[T]

  @library
  case class Single[T](x: T) extends Conc[T]

  @library
  case class CC[T](left: Conc[T], right: Conc[T]) extends Conc[T]

  @library
  case class Append[T](left: Conc[T], right: Conc[T]) extends Conc[T]

  def lookup[T](xs: Conc[T], i: BigInt): T = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    xs match {
      case Single(x) => x
      case CC(l, r) =>
        if (i < l.size) lookup(l, i)
       else lookup(r, i - l.size)
      case Append(l, r) =>
        if (i < l.size) lookup(l, i)
        else lookup(r, i - l.size)
      case _ => error[T]("Impossible case because of requirements")
    }
  } ensuring (res =>  instAppendIndexAxiom(xs, i) &&  // an auxiliary axiom instantiation that required for the proof
    res == xs.toList(i)) // correctness


  def instAppendIndexAxiom[T](xs: Conc[T], i: BigInt): Boolean = {
    require(0 <= i && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case Append(l, r) =>
        appendIndex(l.toList, r.toList, i)
      case _ => true
    }
  }.holds

  def update[T](xs: Conc[T], i: BigInt, y: T): Conc[T] = {
    require(xs.valid && !xs.isEmpty && i >= 0 && i < xs.size)
    xs match {
      case Single(x) => Single(y)
      case CC(l, r) =>
        if (i < l.size) CC(update(l, i, y), r)
        else CC(l, update(r, i - l.size, y))
      case Append(l, r) =>
        if (i < l.size) {
          Append(update(l, i, y), r)
        } else
          Append(l, update(r, i - l.size, y))
      case _ => error[Conc[T]]("Impossible case because of requirements")
    }
  } ensuring (res => instAppendUpdateAxiom(xs, i, y) && // an auxiliary axiom instantiation
    res.level == xs.level && // heights of the input and output trees are equal
    res.valid && // tree invariants are preserved
    res.toList == xs.toList.updated(i, y) && // correctness
    numTrees(res) == numTrees(xs)) //auxiliary property that preserves the potential function

  def instAppendUpdateAxiom[T](xs: Conc[T], i: BigInt, y: T): Boolean = {
    require(i >= 0 && i < xs.size)
    xs match {
      case CC(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case Append(l, r) =>
        appendUpdate(l.toList, r.toList, i, y)
      case _ => true
    }
  }.holds

  /**
   * A generic concat that applies to general concTrees
   */
  def concat[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid)
    concatNormalized(normalize(xs), normalize(ys))
  }

  /**
   * This concat applies only to normalized trees.
   * This prevents concat from being recursive
   */
  def concatNormalized[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid &&
      xs.isNormalized && ys.isNormalized)
    (xs, ys) match {
      case (xs, Empty()) => xs
      case (Empty(), ys) => ys
      case _ =>
        concatNonEmpty(xs, ys)
    }
  } ensuring (res => res.valid && // tree invariants
    res.level <= max(xs.level, ys.level) + 1 && // height invariants
    res.level >= max(xs.level, ys.level) &&
    (res.toList == xs.toList ++ ys.toList) && // correctness
    res.isNormalized //auxiliary properties
    )

  def concatNonEmpty[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid &&
      xs.isNormalized && ys.isNormalized &&
      !xs.isEmpty && !ys.isEmpty)

    val diff = ys.level - xs.level
    if (diff >= -1 && diff <= 1)
      CC(xs, ys)
    else if (diff < -1) {
      // ys is smaller than xs
      xs match {
        case CC(l, r) =>
          if (l.level >= r.level)
            CC(l, concatNonEmpty(r, ys))
          else {
            r match {
              case CC(rl, rr) =>
                val nrr = concatNonEmpty(rr, ys)
                if (nrr.level == xs.level - 3) {
                  CC(l, CC(rl, nrr))
                } else {
                  CC(CC(l, rl), nrr)
                }
              case _ => error[Conc[T]]("Impossible case")
            }
          }
        case _ => error[Conc[T]]("Impossible case")
      }
    } else {
      ys match {
        case CC(l, r) =>
          if (r.level >= l.level) {
            CC(concatNonEmpty(xs, l), r)
          } else {
            l match {
              case CC(ll, lr) =>
                val nll = concatNonEmpty(xs, ll)
                if (nll.level == ys.level - 3) {
                  CC(CC(nll, lr), r)
                } else {
                  CC(nll, CC(lr, r))
                }
              case _ => error[Conc[T]]("Impossible case")
            }
          }
        case _ => error[Conc[T]]("Impossible case")
      }
    }
  } ensuring (res =>
    appendAssocInst(xs, ys) && // instantiation of an axiom
    res.level <= max(xs.level, ys.level) + 1 && // height invariants
    res.level >= max(xs.level, ys.level) &&
    res.balanced && res.appendInv && res.concInv && //this is should not be needed
    res.valid && // tree invariant is preserved
    res.toList == xs.toList ++ ys.toList && // correctness
    res.isNormalized // auxiliary properties
    )


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


  def insert[T](xs: Conc[T], i: BigInt, y: T): Conc[T] = {
    require(xs.valid && i >= 0 && i <= xs.size &&
      xs.isNormalized) //note the precondition
    xs match {
      case Empty() => Single(y)
      case Single(x) =>
        if (i == 0)
          CC(Single(y), xs)
        else
          CC(xs, Single(y))
      case CC(l, r) if i < l.size =>
        concatNonEmpty(insert(l, i, y), r)
      case CC(l, r) =>
       concatNonEmpty(l, insert(r, i - l.size, y))
    }
  } ensuring (res => insertAppendAxiomInst(xs, i, y) && // instantiation of an axiom
    res.valid && res.isNormalized && // tree invariants
    res.level - xs.level <= 1 && res.level >= xs.level && // height of the output tree is at most 1 greater than that of the input tree
    res.toList == insertAtIndex(xs.toList, i, y) // correctness
    )

  /**
   * Using a different version of insert than of the library
   * because the library implementation in unnecessarily complicated.
   */
  def insertAtIndex[T](l: List[T], i: BigInt, y: T): List[T] = {
    require(0 <= i && i <= l.size)
    l match {
      case Nil() =>
        Cons[T](y, Nil())
      case _ if i == 0 =>
        Cons[T](y, l)
      case Cons(x, tail) =>
        Cons[T](x, insertAtIndex(tail, i - 1, y))
    }
  }

  // A lemma about `append` and `insertAtIndex`
  def appendInsertIndex[T](l1: List[T], l2: List[T], i: BigInt, y: T): Boolean = {
    require(0 <= i && i <= l1.size + l2.size)
    (l1 match {
      case Nil() => true
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
      case _ => true
    }
  }.holds

  def split[T](xs: Conc[T], n: BigInt): (Conc[T], Conc[T]) = {
    require(xs.valid && xs.isNormalized)
    xs match {
      case Empty() =>
        (Empty[T](), Empty[T]())
      case s @ Single(x) =>
        if (n <= 0) {
          (Empty[T](), s)
        } else {
          (s, Empty[T]())
        }
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
      case _ => error[(Conc[T], Conc[T])]("Impossible case")
    }
  } ensuring (res  => instSplitAxiom(xs, n) && // instantiation of an axiom
    res._1.valid && res._2.valid && // tree invariants are preserved
    res._1.isNormalized && res._2.isNormalized &&
    xs.level >= res._1.level && xs.level >= res._2.level && // height bounds of the resulting tree
    res._1.toList == xs.toList.take(n) && res._2.toList == xs.toList.drop(n) // correctness
    )

  def instSplitAxiom[T](xs: Conc[T], n: BigInt): Boolean = {
    xs match {
      case CC(l, r) =>
        appendTakeDrop(l.toList, r.toList, n)
      case _ => true
    }
  }.holds

  def append[T](xs: Conc[T], x: T): Conc[T] = {
    require(xs.valid)
    val ys = Single[T](x)
    xs match {
      case xs @ Append(_, _) =>
        appendPriv(xs, ys)
      case CC(_, _) =>
        Append(xs, ys) //creating an append node
      case Empty() => ys
      case Single(_) => CC(xs, ys)
    }
  } ensuring (res => res.valid && //conctree invariants
    res.toList == xs.toList ++ Cons(x, Nil[T]()) && //correctness
    res.level <= xs.level + 1
  )

  /**
   * This is a private method and is not exposed to the
   * clients of conc trees
   */
  def appendPriv[T](xs: Append[T], ys: Conc[T]): Conc[T]  = {
    require(xs.valid && ys.valid &&
      !ys.isEmpty && ys.isNormalized &&
      xs.right.level >= ys.level)

    if (xs.right.level > ys.level)
      Append(xs, ys)
    else {
      val zs = CC(xs.right, ys)
      xs.left match {
        case l @ Append(_, _) => appendPriv(l, zs)
        case l if l.level <= zs.level => //note: here < is not possible
          CC(l, zs)
        case l =>
          Append(l, zs)
      }
    }
  } ensuring (res => appendAssocInst2(xs, ys) &&
    res.valid && //conc tree invariants
    res.toList == xs.toList ++ ys.toList && //correctness invariants
    res.level <= xs.level + 1 )

  def appendAssocInst2[T](xs: Conc[T], ys: Conc[T]): Boolean = {
    xs match {
      case CC(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList)
      case Append(l, r) =>
        appendAssoc(l.toList, r.toList, ys.toList)
      case _ => true
    }
  }.holds

  def numTrees[T](t: Conc[T]): BigInt = {
    t match {
      case Append(l, r) => numTrees(l) + 1
      case _ => BigInt(1)
    }
  } ensuring (res => res >= 0)

  def normalize[T](t: Conc[T]): Conc[T] = {
    require(t.valid)
    t match {
      case Append(l @ Append(_, _), r) =>
        wrap(l, r)
      case Append(l, r) =>
        concatNormalized(l, r)
      case _ => t
    }
  } ensuring (res => res.valid &&
    res.isNormalized &&
    res.toList == t.toList && //correctness
    res.size == t.size && res.level <= t.level //normalize preserves level and size
    )

  def wrap[T](xs: Append[T], ys: Conc[T]): Conc[T] = {
    require(xs.valid && ys.valid && ys.isNormalized &&
      xs.right.level >= ys.level)
    val nr  = concatNormalized(xs.right, ys)
    xs.left match {
      case l @ Append(_, _) => wrap(l, nr)
      case l =>
        concatNormalized(l, nr)
    }
  } ensuring (res =>
    appendAssocInst2(xs, ys) && //some lemma instantiations
    res.valid &&
    res.isNormalized &&
    res.toList == xs.toList ++ ys.toList && //correctness
    res.size == xs.size + ys.size && //other auxiliary properties
    res.level <= xs.level
    )

    def lemma_fromListReversed[A](xs: List[A]): Boolean = {
      import Conc._
      decreases(xs.size)
      (fromListReversed(xs).toList == xs.reverse) because { xs match {
        case Nil() =>
          assert(fromListReversed(Nil[A]()).toList == Nil[A]())
          assert(Nil[A]() == Nil[A]().reverse)
          check(fromListReversed(Nil[A]()).toList == Nil[A]().reverse)
        case Cons(y, ys) => {
          assert(fromListReversed(y :: ys).toList == append(fromListReversed(ys), y).toList)
          assert(append(fromListReversed(ys), y).toList == fromListReversed(ys).toList ++ Cons(y, Nil[A]()))
          assert(lemma_fromListReversed(ys))
          assert(fromListReversed(ys).toList ++ Cons(y, Nil[A]()) == ys.reverse ++ Cons(y, Nil[A]()))
          assert(ys.reverse ++ Cons(y, Nil[A]()) == ys.reverse ++ Cons(y, Nil[A]()).reverse)
          assert(ListSpecs.reverseAppend(Cons(y, Nil[A]()), ys))
          assert(ys.reverse ++ Cons(y, Nil[A]()).reverse == (Cons(y, Nil[A]()) ++ ys).reverse)
          assert((Cons(y, Nil[A]()) ++ ys).reverse == (y :: ys).reverse)
          check(fromListReversed(xs).toList == xs.reverse)
        }
      }}
    }.holds
}