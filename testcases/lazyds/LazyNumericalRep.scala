package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._
import leon.collection._

/**
 * This benchmark requires an unrollfactor of 5
 */

object DigitObject {
  sealed abstract class Digit
  case class Zero() extends Digit {
    @ignore
    override def toString = "0"
  }
  case class One() extends Digit {
    @ignore
    override def toString = "1"
  }
}

import DigitObject._
object LazyNumericalRep {

  @finite
  sealed abstract class NumList {
    @inline
    val isTip = this == Tip()
    @inline
    val isSpine: Boolean = !isTip
  }

  case class Tip() extends NumList
  case class Spine(head: Digit, rear: NumStream) extends NumList

  sealed abstract class NumStream {

    @inline
    def isSusp = this match {
      case _: Susp => true
      case _       => false
    }

    lazy val fval = {
      require(isSusp)
      this match {
        case Susp(f) => f()
      }
    }

    def get: NumList = {
      this match {
        case Susp(f) => fval
        case Val(x)  => x
      }
    }

    def getV = this match {
      case Susp(f) => fval*
      case Val(x)  => x
    }

    def isCached = this match {
      case _: Val => true
      case _      => cached(fval)
    }
  }
  private case class Val(x: NumList) extends NumStream
  private case class Susp(fun: () => NumList) extends NumStream

  /**
   * Checks whether there is a zero before an unevaluated closure
   */
  def zeroPrecedesLazy(q: NumStream): Boolean = {
    if (q.isCached) {
      q.getV match {
        case Spine(Zero(), rear) => true // here we have seen a zero
        case Spine(_, rear)      => zeroPrecedesLazy(rear) //here we have not seen a zero
        case Tip()               => true
      }
    } else false
  }

  /**
   * Checks whether there is a zero before a given suffix
   */
  @invisibleBody
  def zeroPrecedesSuf(q: NumStream, suf: NumStream): Boolean = {
    if (q != suf) {
      q.getV match {
        case Spine(Zero(), rear) => true
        case Spine(_, rear)      => zeroPrecedesSuf(rear, suf)
        case Tip()               => false
      }
    } else false
  }

  /**
   * Everything until suf is evaluated. This
   * also asserts that suf should be a suffix of the list
   */
  @invisibleBody
  def concreteUntil(l: NumStream, suf: NumStream): Boolean = {
    if (l != suf) {
      l.isCached && (l.getV match {
        case Spine(_, tail) => concreteUntil(tail, suf)
        case _              => false
      })
    } else true
  }

  @invisibleBody
  def isConcrete(l: NumStream): Boolean = {
    l.isCached && (l.getV match {
      case Spine(_, tail) => isConcrete(tail)
      case _              => true
    })
  }

  @invisibleBody
  def schedulesProperty(q: NumStream, schs: List[NumStream]): Boolean = {
    schs match {
      case Cons(head, tail) =>
        head match {
          case Susp(fun) =>
            concreteUntil(q, head) &&
              schedulesProperty(pushUntilCarry(head), tail)
          case _ => false
        }
      case Nil() =>
        isConcrete(q)
    }
  }

  @invisibleBody
  def strongSchedsProp(q: NumStream, schs: List[NumStream]) = {
    q.isCached &&
      (schs match {
        case Cons(head, tail) =>
          zeroPrecedesSuf(q, head) // zeroPrecedesSuf holds initially
        case Nil() => true
      }) &&
      schedulesProperty(q, schs)
  }

  /**
   * (a) If we push a carry and get back 0 then there is a new carry
   * (b) If we push a carry and get back 1 then there the carry has been fully pushed
   * Note that if 'q' has a suspension then it would have a carry.
   */
  @invisibleBody
  def pushUntilCarry(q: NumStream): NumStream = {
    q.getV match {
      case Spine(Zero(), rear) => // if we push a carry and get back 0 then there is a new carry
        pushUntilCarry(rear)
      case Spine(_, rear) => // if we push a carry and get back 1 then there the carry has been fully pushed
        rear
      case Tip() => q
    }
  }

  case class Number(digs: NumStream, schedule: List[NumStream]) {
    def valid = strongSchedsProp(digs, schedule)
  }

  def emptyNum = Number(Val(Tip()), Nil())

  @invisibleBody
  def inc(xs: NumStream): NumList = {
    require(zeroPrecedesLazy(xs))
    xs.get match {
      case Tip() =>
        Spine(One(), xs)
      case s @ Spine(Zero(), rear) =>
        Spine(One(), rear)
      case s @ Spine(_, _) =>
        incLazy(xs)
    }
  } ensuring (_ => steps <= ?)

  @invisibleBody
  @invstate
  def incLazy(xs: NumStream): NumList = {
    require(zeroPrecedesLazy(xs) &&
      xs.isCached &&
      (xs.getV match {
        case Spine(h, rear) => h != Zero() && rear.isCached // xs is a spine and it doesn't start with a zero
        case _              => false
      }))
    xs.get match {
      case Spine(head, rear) => // here, rear is guaranteed to be evaluated by 'zeroPrecedeLazy' invariant
        val carry = One()
        rear.get match {
          case Tip() =>
            Spine(Zero(), Val(Spine(carry, rear)))

          case Spine(Zero(), srearfun) =>
            Spine(Zero(), Val(Spine(carry, srearfun)))

          case s =>
            Spine(Zero(), Susp(() => incLazy(rear)))
        }
    }
  } ensuring { res =>
    (res match {
      case Spine(Zero(), r) =>
        (r match {
          case _: Val    => true
          case Susp(fun) => fun().isSpine // this is necessary to assert properties on the state in the recursive invocation
        }) &&
          (!isConcrete(xs) || isConcrete(pushUntilCarry(r)))
      case _ => false
    }) &&
      steps <= ?
  }

  @invisibleBody
  def incNum(w: Number): (NumStream, List[NumStream]) = {
    require(w.valid &&
      // instantiate the lemma that implies zeroPrecedesLazy
      (w.schedule match {
        case Cons(h, _) =>
          zeroPredSufConcreteUntilLemma(w.digs, h)
        case _ =>
          concreteZeroPredLemma(w.digs)
      }))
    val nq = inc(w.digs)
    val nsched = nq match {
      case Spine(Zero(), rear: Susp) =>
        Cons(rear, w.schedule) // this is the only case where we create a new lazy closure
      case _ =>
        w.schedule
    }
    (Val(nq), nsched)
  } ensuring { res =>
    // lemma instantiations
    (w.schedule match {
      case Cons(head, tail) =>
        w.digs.getV match {
          case Spine(h, _) =>
            if (h != Zero())
              incLazyLemma(w.digs, head)
            else true
          case _ => true
        }
      case _ => true
    }) &&
      schedulesProperty(res._1, res._2) &&
      steps <= ?
  }

  @invisibleBody
  def Pay[T](q: NumStream, scheds: List[NumStream]): List[NumStream] = {
    require(schedulesProperty(q, scheds) && q.isCached)
    scheds match {
      case c @ Cons(head, rest) =>
        head.get match {
          case Spine(Zero(), rear: Susp) => Cons(rear, rest)
          case _                         => rest
        }
      case Nil() => scheds
    }
  } ensuring { res =>
    payPostconditionInst(q, res, scheds, inSt[NumList], outSt[NumList]) && // properties
      schedulesProperty(q, res) &&
      steps <= ?
  }

  /**
   * Pushing an element to the left of the queue preserves the data-structure invariants
   */
  @invisibleBody
  def incAndPay(w: Number) = {
    require(w.valid)
    val (q, scheds) = incNum(w)
    val nscheds = Pay(q, scheds)
    Number(q, nscheds)

  } ensuring { res => res.valid && steps <= ? }

  def firstDigit(w: Number): Digit = {
    require(!w.digs.getV.isTip)
    w.digs.get match {
      case Spine(d, _) => d
    }
  }

  /**
   * Lemma instantiations (separated into a function for readability)
   */
  @inline
  def payPostconditionInst(q: NumStream, res: List[NumStream], scheds: List[NumStream], in: Set[Fun[NumList]], out: Set[Fun[NumList]]) = {
    // instantiations for proving the scheds property
    (scheds match {
      case Cons(head, rest) =>
        concUntilExtenLemma(q, head, in, out) &&
          (head.getV match {
            case Spine(Zero(), rear) =>
              res match {
                case Cons(rhead, rtail) =>
                  schedMonotone(in, out, rtail, pushUntilCarry(rhead)) &&
                    concUntilMonotone(rear, rhead, in, out) &&
                    concUntilCompose(q, rear, rhead)
                case _ =>
                  concreteMonotone(in, out, rear) &&
                    concUntilConcreteExten(q, rear)
              }
          })
      case _ => true
    }) &&
      // instantiations for zeroPrecedesSuf property
      (scheds match {
        case Cons(head, rest) =>
          (concreteUntilIsSuffix(q, head) in in) &&
            (res match {
              case Cons(rhead, rtail) =>
                concreteUntilIsSuffix(pushUntilCarry(head), rhead) &&
                  suffixZeroLemma(q, head, rhead) &&
                  zeroPrecedesSuf(q, rhead)
              case _ =>
                true
            })
        case _ =>
          true
      })
  }

  /**
   * Lemma:
   * forall suf. suf.getV.head != Zero() ^ zeroPredsSuf(xs, suf) ^ concUntil(xs.tail.tail, suf) => concUntil(push(rear), suf)
   */
  @invisibleBody
  @invstate
  def incLazyLemma(xs: NumStream, suf: NumStream): Boolean = {
    require(zeroPrecedesSuf(xs, suf) &&
      (xs.getV match {
        case Spine(h, _) => h != Zero()
        case _           => false
      }) && suf.isSusp && concreteUntil(xs, suf))
    // induction scheme
    (xs.getV match {
      case Spine(head, rear) =>
        rear.getV match {
          case s @ Spine(h, _) =>
            if (h != Zero())
              incLazyLemma(rear, suf)
            else true
          case _ => true
        }
    }) &&
      zeroPredSufConcreteUntilLemma(xs, suf) && // instantiate the lemma that implies zeroPrecedesLazy
      // property
      (incLazy(xs) match {
        case Spine(Zero(), rear) =>
          concreteUntil(pushUntilCarry(rear), suf)
      })
  }.holds

  // monotonicity lemmas
  def schedMonotone[T](st1: Set[Fun[NumList]], st2: Set[Fun[NumList]], scheds: List[NumStream], l: NumStream): Boolean = {
    require(st1.subsetOf(st2) &&
      (schedulesProperty(l, scheds) in st1)) // here the input state is fixed as 'st1'
    //induction scheme
    (scheds match {
      case Cons(head, tail) =>
        head.getV match {
          case Spine(_, rear) =>
            concUntilMonotone(l, head, st1, st2) &&
              schedMonotone(st1, st2, tail, pushUntilCarry(head))
          case _ => true
        }
      case Nil() =>
        concreteMonotone(st1, st2, l)
    }) && (schedulesProperty(l, scheds) in st2) //property
  } holds

  @traceInduct
  def concreteMonotone[T](st1: Set[Fun[NumList]], st2: Set[Fun[NumList]], l: NumStream): Boolean = {
    ((isConcrete(l) in st1) && st1.subsetOf(st2)) ==> (isConcrete(l) in st2)
  } holds

  @traceInduct
  def concUntilMonotone[T](q: NumStream, suf: NumStream, st1: Set[Fun[NumList]], st2: Set[Fun[NumList]]): Boolean = {
    ((concreteUntil(q, suf) in st1) && st1.subsetOf(st2)) ==> (concreteUntil(q, suf) in st2)
  } holds

  // suffix predicates and  their properties (this should be generalizable)

  def suffix[T](q: NumStream, suf: NumStream): Boolean = {
    if (q == suf) true
    else {
      q.getV match {
        case Spine(_, rear) =>
          suffix(rear, suf)
        case Tip() => false
      }
    }
  }

  def properSuffix[T](l: NumStream, suf: NumStream): Boolean = {
    l.getV match {
      case Spine(_, rear) =>
        suffix(rear, suf)
      case _ => false
    }
  } ensuring (res => !res || (suffixDisequality(l, suf) && suf != l))

  /**
   * suf(q, suf) ==> suf(q.rear, suf.rear)
   */
  @traceInduct
  def suffixTrans[T](q: NumStream, suf: NumStream): Boolean = {
    suffix(q, suf) ==> ((q.getV, suf.getV) match {
      case (Spine(_, rear), Spine(_, sufRear)) =>
        // 'sufRear' should be a suffix of 'rear1'
        suffix(rear, sufRear)
      case _ => true
    })
  }.holds

  /**
   * properSuf(l, suf) ==> l != suf
   */
  def suffixDisequality[T](l: NumStream, suf: NumStream): Boolean = {
    require(properSuffix(l, suf))
    suffixTrans(l, suf) && // lemma instantiation
      ((l.getV, suf.getV) match { // induction scheme
        case (Spine(_, rear), Spine(_, sufRear)) =>
          // 'sufRear' should be a suffix of 'rear1'
          suffixDisequality(rear, sufRear)
        case _ => true
      }) && l != suf // property
  }.holds

  @traceInduct
  def suffixCompose[T](q: NumStream, suf1: NumStream, suf2: NumStream): Boolean = {
    (suffix(q, suf1) && properSuffix(suf1, suf2)) ==> properSuffix(q, suf2)
  } holds

  // properties of 'concUntil'

  @traceInduct
  def concreteUntilIsSuffix[T](l: NumStream, suf: NumStream): Boolean = {
    concreteUntil(l, suf) ==> suffix(l, suf)
  }.holds

  // properties that extend `concUntil` to larger portions of the queue

  @traceInduct
  def concUntilExtenLemma[T](q: NumStream, suf: NumStream, st1: Set[Fun[NumList]], st2: Set[Fun[NumList]]): Boolean = {
    (suf.isSusp && (concreteUntil(q, suf) in st1) && (st2 == st1 ++ Set(Fun(suf.fval)))) ==>
      (suf.getV match {
        case Spine(_, rear) =>
          concreteUntil(q, rear) in st2
        case _ => true
      })
  } holds

  @traceInduct
  def concUntilConcreteExten[T](q: NumStream, suf: NumStream): Boolean = {
    (concreteUntil(q, suf) && isConcrete(suf)) ==> isConcrete(q)
  } holds

  @traceInduct
  def concUntilCompose[T](q: NumStream, suf1: NumStream, suf2: NumStream): Boolean = {
    (concreteUntil(q, suf1) && concreteUntil(suf1, suf2)) ==> concreteUntil(q, suf2)
  } holds

  // properties that relate `concUntil`, `concrete`,  `zeroPrecedesSuf` with `zeroPrecedesLazy`
  //   - these are used in preconditions to derive the `zeroPrecedesLazy` property

  @traceInduct
  def zeroPredSufConcreteUntilLemma[T](q: NumStream, suf: NumStream): Boolean = {
    (zeroPrecedesSuf(q, suf) && concreteUntil(q, suf)) ==> zeroPrecedesLazy(q)
  } holds

  @traceInduct
  def concreteZeroPredLemma[T](q: NumStream): Boolean = {
    isConcrete(q) ==> zeroPrecedesLazy(q)
  } holds

  // properties relating `suffix` an `zeroPrecedesSuf`

  def suffixZeroLemma[T](q: NumStream, suf: NumStream, suf2: NumStream): Boolean = {
    require(suf.getV match {
      case Spine(Zero(), _) =>
        suffix(q, suf) && properSuffix(suf, suf2)
      case _ => false
    })
    suffixCompose(q, suf, suf2) && (
      // induction scheme
      if (q != suf) {
        q.getV match {
          case Spine(_, tail) =>
            suffixZeroLemma(tail, suf, suf2)
          case _ =>
            true
        }
      } else true) &&
      zeroPrecedesSuf(q, suf2) // property
  }.holds

  @ignore
  def main(args: Array[String]) {
    //import eagerEval.BigNums
    import scala.util.Random
    import scala.math.BigInt
    import stats._
    import collection._

    println("Running Numerical Representation test...")
    val ops = 1000000
    // initialize to a queue with one element (required to satisfy preconditions of dequeue and front)
    //var bignum: BigNums.BigNum = BigNums.Nil()
    var lazynum = emptyNum
    var totalTime1 = 0L
    var totalTime2 = 0L
    println(s"Testing amortized emphemeral behavior on $ops operations...")
    for (i <- 0 until ops) {
      //println("Inc..")
      //bignum = timed { BigNums.increment(bignum) } { totalTime1 += _ }
      lazynum = timed { incAndPay(lazynum) } { totalTime2 += _ }
      //val d1 = BigNums.firstDigit(bignum)
      val d2 = firstDigit(lazynum)
      //assert(d1.toString == d2.toString, s"Eager head: $d1 Lazy head: $d2")
    }
    println(s"Ephemeral Amortized Time - Eager: ${totalTime1 / 1000.0}s Lazy: ${totalTime2 / 1000.0}s") // this should be linear in length for both cases
    // now, test worst-case behavior (in persitent mode if necessary)
    val length = (1 << 22) - 1 // a number of the form: 2^{n-1}
    //bignum = BigNums.Nil()
    lazynum = emptyNum
    for (i <- 0 until length) {
      //bignum = BigNums.increment(bignum)
      lazynum = incAndPay(lazynum)
    }
    //println(s"Number of leading ones of bignum: ${BigNums.leadingOnes(bignum)}")
    //dequeue 1 element from both queues
    //timed { BigNums.increment(bignum) } { t => println(s"Time for one eager increment in the worst case: ${t / 1000.0}s") }
    timed { incAndPay(lazynum) } { t => println(s"Time for one lazy increment in the worst case: ${t / 1000.0}s") }
  }
}
