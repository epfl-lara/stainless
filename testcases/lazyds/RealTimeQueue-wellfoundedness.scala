package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import collection._
import instrumentation._
import invariant._

object RealTimeQueueFinite {

  sealed abstract class Stream[T] {
    @inline
    def isEmpty: Boolean = this == SNil[T]()
    @inline
    def isCons: Boolean = !isEmpty

    def size: BigInt = { // ranking function this.rank
      this match {
        case SNil()      => BigInt(0)
        case c@SCons(_, _, _) => 1 + (c.tail*).size
      }
    } ensuring (_ >= 0)    
        
    @inline
    def rank: BigInt = size
//      this match {
//      case SNil() => BigInt(0)
//      case SCons(_, _, r) => r 
//    }
       
    def wf: Boolean = {
      rank >= 0  && 
      (this match {
        case SNil()      => true        
        case SCons(_, tfun, r) =>
          val t = (tfun()*)
          t.rank < r && t.wf              
      })
    } // wellfoundedness prop: (tailFun*).rank < this.rank && \forall x. rank >= 0 && tailFun*.satisfies prop

    lazy val tail: Stream[T] = {
      require(isCons)
      this match {
        case SCons(x, tailFun, _) => tailFun()
      }
    }
  }
  case class SCons[T](x: T, tailFun: () => Stream[T], rank: BigInt) extends Stream[T]
  case class SNil[T]() extends Stream[T]

  def isConcrete[T](l: Stream[T]): Boolean = {
    require(l.wf) // ranking function l.rank (it decreases across each iteration and is positive)
    l match {
      case c@SCons(_, _, _) =>
        c.tail.cached && isConcrete(c.tail*)
      case _ => true
    }
  }

  @invisibleBody
  @invstate // says that the function doesn't change state
  def rotate[T](f: Stream[T], r: List[T], a: Stream[T]): Stream[T] = {
    require(f.wf && a.wf && r.size == f.size + 1 && isConcrete(f)) 
    (f, r) match {
      case (SNil(), Cons(y, _)) => //in this case 'y' is the only element in 'r'
        SCons[T](y, lift(a), a.rank + 1) //  rank: a.rank + 1
      case (c@SCons(x, _, fr), Cons(y, r1)) =>
        val newa = SCons[T](y, lift(a), a.rank + 1) // rank : a.rank + 1
        val ftail = c.tail
        val rot = () => rotate(ftail, r1, newa)
        SCons[T](x, rot, fr + r.size + a.rank) // @ rank == f.rank + r.rank + a.rank && wf(newlist)
    }
  } ensuring (res => res.wf) // Orb results: time <= 31

  /**
   * Returns the first element of the stream whose tail is not evaluated.
   */
  @invisibleBody
  def firstUnevaluated[T](l: Stream[T]): Stream[T] = {
    require(l.wf)
    l match {
      case c @ SCons(_, _, _) =>
        if (c.tail.cached)
          firstUnevaluated(c.tail*)
        else l
      case _           => l
    }
  } 
//    ensuring (res => (!res.isEmpty || isConcrete(l)) && //if there are no lazy closures then the stream is concrete
//    (res match {
//      case c@SCons(_, _) =>
//        firstUnevaluated(l) == firstUnevaluated(c.tail) // after evaluating the firstUnevaluated closure in 'l' we can access the next unevaluated closure
//      case _ => true
//    }))
}
