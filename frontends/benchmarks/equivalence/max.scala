import stainless.annotation._
import stainless.lang._
import stainless.collection._
import stainless.proof._ 

object Max {

  def maxR(lst: List[Int]): Int = {
    lst match {
      case Nil()           => -1
      case Cons(hd, Nil()) => hd
      case Cons(hd, tl)    => 
        if (hd > maxR(tl)) hd 
        else maxR(tl)
    }
  } 

  def maxC(l: List[Int]): Int = {
    l match {
      case Nil()                => -1
      case Cons(a, Nil())       => a
      case Cons(a, Cons(b, tl)) => 
        if (a > b) maxC(a :: tl) 
        else maxC(b :: tl)
    }
  }

  def maxT(lst: List[Int]): Int = {
    def bigger(a: Int, b: Int) = 
      if (a >= b) a else b
    lst match {
      case Nil()        => -1
      case Cons(hd, tl) => 
        tl.foldLeft(hd)(bigger)
    }
  }

}