/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object ChooseWithWitness {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    def size(l: List) : BigInt = (l match {
        case Nil() => BigInt(0)
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    def content(l: List) : Set[Int] = l match {
      case Nil() => Set.empty[Int]
      case Cons(x, xs) => Set(x) ++ content(xs)
    }

    def createListOfSize(i: BigInt): List = {
      require(i >= 0)

      if (i == BigInt(0)) {
        Nil()
      } else {
        Cons(0, createListOfSize(i - 1))
      }
    } ensuring ( size(_) == i )

    def listOfSize(i: BigInt): List = {
      require(i >= 0)

      if (i == BigInt(0)) {
        Nil()
      } else {
        assert(size(createListOfSize(i)) == i) // provides choose quantification with a matcher
        choose[List] { (res: List) => size(res) == i }
      }
    } ensuring ( size(_) == i )

    def listOfSize2(i: BigInt): List = {
      require(i >= 0)

      if (i > 0) {
        Cons(0, listOfSize(i-1))
      } else {
        Nil()
      }
    } ensuring ( size(_) == i )
}
