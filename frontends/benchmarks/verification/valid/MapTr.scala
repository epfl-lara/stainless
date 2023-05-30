import stainless.collection._
import stainless.lang._
import stainless.proof._

// An example assignment from FP'22

extension (l: List[Int])
  def mapTr(f: Int => Int, acc: List[Int]): List[Int] =
    l match
      case Nil[Int]()       => acc
      case Cons(x, xs) => xs.mapTr(f, acc ++ (f(x) :: Nil[Int]()))

// Given the following lemmas:

def MapNil(f: Int => Int): Boolean = {
  Nil[Int]().map(f) == Nil[Int]()
}.holds

def MapCons(x: Int, xs: List[Int], f: Int => Int): Boolean = {
  (x :: xs).map(f) == f(x) :: xs.map(f)
}.holds

def MapTrNil(f: Int => Int, xs: List[Int]): Boolean = {
  Nil[Int]().mapTr(f, xs) == xs
}.holds

def MapTrCons(x: Int, xs: List[Int], f: Int => Int, ys: List[Int]): Boolean = {
  (x :: xs).mapTr(f, ys) == xs.mapTr(f, ys ++ (f(x) :: Nil[Int]()))
}.holds

def NilAppend(xs: List[Int]): Boolean = {
  Nil[Int]() ++ xs == xs
}.holds

def ConsAppend(x: Int, xs: List[Int], ys: List[Int]): Boolean = {
  ((x :: xs) ++ ys) == x :: (xs ++ ys)
}.holds

// Let us ﬁrst prove the following lemma:
// l.mapTr(f, y :: ys) === y :: l.mapTr(f, ys)

def AccOut(l: List[Int], f: Int => Int, y: Int, ys: List[Int]): Boolean = {
  ( l.mapTr(f, y :: ys) == y :: l.mapTr(f, ys) ) because {
    l match {
      // Case l is empty
      case Nil[Int]() => {
        Nil[Int]().mapTr(f, y :: ys)              ==| MapTrNil(f, y :: ys)                                |
        y :: ys                                   ==| MapTrNil(f, ys)                                     |
        y :: Nil[Int]().mapTr(f, ys)
      }.qed
      // Case l is not empty
      case Cons(x, xs) => {
        (x :: xs).mapTr(f, y :: ys)                    ==| MapTrCons(x, xs, f, y :: ys)                   |
        xs.mapTr(f, (y :: ys) ++ (f(x) :: Nil[Int]())) ==| ConsAppend(y, ys, (f(x) :: Nil[Int]()))        |
        xs.mapTr(f, y :: (ys ++ (f(x) :: Nil[Int]()))) ==| AccOut(xs, f, y, ys ++ (f(x) :: Nil[Int]()))   |
        y :: xs.mapTr(f, ys ++ (f(x) :: Nil[Int]()))   ==| MapTrCons(x, xs, f, ys)                        |
        y :: (x :: xs).mapTr(f, ys)
      }.qed
    }
  }
}.holds

// Given all lemmas on the previous page, including AccOut, let us now prove our goal:
// l.map(f) === l.mapTr(f, Nil)

def MapEqMapTr(l: List[Int], f: Int => Int): Boolean = {
  ( l.map(f) == l.mapTr(f, Nil[Int]()) ) because {
    l match {
      // case l is empty
      case Nil[Int]() => {
        Nil[Int]().map(f)                                 ==|  MapNil(f)                          |
        Nil[Int]()                                        ==|  MapTrNil(f, Nil[Int]())            |
        Nil[Int]().mapTr(f, Nil[Int]())
      }.qed
      // case l is not empty
      case Cons(x, xs) => {
        (x :: xs).map(f)                                  ==|  MapCons(x, xs, f)                  |
        f(x) :: xs.map(f)                                 ==|  MapEqMapTr(xs, f)                  |
        f(x) :: xs.mapTr(f, Nil[Int]())                   ==|  AccOut(xs, f, f(x), Nil[Int]())    |
        xs.mapTr(f, f(x) :: Nil[Int]())                   ==|  NilAppend(f(x) :: Nil[Int]())      |
        xs.mapTr(f, Nil[Int]() ++ (f(x) :: Nil[Int]()))   ==|  MapTrCons(x, xs, f, Nil[Int]())    |
        (x :: xs).mapTr(f, Nil[Int]())
      }.qed
    }
  }
}.holds


