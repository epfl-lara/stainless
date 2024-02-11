package stainless
package covcollection

import lang.Map
import annotation._

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
  }} ensuring(isSorted(_))

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

  @library
  implicit class ListBigIntOps(l: List[BigInt]) {
    def sum: BigInt = ListOps.sum(l)

    def sorted: List[BigInt] = ListOps.sorted(l)

    def isSorted: Boolean = ListOps.isSorted(l)
  }

  @library
  implicit class FlattenableListOps[A](l: List[List[A]]) {
    def flatten: List[A] = ListOps.flatten(l)
  }

  @library
  implicit class ToMapOps[K, V](l: List[(K, V)]) {
    def toMap: Map[K, V] = ListOps.toMap(l)
  }
}