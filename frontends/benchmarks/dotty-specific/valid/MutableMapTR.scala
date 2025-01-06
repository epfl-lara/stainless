import scala.annotation.tailrec
import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

object MTailList:
  sealed abstract class MutableList[T]  
  case class MNil[T]() extends MutableList[T]
  case class MCons[T](val hd: T, var tail: MutableList[T]) extends MutableList[T]

  extension[T] (ml: MutableList[T])
    @pure
    def toList: List[T] =
      ml match
        case MNil() => Nil()
        case MCons(h, t) => Cons(h, t.toList)

  def mapTR[T,U](l: MutableList[T], f: T => U): MutableList[U] = {
    l match
      case MNil() => MNil[U]()
      case MCons(hd, tl) =>
        val acc: MCons[U] = MCons[U](f(hd), MNil())
        mapTRWorker[T,U](tl, f, acc)
        acc
 }.ensuring(_.toList == l.toList.map(f))

  @tailrec
  def mapTRWorker[T,U](
      l: MutableList[T],
      f: T => U,
      acc: MCons[U]
  ): Unit = {
    require(acc.tail == MNil[U]())
    l match
      case MNil() => ()
      case MCons(h, t) => 
        acc.tail = MCons[U](f(h), MNil())      
        mapTRWorker(t, f, acc.tail.asInstanceOf[MCons[U]])
        assert(acc.tail.asInstanceOf[MCons[U]].toList == f(h) :: t.toList.map(f))
 }.ensuring(_ => acc.toList == old(acc).hd :: l.toList.map(f))
