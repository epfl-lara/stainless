import stainless.annotation._
import stainless.lang._

object Issue1111b {

  sealed case class Tuple2[@mutable T0, @mutable T1](fst: MutCell[T0], snd: MutCell[T1])
  sealed case class Container[@mutable K, @mutable V](pair: MutCell[Option[Tuple2[K, V]]])

  sealed abstract class Option[@mutable T]
  case class Some[@mutable T](value: MutCell[T]) extends Option[T]
  case class None[@mutable T]() extends Option[T]

  sealed case class MutCell[@mutable T](var value: T)

  sealed case class Data(value: MutCell[String])

  case class DataasEquals() extends Equals[Data] {
    @pure
    def equals(self: Data, other: Data): Boolean = self.value.value == other.value.value
  }

  abstract class Equals[@mutable E] {
    @pure
    def equals(param0: E, param1: E): Boolean
  }

  @pure
  def neww[@mutable K, @mutable V]: Container[K, V] = {
    freshCopy(Container[K, V](MutCell[Option[Tuple2[K, V]]](None[Tuple2[K, V]]())))
  } ensuring {
    (ret: Container[K, V]) => is_empty[K, V](ret)
  }

  @pure
  def is_empty[@mutable K, @mutable V](self: Container[K, V]): Boolean = self.pair.value match {
    case None() => true
    case _ => false
  }

  def get_mut[@mutable K, @mutable V](self: MutCell[Container[K, V]], key: K, ev0: Equals[K]): Option[V] = {
    self.value.pair match {
      case MutCell(Some(MutCell(Tuple2(k, v)))) if ev0.equals(k.value, key) =>
        Some[V](v)
      case _ =>
        None[V]()
    }
  } ensuring {
    (ret: Option[V]) => is_empty[K, V](self.value) ==> (ret match {
      case None() =>
        true
      case _ =>
        false
    })
  }

  def insert[@mutable K, @mutable V](self: MutCell[Container[K, V]], k: K, v: V): Unit = {
    self.value.pair.value = freshCopy(Some[Tuple2[K, V]](MutCell[Tuple2[K, V]](Tuple2[K, V](MutCell[K](k), MutCell[V](v)))))
  } ensuring {
    (ret: Unit) => !is_empty[K, V](self.value)
  }

  @pure
  def main: Unit = {
    var cont: MutCell[Container[Data, Int]] = MutCell[Container[Data, Int]](freshCopy(neww[Data, Int]))
    val key: Data = freshCopy(Data(MutCell[String]("foo")))
    if (!is_empty[Data, Int](cont.value)) {
      error[Nothing]("assertion failed: cont.is_empty()")
    } else {
      ()
    }
    if (!(get_mut[Data, Int](cont, key, DataasEquals()) match {
      case None() =>
        true
      case _ =>
        false
    })) {
      error[Nothing]("assertion failed: matches!(cont . get_mut(& key), None)")
    } else {
      ()
    }
    insert[Data, Int](cont, freshCopy(key), 0)
    get_mut[Data, Int](cont, key, DataasEquals()) match {
      case Some(v) =>
        v.value = 1000
      case _ =>
        error[Nothing]("no value")
    }
    if (!(cont.value match {
      case Container(MutCell(Some(MutCell(Tuple2(MutCell(k), MutCell(1000)))))) if DataasEquals().equals(k, key) =>
        true
      case _ =>
        false
    })) {
      error[Nothing]("assertion failed: matches!(cont, Container { pair : Some((k, 1000)) } if k . equals(& key))")
    } else {
      ()
    }
  }

}
