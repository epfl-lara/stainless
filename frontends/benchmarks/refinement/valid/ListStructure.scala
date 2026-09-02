package listStructure

import stainless.collection.*

case class Structure[S,T](
  valid: S => Boolean,
  single: T => {s:S with valid(s)})

object IntListStructure:
  type S = List[Int]
  type T = Int
  val valid = (s:S) => s.nonEmpty
  val single : T => {s:S with valid(s)} = 
    (t:T) => Cons[Int](t, Nil[Int]())
  def get = Structure[S,T](valid, single)