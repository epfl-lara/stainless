import stainless.collection.*

case class Structure[S,T](
  valid: S => Boolean,
  single: T => S,
  insert: (S,T) => S)

object IntListStructure:
  type S = List[Int]
  type T = Int
  def valid = (s:S) => s.nonEmpty
  def single = (t:T) => Cons(t,Nil())
  def insert = (s:List[Int], i:Int) => i::s
  def get = Structure[S,T](valid, single, insert)
