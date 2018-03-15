import stainless.collection._

object PatternTest {

def pt(i: List[BigInt]): Boolean = i match {
  case Nil() => false
  case a @ Cons(_, _) => a.isEmpty
}
}
