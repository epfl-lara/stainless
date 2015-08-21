import leon.lang._ 
object Unap2 {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] = 
    if (i._1 == 0) None() else Some((i._3, i._2))
}
 
object Unapply {
  def bar: Boolean = { (42, false, ()) match {
    case Unap2(_, b) if b => b
  }} ensuring { res => res }
}
