import leon.lang._

object Unap1 {
  def unapply[A, B](i: (Int, B, A)): Option[(A, B)] = 
    if (i._1 == 0) None() else Some((i._3, i._2))
}
  
object Unapply1 {
  
  def bar: Boolean = { (42, false, ()) match {
    case Unap1(_, b) if b => b
    case Unap1((), b) => b
  }} ensuring { res => res }
  
}
