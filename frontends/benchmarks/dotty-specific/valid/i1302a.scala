import stainless.collection._

object i1302a {
  def f(l: List[(BigInt, BigInt)]): Unit = {
    val _ = l.map(_._1).map((x) => x)
    val _ = l.map(_._2).map((y) => y)
    val _ = l.map { case (x, y) => (x, y) }
    val _ = l.map((x, y) => (x, y))
    ()
  }
}