import stainless.collection._

object i731a {
  def f(l: List[(BigInt, BigInt, BigInt)]): Unit = {
    require(l.forall { case (_, _, c) => true })

    if (!l.isEmpty)
      f(l.tail)

 }.ensuring { _ =>
    l.map { case (token, _, identity) => token -> identity }.forall(_ => true)
  }
}
