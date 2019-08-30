import stainless.lang._
import stainless.collection._

object FunctionCaching {

  case class FunCache(var cached: Map[BigInt, BigInt])

  def fun(x: BigInt)(implicit funCache: FunCache): BigInt = {
    funCache.cached.get(x) match {
      case None() => 
        val res = 2*x + 42
        funCache.cached = funCache.cached.updated(x, res)
        res
      case Some(cached) =>
        cached + 1
    }
  }

  def funWronglyCached(x: BigInt, trash: List[BigInt]): Boolean = {
    implicit val cache = FunCache(Map())
    val res1 = fun(x)
    multipleCalls(trash)
    val res2 = fun(x)
    res1 == res2
  }.holds


  def multipleCalls(args: List[BigInt])(implicit funCache: FunCache): Unit = args match {
    case Nil() => ()
    case x::xs => fun(x); multipleCalls(xs)
  }

}
