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
        cached
    }
  } ensuring(res => old(funCache).cached.get(x) match {
    case None() => true
    case Some(v) => v == res
  })

  def funProperlyCached(x: BigInt, trash: List[BigInt]): Boolean = {
    implicit val cache = FunCache(Map())
    val res1 = fun(x)
    multipleCalls(trash, x)
    val res2 = fun(x)
    res1 == res2
  } holds

  def multipleCalls(args: List[BigInt], x: BigInt)(implicit funCache: FunCache): Unit = {
    require(funCache.cached.get(x).forall(_ == 2*x + 42))
    args match {
      case Nil() => ()
      case y::ys => 
        fun(y)
        multipleCalls(ys, x)
    }
  } ensuring(_ => funCache.cached.get(x).forall(_ == 2*x + 42))

}
