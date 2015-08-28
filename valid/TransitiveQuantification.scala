import leon.lang._

object Transitive {
  
  def multiAssoc(f: (Int, Int, Int) => Int): Boolean = {
    require(forall { (a: Int, b: Int, c: Int, d: Int, e: Int) =>
      f(f(a,b,c),d,e) == f(a,f(b,c,d),e) && f(a,f(b,c,d),e) == f(a,b,f(c,d,e))
    })
    f(f(1,2,3),4,5) == f(1,2,f(3,4,5))
  }.holds

}
