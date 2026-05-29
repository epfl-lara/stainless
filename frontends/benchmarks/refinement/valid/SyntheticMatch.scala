type DiagInt = {p : (Int,Int) with p._1 == p._2}

def f(y:Int) = {
  val (a,b) = {
    (y,y) : DiagInt
  }
  assert(a == b)
  (a,b)
}