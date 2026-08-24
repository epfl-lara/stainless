package functionClosureMini

def f(i: BigInt): Unit = ()
def fun2(from: BigInt): Unit =
  val i: (BigInt with from <= i) = from.asInstanceOf[{i: BigInt with from <= i}]
  def inner(): Unit =
    f(i)
    inner()
