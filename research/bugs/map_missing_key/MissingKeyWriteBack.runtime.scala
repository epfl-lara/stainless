case class MutableMap[A, B](theMap: scala.collection.mutable.Map[A, B], default: () => B) {
  def apply(k: A): B = if (theMap.contains(k)) theMap(k) else default()
}

case class Box(var value: BigInt)

object MissingKeyRuntime {
  def main(args: Array[String]): Unit = {
    val m = MutableMap[BigInt, Box](scala.collection.mutable.Map[BigInt, Box](), () => Box(0))
    val x = m(0)
    x.value = 1

    println(s"x.value          = ${x.value}")
    println(s"m(0).value       = ${m(0).value}")
    println(s"key 0 in the map = ${m.theMap.contains(0)}")
    println(s"m(0).value == 1  = ${m(0).value == 1}")
  }
}
