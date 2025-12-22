import stainless.collection._

object BasicIArrayUse:
  def head[A](arr: IArray[A]): BigInt = {
    require(arr.list.size > 0)
    arr(0)
  }
end BasicIArrayUse