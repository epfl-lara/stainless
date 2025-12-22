import stainless.collection._

object BasicIArrayUse:
  def iArrayLength[A](arr: IArray[A]): BigInt = {
    require(arr.list.size >= 0)
    arr.size
  }
end BasicIArrayUse