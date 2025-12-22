import stainless.collection._

object BasicIArrayUse:
  def head[A](arr: IArray[A]): A = {
    require(arr.list.size > 0)
    arr(0)
  }
end BasicIArrayUse