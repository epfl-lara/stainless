import stainless.collection.List

object MethodCallsWithMultipleArgsLists:
  trait Interface:
    def pred[C](l: List[C])(x: Int)(y: Int): Boolean = true
    def f[C](l: List[C]): List[C]
  end Interface

  case object Impl extends Interface:
    override def f[C](l: List[C]): List[C] = {
      require(pred(l)(0)(0))
      l
    }

    def g(l: List[Int]): List[Int] = {
      require(pred[Int](l)(1)(2))
      l
    }
  end Impl

  @main def methodCallsWithMultipleArgsListsMain(): Unit =
    val res = Impl.f(List(1, 2, 3))
    val res2 = Impl.g(List(4, 5, 6))
end MethodCallsWithMultipleArgsLists