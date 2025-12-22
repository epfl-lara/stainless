import stainless.collection.List
import scala.reflect.ClassTag

object ClassTagMethodCalls:
  trait Interface:
    def pred[C: ClassTag](l: List[C]): Boolean = true
    def f[C: ClassTag](l: List[C]): List[C]
  end Interface

  case object Impl extends Interface:
    override def f[C: ClassTag](l: List[C]): List[C] = {
      require(pred(l))
      l
    }
  end Impl

  @main def classTagMethodCallsMain(): Unit =
    val res = Impl.f(List(1, 2, 3))
end ClassTagMethodCalls