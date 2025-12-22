import scala.reflect.ClassTag
import stainless.annotation.law

/** Tests that Stainless accepts `ClassTag` parameters. It should strip them
  * from the extracted code, as they are not needed for verification.
  */
object ClassTagLaws:
  trait MyTrait:
    def test[T: ClassTag](v1: T, v2: T): Boolean
    def combine[T: ClassTag](v1: T, v2: T): T
    @law def testForall[T: ClassTag](v1: T, v2: T): Boolean = this.test(this.combine(v1, v2), this.combine(v1, v2))
  end MyTrait
  
  case object Impl extends MyTrait:
    override def test[T: ClassTag](v1: T, v2: T): Boolean = v1 == v2
    override def combine[T: ClassTag](v1: T, v2: T): T = v1
    override def testForall[T: ClassTag](v1: T, v2: T): Boolean = this.test(this.combine(v1, v2), this.combine(v1, v2))
  end Impl
end ClassTagLaws