import stainless.lang.*
import stainless.math.sqrt

object FloatingPoints3 {
  def testBasicFloatOperators() = {
    val two = 2f
    val nine = 9f
    val ten = 10f
    assert(two + nine == 11f)
    assert(two - nine == -7f)
    assert(two * nine == 18f)
    assert(two / ten == 0.2f)
    assert(-two == -2f)
    assert(two != nine)
    assert(ten > nine)
    assert(two <= nine)
    assert(ten >= nine)
    assert(nine <= nine)
    assert(nine >= nine)
    assert(sqrt(nine) == 3f)
  }

  def testBasicDoubleOperators() = {
    val two = 2d
    val nine = 9d
    val ten = 10d
    assert(two + nine == 11d)
    assert(two - nine == -7d)
    assert(two * nine == 18d)
    assert(two / ten == 0.2d)
    assert(-two == -2d)
    assert(two != nine)
    assert(ten > nine)
    assert(two <= nine)
    assert(ten >= nine)
    assert(nine <= nine)
    assert(nine >= nine)
    assert(sqrt(nine) == 3d)
  }
}