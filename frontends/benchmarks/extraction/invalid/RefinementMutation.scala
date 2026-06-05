package badMutation
import language.experimental.qualifiedTypes.silent

object A:
  case class Box(var x: Int):
    def incX() : Int = 
      x += 1
      x

    // should be rejected as `incX()` performs mutation 
    def foo() : {r : Boolean with r == (incX() > 0)} = x > 0

