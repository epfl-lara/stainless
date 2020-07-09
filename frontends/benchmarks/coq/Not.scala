import stainless.lang._

object Test {

    def f(x: Boolean) = {
        require(x)
        !x
    } ensuring (y => !y)
}