import stainless.lang._

object Not {

    def f(x: Boolean) = {
        require(x)
        !x
    }.ensuring(y => !y)
}
