import stainless.annotation._

object MainAnnotation3 {
  object Nested {
    @main
    @extern
    def theMain3: Unit = {
      println("Nasty main not using Stainless println!")
    }
  }
}