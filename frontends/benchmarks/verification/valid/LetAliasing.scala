// https://github.com/epfl-lara/stainless/issues/400

object LetAliasing {
  case class MutableBox(var value: Boolean)

  def mutate(b: MutableBox): Unit = {
    b.value = true
  }

  def prop = {
    val box1 = MutableBox(false)
    val box2 = box1
    mutate(box2)
    assert(box1.value)
    assert(box2.value)
    box2
  }
}
