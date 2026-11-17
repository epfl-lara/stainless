import stainless.lang._

object CakeMixins {
  trait Trees {
    def name: String = "trees"
  }
  trait ExtTrees extends Trees {
    override def name: String = "ext"
  }
  trait Printing extends Trees {
    override def name: String = "printing " + super.name
  }
  trait Fixed extends Trees {
    override def name: String = "fixed"
  }

  case object ext extends ExtTrees with Printing
  case object fixedFirst extends Fixed with ExtTrees

  def name(t: Trees): String = t.name

  // The super call goes to `ExtTrees`, not to `Trees`
  def wrongSuper: Unit = {
    assert(name(ext) == "printing trees")
  }

  // `ExtTrees` comes last in the linearization
  def wrongOrder: Unit = {
    assert(name(fixedFirst) == "fixed")
  }
}
