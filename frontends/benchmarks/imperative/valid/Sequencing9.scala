object Sequencing9 {

  case class Box(var value: Int)

  sealed trait OptionMut {
    def isEmpty: Boolean = this match {
      case SomeMut(_) => false
      case NoneMut() => true
    }

    def head: Box = {
      require(!isEmpty)
      val SomeMut(v) = this
      v
    }

    def filter(p: Int => Boolean): OptionMut = {
      // Here, the normalizer phase of AntiAliasing will
      // introduce an extra binding to this.head (due to being of a mutable type)
      // However, that binding may not appear before the !isEmpty condition, because
      // && is short-circuiting.
      // That is, the following normalization would be incorrect:
      //   val targetBound = this.head // Not guarded by !isEmpty anymore!
      //   if (!isEmpty && p(targetBound.value)) SomeMut(head)
      // while the following is correct:
      //   if (!isEmpty && {val targetBound = this.head; p(targetBound.value)}) SomeMut(head)
      if (!isEmpty && p(head.value)) SomeMut(head)
      else NoneMut()
    }
  }

  case class SomeMut(var box: Box) extends OptionMut
  case class NoneMut() extends OptionMut
}
