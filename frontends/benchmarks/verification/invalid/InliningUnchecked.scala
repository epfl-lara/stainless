object InliningUnchecked {

  @inline def f: Int = 0

  def g: Int = {
    f
  }.ensuring(_ == 10)

}
