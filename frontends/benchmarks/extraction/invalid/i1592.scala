object i1592:
  val t: Thread = new Thread:
    override def run: Unit =
      wait()
