object PrivateIsFinal {
  trait SomeTrait {
    private def someSecret(x: BigInt): BigInt = x + 42

    final def testSecret(x: BigInt): Unit = {
      assert(someSecret(x) == 42 + x)
    }
  }
}
