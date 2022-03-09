object i1051c {
  case class BankAccount(var checking: BigInt)
  case class Transaction(
    account: BankAccount,
    account2: BankAccount,
    var executed: Boolean
  )
  def execute(tr: Transaction): Unit = {
    tr.executed = true
    val old = tr.account2.checking
    incr(tr.account)
    assert(tr.account2.checking == old)
  }
  def incr(acc: BankAccount): Unit = {
    acc.checking += 1
  }
  def incr2(from: BankAccount, to: BankAccount): Unit = {
    require(from.checking == 0)
    execute(Transaction(from, from, false)) // Illegal aliasing within expr
    assert(from.checking == 1)
  }
  def test = incr2(BankAccount(0), BankAccount(0))
}