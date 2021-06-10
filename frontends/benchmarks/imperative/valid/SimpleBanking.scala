import stainless.lang._

object SimpleBanking {

  case class BankAccount(var checking: BigInt)

  case class Transaction(
    account: BankAccount,
    var executed: Boolean
  )

  def execute(tr: Transaction): Unit = {
    tr.executed = true
    incr(tr.account)
  }

  def incr(acc: BankAccount): Unit = {
    acc.checking += 1
  }

  def incr2(from: BankAccount, to: BankAccount): Unit = {
    require(from.checking == 0)
    execute(Transaction(from, false))
    assert(from.checking == 1)
  }
}
