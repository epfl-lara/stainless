import stainless.lang._
import stainless.annotation._

object PrecondWitness4 {
  // Methods can have witnesses, with a receiver of their own
  case class Account(balance: BigInt) {
    require(balance >= 0)

    def withdraw(amount: BigInt): Account = {
      require(amount > 0 && amount <= balance)
      precondWitness(Account(10).withdraw(3))
      Account(balance - amount)
    }.ensuring(res => res.balance == balance - amount)
  }

  // With --sat-precond=annotated, the witness replaces the satisfiability check of the precondition
  @checkSatPrecondition
  def f(x: BigInt, y: BigInt): BigInt = {
    require(x > y && y > 0)
    precondWitness(f(2, 1))
    x - y
  }.ensuring(res => res > 0)
}
