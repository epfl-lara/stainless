import stainless.lang._
import stainless.lang.StaticChecks._

import SFuns._

object Lists {

  abstract class List[A] {
    def ::(el: A) = Cons(el, this)
  }
  case class Cons[A](head: A, tail: List[A]) extends List[A]
  case class Nil[A]() extends List[A]

  //def sizeOverflow[A](l: List[A]): Int = (l match {
  //  case Nil() => 0
  //  case Cons(_, t) => 1 + sizeOverflow(t)
  //}) ensuring(res => res >= 0)

  def sizeSpec[A](l: List[A]): BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => 1 + sizeSpec(t)
  }) //ensuring(res => res >= 0)

  def size[A](l: List[A]): BigInt = {
    var res: BigInt = 0
    var lst: List[A] = l
    (while(!isEmpty(lst)) {
      lst = tail(lst)
      res += 1
    }) invariant(res + sizeSpec(lst) == sizeSpec(l))
    res
  } ensuring(res => res == sizeSpec(l))


  def isEmpty[A](l: List[A]): Boolean = l match {
      case Nil() => true
      case _ => false
  }

  def tail[A](l: List[A]): List[A] = {
    require(!isEmpty(l))
    l match {
      case Cons(_, t) => t
    }
  }

  def foreach[A, S](l: List[A], sf: SFun[A, S, Unit]): Unit = l match {
    case Cons(x,xs) =>
      sf(x)
      foreach(xs, sf)
    case Nil() =>
      ()
  }

  def testForeach(): Unit = {
    val l: List[Int] = 1::2::3::4::5::6::7::8::9::10::Nil[Int]()
    val sum = State(0)
    foreach(l, SFun[Int, Int, Unit](
                 sum, (el: Int, s: State[Int]) => s.value += el))
    assert(sum.value == 55)
  }

}


object Banking {

  case class BankAccount(var checking: BigInt, var savings: BigInt) {
    require(checking >= 0 && savings >= 0)

    def balance: BigInt = {
      checking + savings
    } ensuring(_ >= 0)

    def save(amount: BigInt): Unit = {
      require(amount >= 0 && amount <= checking)
      checking = checking - amount
      savings = savings + amount
    } ensuring(_ => balance == old(this).balance)
  }

  def transfer(from: BankAccount, to: BankAccount, amount: BigInt): Unit = {
    require(amount >= 0 && from.checking >= amount)
    from.checking -= amount
    to.checking += amount
  } ensuring(_ => from.balance + to.balance == old(from).balance + old(to).balance &&
                  from.checking == old(from).checking - amount &&
                  to.checking == old(to).checking + amount)

  case class Transaction(
    operation: (BankAccount, BigInt) => Boolean,
    cancel: (BankAccount, BigInt) => Unit,
    account: BankAccount, amount: BigInt, var executed: Boolean
  ) {

    def execute(): Boolean = {
      require(!executed)
      executed = operation(account, amount)
      executed
    }

    def rollback(): Unit = {
      require(executed)
      cancel(account, amount)
      executed = false
    }
  }

  def retry(transaction: Transaction, times: Int): Boolean = {
    require(times > 0 && !transaction.executed)
    var i = 0
    var success = false
    (while(i < times && !success) {
      success = transaction.execute()
      i += 1
    }) invariant(i >= 0 && i <= times && success == transaction.executed)
    success
  } ensuring(status => status == transaction.executed)

  def execute(transaction1: Transaction, transaction2: Transaction): Boolean = {
    require(!transaction1.executed && !transaction2.executed)
    if(transaction1.execute()) {
      if(transaction2.execute()) true else {
        transaction1.rollback()
        false
      }
    } else false
  } ensuring(executed => (
    (executed ==> (transaction1.executed && transaction2.executed)) &&
    (!executed ==> (!transaction1.executed && !transaction2.executed))
  ))


  def addOp(acc: BankAccount, amount: BigInt): Boolean = {
    if(amount < 0) false else {
      acc.checking += amount
      true
    }
  }
  def subOp(acc: BankAccount, amount: BigInt): Boolean = {
    if(amount < 0 || amount > acc.checking) false else {
      acc.checking -= amount
      true
    }
  }

  def transfer2(from: BankAccount, to: BankAccount, amount: BigInt): Unit = {
    require(amount >= 0 && from.checking >= amount)

    val status = execute(
      Transaction((acc, amount) => subOp(acc, amount),
                  (acc, amount) => addOp(acc, amount),
                  from, amount, false),
      Transaction((acc, amount) => addOp(acc, amount),
                  (acc, amount) => subOp(acc, amount),
                  to, amount, false)
    )
    assert(status)
  } ensuring(_ => 
      from.balance + to.balance == old(from).balance + old(to).balance &&
      from.checking == old(from).checking - amount &&
      to.checking == old(to).checking + amount
    )

  def test(): Unit = {
    val add = Transaction((acc, amount) => {
                            if(amount < 0) false else {
                              acc.checking += amount
                              true
                            }
                          },
                          (acc, amount) => {
                            if(amount < 0 || amount > acc.checking) () else {
                              acc.checking -= amount
                            }
                          },
                          BankAccount(1000, 2000), 500, false)

    add.execute()
    assert(add.account.checking == 1500)
    add.rollback()
    assert(add.account.checking == 1000)
  }


}

object SFuns {

  case class State[A](var value: A)

  case class SFun[A, S, B](state: State[S], f: (A, State[S]) => B) {
    def apply(a: A): B = f(a, state)
  }

  def makeCounter: SFun[Unit, BigInt, BigInt] = {
    SFun(State(0),
         (_: Unit, c: State[BigInt]) => { 
           c.value += 1
           c.value
         })
  }

  def test: Unit = {
    val counter = makeCounter
    val c1 = counter()
    val c2 = counter()
    assert(c1 == 1)
    assert(c2 == 2)
  }

}
