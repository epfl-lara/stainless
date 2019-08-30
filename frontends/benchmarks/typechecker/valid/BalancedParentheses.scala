import stainless.annotation._
import stainless.lang._
import stainless.equations._
import scala.language.postfixOps

object BalancedParenthesesUtils {
  @inline
  def parallel[A,B](x: => A, y: => B): (A,B) = (x, y)

  @inline
  def check(p: Boolean): Boolean = p
}

import BalancedParenthesesUtils._

object BalancedParenthesesLists {

  sealed abstract class List[A] {

    def foldRight[B](z: B)(f: (A, B) => B): B = {
      decreases(this)
      this match {
        case Nil() => z
        case Cons(x, xs) => f(x, xs.foldRight(z)(f))
      }
    }

    def foldRight1(f: (A, A) => A): A = {
      require(!this.isEmpty())
      decreases(this)

      this match {
        case Cons(x, Nil()) => x
        case Cons(x, xs) => f(x, xs.foldRight1(f))
      }
    }

    def append(that: List[A]): List[A] = {
      decreases(this)
      this match {
        case Nil() => that
        case Cons(x, xs) => Cons(x, xs.append(that))
      }
    }

    def isEmpty() = this match {
      case Nil() => true
      case _     => false
    }

    def map[B](f: A => B): List[B] = {
      decreases(this)
      this match {
        case Nil() => Nil()
        case Cons(x, xs) => Cons(f(x), xs.map(f))
      }
    }
  }

  case class Nil[A]() extends List[A]
  case class Cons[A](head: A, tail: List[A]) extends List[A]
}

object Trees {

  import BalancedParenthesesLists._

  sealed abstract class Tree[A] {

    def toList(): List[A] = {
      decreases(this)
      this match {
        case Leaf(x) => Cons(x, Nil())
        case Branch(l, r) => l.toList().append(r.toList())
      }
    } ensuring (res => !res.isEmpty())

    def fold(f: (A, A) => A): A = {
      decreases(this)
      this match {
        case Leaf(x) => x
        case Branch(l, r) => {
          val (left, right) = parallel(l.fold(f), r.fold(f))

          f(left, right)
        }
      }
    }

    def map[B](f: A => B): Tree[B] = {
      decreases(this)
      this match {
        case Leaf(x) => Leaf(f(x))
        case Branch(l, r) => {
          val (left, right) = parallel(l.map(f), r.map(f))

          Branch(left, right)
        }
      }
    }
  }

  case class Leaf[A](value: A) extends Tree[A]
  case class Branch[A](left: Tree[A], right: Tree[A]) extends Tree[A]
}

object BalancedParentheses {

  import Trees._
  import BalancedParenthesesLists._

  /** Original algorithm to check whether is list of parenthesis is matched. */
  def isMatched(xs: List[Parenthesis]): Boolean = {
    xs.foldRight(BigInt(0))(updateCounter) == 0
  }

  def updateCounter(p: Parenthesis, c: BigInt): BigInt =
    if (c < 0) -1
    else p match {
      case OpenParenthesis()  => c - 1
      case CloseParenthesis() => c + 1
    }



  def min(a: BigInt, b: BigInt): BigInt = if (a <= b) a else b

  sealed abstract class Parenthesis
  case class OpenParenthesis() extends Parenthesis
  case class CloseParenthesis() extends Parenthesis

  case class Balance(extraOpen: BigInt, extraClose: BigInt) {

    def nonNegative(): Boolean = extraOpen >= 0 && extraClose >= 0

    def ++(that: Balance): Balance = {
      val openedClosed = min(this.extraOpen, that.extraClose)

      val newExtraOpen = this.extraOpen + that.extraOpen - openedClosed
      val newExtraClose = this.extraClose + that.extraClose - openedClosed

      Balance(newExtraOpen, newExtraClose)
    }

    def isBalanced(): Boolean = extraOpen == 0 && extraClose == 0

    def +:(p: Parenthesis): Balance = {
      p match {
        case OpenParenthesis() if extraClose > 0 => Balance(extraOpen, extraClose - 1)
        case OpenParenthesis() => Balance(extraOpen + 1, extraClose)
        case CloseParenthesis() => Balance(extraOpen, extraClose + 1)
      }
    }
  }

  def fromParenthesis(parenthesis: Parenthesis) = parenthesis match {
    case OpenParenthesis() => Balance(1, 0)
    case CloseParenthesis() => Balance(0, 1)
  }

  /** Sequentially checks the list of parenthesis is balanced. */
  def isMatchedSequential(xs: List[Parenthesis]): Boolean = {
    xs.foldRight(Balance(0, 0))(_ +: _).isBalanced()
  }

  /** Sequentially checks the list of parenthesis is balanced.
    *
    * This version is closer to the parallel one.
    */
  def isMatchedHybid(xs: List[Parenthesis]): Boolean = {
    require(!xs.isEmpty())

    xs.map(fromParenthesis).foldRight1(_ ++ _).isBalanced()
  }

  /** Checks "in parallel" that the given parenthesis are balanced. */
  def isMatchedParallel(tree: Tree[Parenthesis]): Boolean = {
    tree.map(fromParenthesis).fold(_ ++ _).isBalanced()
  }
}

object BalancedParenthesesSpecs {

  import BalancedParentheses._
  import Trees._
  import BalancedParenthesesLists._

  def append_is_associative(a: Balance, b: Balance, c: Balance): Boolean = {
    a ++ (b ++ c) == (a ++ b) ++ c
  }.holds

  def cons_append_equivalence(p: Parenthesis, b: Balance): Boolean = {
    require(b.nonNegative)

    p +: b == fromParenthesis(p) ++ b
  }.holds

  @induct
  def folds_equivalence(xs: List[Parenthesis]): Boolean = {
    xs.foldRight(Balance(0, 0))(fromParenthesis(_) ++ _) == xs.foldRight(Balance(0, 0))(_ +: _)
  }.holds

  def append(xs: List[Balance], ys: List[Balance]): Boolean = {
    require(!xs.isEmpty() && !ys.isEmpty())
    decreases(xs)

    val f: (Balance, Balance) => Balance = _ ++ _

    (f(xs.foldRight1(f), ys.foldRight1(f)) == xs.append(ys).foldRight1(f)) because {
      xs match {
        case Cons(x, Nil()) => {
          f(xs.foldRight1(f), ys.foldRight1(f)) ==| (xs.foldRight1(f) == x)        |
          f(x, ys.foldRight1(f))                ==| trivial                        |
          Cons(x, ys).foldRight1(f)             ==| (xs.append(ys) == Cons(x, ys)) |
          xs.append(ys).foldRight1(f)
        } qed
        case Cons(z, zs) => {
          f(xs.foldRight1(f), ys.foldRight1(f))        ==| (xs.foldRight1(f) == f(z, zs.foldRight1(f)))                 |
          f(f(z, zs.foldRight1(f)), ys.foldRight1(f))  ==| append_is_associative(z, zs.foldRight1(f), ys.foldRight1(f)) |
          f(z, f(zs.foldRight1(f), ys.foldRight1(f)))  ==| append(zs, ys)                                         |
          f(z, zs.append(ys).foldRight1(f))            ==| trivial                                                      |
          Cons(z, zs.append(ys)).foldRight1(f)         ==| trivial                                                      |
          xs.append(ys).foldRight1(f)
        } qed
      }
    }
  }.holds

  def fold_foldRight1_equivalence(tree: Tree[Balance]): Boolean = {
    decreases(tree)

    val f: (Balance, Balance) => Balance = _ ++ _

    (tree.fold(f) == tree.toList().foldRight1(f)) because {
      tree match {
        case Leaf(x) => {
          tree.fold(f)                 ==| trivial |
          x                            ==| trivial |
          Cons(x, Nil()).foldRight1(f) ==| trivial |
          tree.toList().foldRight1(f)
        } qed
        case Branch(l, r) => {
          tree.fold(f)                                          ==| trivial                              |
          f(l.fold(f), r.fold(f))                               ==| fold_foldRight1_equivalence(l) |
          f(l.toList().foldRight1(f), r.fold(f))                ==| fold_foldRight1_equivalence(r) |
          f(l.toList().foldRight1(f), r.toList().foldRight1(f)) ==| append(l.toList(), r.toList()) |
          l.toList().append(r.toList()).foldRight1(f)           ==| trivial                              |
          tree.toList().foldRight1(f)
        } qed
      }
    }
  }.holds

  @induct
  def map_append(xs: List[Parenthesis], ys: List[Parenthesis], f: Parenthesis => Balance): Boolean = {
    xs.map(f).append(ys.map(f)) == xs.append(ys).map(f)
  }.holds

  def toList_map_commutativity(tree: Tree[Parenthesis], f: Parenthesis => Balance): Boolean = {
    decreases(tree)
    (tree.map(f).toList() == tree.toList().map(f)) because {
      tree match {
        case Leaf(x) => trivial
        case Branch(l, r) => {
          check(toList_map_commutativity(l, f)) &&
          check(toList_map_commutativity(r, f)) &&
          check(map_append(l.toList(), r.toList(), f))
        }
      }
    }
  }.holds

  @induct
  def foldRight_accumulator_equivalence[A](xs: List[A], z: A, f: (A, A) => A): Boolean = {
    xs.foldRight(z)(f) == xs.append(Cons(z, Nil())).foldRight1(f)
  }.holds

  @induct
  def foldRight_map_commutivity(xs: List[Parenthesis]): Boolean = {
    xs.foldRight(Balance(0, 0))(fromParenthesis(_) ++ _) == xs.map(fromParenthesis).foldRight(Balance(0, 0))(_ ++ _)
  }.holds

  def remove_null_balance(xs: List[Parenthesis]): Boolean = {
    require(!xs.isEmpty())
    decreases(xs)

    (xs.map(fromParenthesis).append(Cons(Balance(0, 0), Nil())).foldRight1(_ ++ _) ==
        xs.map(fromParenthesis).foldRight1(_ ++ _)) because {
      xs match {
        case Cons(y, Nil()) => {
          xs.map(fromParenthesis).append(Cons(Balance(0, 0), Nil())).foldRight1(_ ++ _) ==|
            trivial                                                                       |
          fromParenthesis(y) ++ Balance(0, 0)                                           ==|
            trivial                                                                       |
          fromParenthesis(y)                                                            ==|
            trivial                                                                       |
          xs.map(fromParenthesis).foldRight1(_ ++ _)
        } qed
        case Cons(y, ys) => {
          xs.map(fromParenthesis).append(Cons(Balance(0, 0), Nil())).foldRight1(_ ++ _)                       ==|
            trivial                                                                                             |
          fromParenthesis(y) ++ ys.map(fromParenthesis).append(Cons(Balance(0, 0), Nil())).foldRight1(_ ++ _) ==|
            remove_null_balance(ys)                                                                             |
          fromParenthesis(y) ++ ys.map(fromParenthesis).foldRight1(_ ++ _)                                    ==|
            trivial                                                                                             |
          xs.map(fromParenthesis).foldRight1(_ ++ _)
        } qed
      }
    }
  }.holds



  def balanceToCounter(b: Balance): BigInt = b match {
    case Balance(extraOpen, _) if extraOpen > 0 => -1
    case Balance(BigInt(0), BigInt(0)) => 0
    case Balance(_, extraClose) if extraClose >= 0 => extraClose
    case _ => -1
  }

  def toCounter_updateCounter(b: Balance, p: Parenthesis): Boolean = {
    require(b.nonNegative())

    updateCounter(p, balanceToCounter(b)) == balanceToCounter(p +: b)
  }.holds


  def original_sequential_helper(xs: List[Parenthesis]): Boolean = {
    decreases(xs)
    val balance = xs.foldRight(Balance(0, 0))(_ +: _)
    val counter = xs.foldRight(BigInt(0))(updateCounter)

    {
      balanceToCounter(balance) == counter && balance.nonNegative()
    } because {
      xs match {
        case Nil() => trivial
        case Cons(p, ps) =>
          check(original_sequential_helper(ps)) &&
          check(ps.foldRight(Balance(0, 0))(_ +: _).nonNegative()) &&
          ({
            balanceToCounter(balance)                                               ==|
              trivial                                                                 |
            balanceToCounter(p +: ps.foldRight(Balance(0, 0))(_ +: _))              ==|
              toCounter_updateCounter(ps.foldRight(Balance(0, 0))(_ +: _), p)         |
            updateCounter(p, balanceToCounter(ps.foldRight(Balance(0, 0))(_ +: _))) ==|
              original_sequential_helper(ps)                                          |
            updateCounter(p, ps.foldRight(BigInt(0))(updateCounter))                ==|
              trivial                                                                 |
            counter
          } qed)
      }
    }
  }.holds


  def original_sequential_equivalence(xs: List[Parenthesis]): Boolean = {
    {
      isMatched(xs) == isMatchedSequential(xs)
    } because {
      check(original_sequential_helper(xs))
    }
  }.holds

  def sequential_hybrid_equivalence(xs: List[Parenthesis]): Boolean = {
    require(!xs.isEmpty())

    (isMatchedSequential(xs) == isMatchedHybid(xs)) because {
      {
        xs.foldRight(Balance(0, 0))(_ +: _)                                           ==|
          folds_equivalence(xs)                                                         |
        xs.foldRight(Balance(0, 0))(fromParenthesis(_) ++ _)                          ==|
          foldRight_map_commutivity(xs)                                                 |
        xs.map(fromParenthesis).foldRight(Balance(0, 0))(_ ++ _)                      ==|
          foldRight_accumulator_equivalence(
            xs.map(fromParenthesis), Balance(0, 0), (a: Balance, b: Balance) => a ++ b) |
        xs.map(fromParenthesis).append(Cons(Balance(0, 0), Nil())).foldRight1(_ ++ _) ==|
          remove_null_balance(xs)                                                       |
        xs.map(fromParenthesis).foldRight1(_ ++ _)
      } qed
    }
  }.holds

  def hybrid_parallel_equivalence(tree: Tree[Parenthesis]): Boolean = {
    (isMatchedHybid(tree.toList()) == isMatchedParallel(tree)) because {
      {
        tree.toList().map(fromParenthesis).foldRight1(_ ++ _)  ==|
          toList_map_commutativity(tree, fromParenthesis)        |
        tree.map(fromParenthesis).toList().foldRight1(_ ++ _)  ==|
          fold_foldRight1_equivalence(tree.map(fromParenthesis)) |
        tree.map(fromParenthesis).fold(_ ++ _)
      } qed
    }
  }.holds


  /** Main lemma. States that the sequential and parallel versions are equivalent. */
  def sequential_parallel_equivalence(tree: Tree[Parenthesis]): Boolean = {

    (isMatched(tree.toList()) == isMatchedParallel(tree)) because {
      check(original_sequential_equivalence(tree.toList())) &&
      check(sequential_hybrid_equivalence(tree.toList())) &&
      check(hybrid_parallel_equivalence(tree))
    }
  }.holds
}
