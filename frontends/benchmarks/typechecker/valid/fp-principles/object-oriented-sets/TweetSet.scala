/* Copyright 2017- LARA, EPFL, Lausanne.
   Author: Dragana Milovancevic. */
   // TODO: check for style, verify properties
package objsets
import stainless.collection._
import stainless.lang._
import stainless.proof._
import stainless.annotation._

import TweetSetUtils._
import TweetSetLemmas._

// A class to represent tweets.
case class Tweet(val user: String, val text: Int, val retweets: Int)

/**
 * This represents a set of objects of type `Tweet` in the form of a binary search
 * tree. Every branch in the tree has two children (two `TweetSet`s). There is an
 * invariant which always holds: for every branch `b`, all elements in the left
 * subtree are smaller than the tweet at `b`. The elements in the right subtree are
 * larger.
 *
 */
sealed abstract class TweetSet {
  // The subset of elements in this set for which predicate `p` is true
  def filter(p: Tweet => Boolean): TweetSet

  // For each recursive function such as `filterAcc`, we use a lexicographic
  // measure of the form (size, 1) for the abstract function, and (size, 0) for
  // the concrete function. In Stainless, abstract functions end up being
  // dispatch functions that call the concrete functions. And the recursive
  // calls that appear in the concrete function refer to the abstract function.
  // The lexicographic measure is therefore approriate:
  // * Either the dispatch function calls the concrete function with the same
  //   argument (i.e. the size does not change) but the second component of the
  //   measure decreases from 1 to 0,
  // * or the concrete function calls the dispatch function on an argument of
  //   a smaller size (and the second component is then allowed to go from 0 to
  //   1).

  // Helper method for `filter` that propagates accumulated tweets
  def filterAcc(p: Tweet => Boolean, acc: TweetSet): TweetSet = {
    decreases((size, 1))
    (??? : TweetSet)
  }

  // A new `TweetSet` that is the union of `this` and `that`
  def union(that: TweetSet): TweetSet = {
    decreases((this, 1))
    (??? : TweetSet)
  }

  // Tweet from `this` set with greatest retweet count
  def mostRetweeted: Tweet

  // Auxiliary function for `mostRetweeted`
  def mostRetweetedAcc(acc: Tweet): Tweet = {
    decreases((this, 1))
    (??? : Tweet)
  }

  /**
   * A list containing all tweets of this set, sorted by retweet count
   * in descending order. The head of the resulting list should
   * have the highest retweet count.
   */
  def descendingByRetweet: TweetList = {
    require(isSearchTree)
    decreases((size, 1))
    (??? : TweetList)
  }

   /**
  * Returns a new `TweetSet` which contains all elements of this set, and the
   * the new element `tweet` in case it does not already exist in this set.
   *
   * If `this.contains(tweet)`, the current set is returned.
   */
  def incl(tweet: Tweet): TweetSet = {
    decreases((this, 1))
    (??? : TweetSet)
  }

  /**
   * Returns a new `TweetSet` which excludes `tweet`.
   */
  def remove(tweet: Tweet): TweetSet = {
    decreases((this, 1))
    (??? : TweetSet)
  }

  /**
   * Tests if `tweet` exists in this `TweetSet`.
   */
  def contains(tweet: Tweet): Boolean = {
    decreases((this, 1))
    (??? : Boolean)
  }

  /**
   * Tests (slower) if `tweet` exists in this `TweetSet`.
   */
  def slowContains(tweet: Tweet): Boolean = {
    decreases((this, 1))
    (??? : Boolean)
  }

  /**
   * This method takes a function and applies it to every element in the set.
   */
  def foreach(f: Tweet => Unit): Unit = {
    decreases((this, 1))
    (??? : Unit)
  }

  /**
   * This method checks that a predicate holds for every element in the set.
   */
  def forall(f: Tweet => Boolean): Boolean = {
    decreases((this, 1))
    (??? : Boolean)
  }

  /**
   * The size of the set
   */
  def size: BigInt = {
    decreases((this, 1))
    (??? : BigInt)
  }

  /**
   * Returns true if the tree is actually a binary search tree
   */
  def isSearchTree: Boolean = {
    decreases((this, 1))
    (??? : Boolean)
  }
}

case class Empty() extends TweetSet {
    def filter(p: Tweet => Boolean): TweetSet = new Empty
    def filterAcc(p: Tweet => Boolean, acc: TweetSet): TweetSet = acc
    def contains(tweet: Tweet): Boolean = false
    def slowContains(tweet: Tweet): Boolean = false
    def incl(tweet: Tweet): TweetSet = new NonEmpty(tweet, new Empty, new Empty)
    def remove(tweet: Tweet): TweetSet = this
    def foreach(f: Tweet => Unit): Unit = ()
    def forall(p: Tweet => Boolean): Boolean = true
    def union(that: TweetSet): TweetSet = that
    def mostRetweeted(): Tweet = new Tweet("empty", -1,-1)
    def mostRetweetedAcc(max: Tweet): Tweet = max
    def descendingByRetweet: TweetList = Nil()
    def size: BigInt = 0
    def isSearchTree: Boolean = true
}

case class NonEmpty(elem: Tweet, left: TweetSet, right: TweetSet) extends TweetSet {

    def descendingByRetweet: TweetList = {
      require(isSearchTree)
      decreases((size, 0))

      val elem = mostRetweeted
      check(mostRetweetedAccContained(this, elem))
      check(this.slowContains(elem))
      check(slowContainedIsContained(this, elem))
      check(this.contains(elem))
      check(removeSize(this, elem))
      check(removeIsSearchTree(this, elem))
      Cons(elem, remove(elem).descendingByRetweet)
    }

    def filter(p: Tweet => Boolean): TweetSet = {
      filterAcc(p, new Empty)
    }

    def filterAcc(p: Tweet => Boolean, acc: TweetSet): TweetSet = {
      decreases((size, 0))

      // this lemma shows that the size of remove(elem) is strictly smaller than this.size
      assert(unionSize(left,right))
      if(p(elem)) remove(elem).filterAcc(p, acc incl elem)
      else remove(elem).filterAcc(p, acc)
    }

    def mostRetweetedAcc(max: Tweet): Tweet = {
      decreases((this, 0))

      if(elem.retweets > max.retweets)
        maxRetweets(left.mostRetweetedAcc(elem), right.mostRetweetedAcc(elem))
      else
        maxRetweets(left.mostRetweetedAcc(max), right.mostRetweetedAcc(max))
    }

    def mostRetweeted(): Tweet = {
      mostRetweetedAcc(elem)
    }

    def contains(x: Tweet): Boolean = {
      decreases((this, 0))
      if (x.text < elem.text) left.contains(x)
      else if (elem.text < x.text) right.contains(x)
      else true
    }

    def slowContains(x: Tweet): Boolean = {
      decreases((this, 0))
      x == elem || left.slowContains(x) || right.slowContains(x)
    }

    def incl(x: Tweet): TweetSet = {
      decreases((this, 0))
      if (x.text < elem.text) new NonEmpty(elem, left.incl(x), right)
      else if (elem.text < x.text) new NonEmpty(elem, left, right.incl(x))
      else this
    } ensuring(res => (res contains x))

    def remove(tw: Tweet): TweetSet = {
      decreases((this, 0))
      if (tw.text < elem.text) new NonEmpty(elem, left.remove(tw), right)
      else if (elem.text < tw.text) new NonEmpty(elem, left, right.remove(tw))
      else left.union(right)
    }

    def foreach(f: Tweet => Unit): Unit = {
      decreases((this, 0))

      f(elem)
      left.foreach(f)
      right.foreach(f)
    }


    def forall(p: Tweet => Boolean): Boolean = {
      decreases((this, 0))

      p(elem) && left.forall(p) && right.forall(p)
    }

    def union(that: TweetSet): TweetSet = {
      decreases((this, 0))

      left union (right union (that incl elem))
    }

    def size: BigInt = {
      decreases((this, 0))

      1 + left.size + right.size
    } ensuring(_ >= 0)

    def isSearchTree: Boolean = {
      decreases((this, 0))

      left.isSearchTree &&
      right.isSearchTree &&
      left.forall(smallerThan(elem)) &&
      right.forall(greaterThan(elem))
    }
}

object TweetSetUtils {

  def smallerThan(x: Tweet) = (y: Tweet) => y.text < x.text
  def greaterThan(x: Tweet) = (y: Tweet) => y.text > x.text

  def maxRetweets(t1: Tweet, t2:Tweet) = {
    if(t1.retweets > t2.retweets) t1
    else t2
  }

}

object TweetSetLemmas {

  def inclSize(s: TweetSet, e: Tweet): Boolean = {
    decreases(s)
    s match {
      case Empty() =>
        (s incl e).size <= s.size + 1
      case NonEmpty(elem, left, right) =>
        // FIXME: change these to assertions when they are no longer simplified for postconditions
        inclSize(left, e) &&
        inclSize(right, e) &&
        (s incl e).size <= s.size + 1
    }
  } holds

  def unionSize(s1: TweetSet, s2: TweetSet): Boolean = {
    decreases(s1)
    s1 match {
      case Empty() =>
        (s1 union s2).size <= s1.size + s2.size
      case NonEmpty(elem, left, right) =>
        // FIXME: change these to assertions when they are no longer simplified for postconditions
        unionSize(left, right union (s2 incl elem)) &&
        unionSize(right, s2 incl elem) &&
        inclSize(s2, elem) &&
        (s1 union s2).size <= s1.size + s2.size
    }
  } holds

  def removeSize(s: TweetSet, e: Tweet): Boolean = {
    decreases(s)
    s match {
      case Empty() =>
        (s.contains(e) && (s remove e).size <= s.size - 1) ||
        (!s.contains(e) && (s remove e).size <= s.size)
      case NonEmpty(elem, left, right) =>
        // FIXME: change these to assertions when they are no longer simplified for postconditions
        removeSize(left, e) &&
        removeSize(right, e) &&
        unionSize(left,right) &&
        (
          (s.contains(e) && (s remove e).size <= s.size - 1) ||
          (!s.contains(e) && (s remove e).size <= s.size)
        )
    }
  } holds


  def mostRetweetedAccContained(s: TweetSet, max: Tweet): Boolean = {
    decreases(s)
    val elem = s.mostRetweetedAcc(max)

    s match {
      case Empty() => ()
      case NonEmpty(e, left, right) =>
        check(mostRetweetedAccContained(left, max))
        check(mostRetweetedAccContained(left, e))
        check(mostRetweetedAccContained(right, max))
        check(mostRetweetedAccContained(right, e))
    }

    elem == max || s.slowContains(elem)
  } holds

  def instantiateForall(s: TweetSet, p: Tweet => Boolean, elem: Tweet): Boolean = {
    require(s.slowContains(elem) && s.forall(p))
    decreases(s)

    s match {
      case Empty() => ()
      case NonEmpty(e, left, right) =>
        if (left.slowContains(elem)) instantiateForall(left, p, elem)
        else if (right.slowContains(elem)) instantiateForall(right, p, elem)
    }

    p(elem)
  } holds

  def slowContainedIsContained(s: TweetSet, elem: Tweet): Boolean = {
    require(s.isSearchTree && s.slowContains(elem))
    decreases(s)

    s match {
      case Empty() => ()
      case NonEmpty(e, left, right) =>
        if (left.slowContains(elem)) {
          instantiateForall(left, smallerThan(e), elem)
          check(slowContainedIsContained(left, elem))
        }
        else if (right.slowContains(elem)) {
          instantiateForall(right, greaterThan(e), elem)
          check(slowContainedIsContained(right, elem))
        }
    }

    s.contains(elem)
  } holds

  def inclForall(s: TweetSet, elem: Tweet, p: Tweet => Boolean): Boolean = {
    require(s.forall(p) && p(elem))
    decreases(s)

    s match {
      case Empty() => ()
      case NonEmpty(e, left, right) =>
        check(inclForall(left, elem, p))
        check(inclForall(right, elem, p))
    }

    (s incl elem).forall(p)
  } holds

  def inclIsSearchTree(s: TweetSet, elem: Tweet): Boolean = {
    require(s.isSearchTree)
    decreases(s)

    s match {
      case Empty() =>
        check((s incl elem).isSearchTree)
      case NonEmpty(e, left, right) =>
        if (elem.text < e.text) {
          check(inclIsSearchTree(left, elem))
          check(inclForall(left, elem, smallerThan(e)))
          check((s incl elem).isSearchTree)
        } else if (elem.text > e.text) {
          check(inclIsSearchTree(right, elem))
          check(inclForall(right, elem, greaterThan(e)))
          check((s incl elem).isSearchTree)
        }
    }

    (s incl elem).isSearchTree
  } holds

  def unionForall(s1: TweetSet, s2: TweetSet, p: Tweet => Boolean): Boolean = {
    require(s1.forall(p) && s2.forall(p))
    decreases(s1)

    s1 match {
      case Empty() => ()
      case NonEmpty(elem, left, right) =>
        check(inclForall(s2, elem, p))
        check(unionForall(right, s2 incl elem, p))
        check(unionForall(left, right union (s2 incl elem), p))
    }

    (s1 union s2).forall(p)
  } holds

  def unionIsSearchTree(s1: TweetSet, s2: TweetSet): Boolean = {
    require(s1.isSearchTree && s2.isSearchTree)
    decreases(s1)

    s1 match {
      case Empty() => ()
      case NonEmpty(elem, left, right) =>
        check(inclIsSearchTree(s2, elem))
        check(unionIsSearchTree(right, s2 incl elem))
        check(unionIsSearchTree(left, right union (s2 incl elem)))
    }

    (s1 union s2).isSearchTree
  } holds

  def removeForall(s: TweetSet, p: Tweet => Boolean, elem: Tweet): Boolean = {
    require(s.forall(p))
    decreases(s)

    s match {
      case Empty() => ()
      case NonEmpty(e, left, right) =>
        check(removeForall(left, p, elem))
        check(removeForall(right, p, elem))
        check(unionForall(left, right, p))
    }

    s.remove(elem).forall(p)
  } holds

  def removeIsSearchTree(s: TweetSet, elem: Tweet): Boolean = {
    require(s.isSearchTree)
    decreases(s)

    s match {
      case Empty() => ()
      case NonEmpty(e, left, right) =>
        check(removeForall(left, smallerThan(e), elem))
        check(removeForall(right, greaterThan(e), elem))
        check(unionIsSearchTree(left, right))
        check(removeIsSearchTree(left, elem))
        check(removeIsSearchTree(right, elem))
    }

    s.remove(elem).isSearchTree
  } holds
}

sealed trait TweetList {
  def head: Tweet
  def tail: TweetList
  def isEmpty: Boolean
  def foreach(f: Tweet => Unit): Unit = {
    decreases(this)
    if (!isEmpty) {
      f(head)
      tail.foreach(f)
    }
  }
}

case class Nil() extends TweetList {
  def head = new Tweet("empty", -1,-1)
  def tail = Nil()
  def isEmpty = true
}

case class Cons(val head: Tweet, val tail: TweetList) extends TweetList {
  def isEmpty = false
}

object GoogleVsApple {
  // TODO: Finish the exercise
}
