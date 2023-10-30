/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object GuessNumber {

  case class State(var seed: BigInt)

  def between(a: Int, x: Int, b: Int): Boolean = a <= x && x <= b

  def random(min: Int, max: Int)(implicit state: State): Int = {
    require(min <= max)
    state.seed += 1
    assert(between(min, min, max))
    choose[Int]((x: Int) => between(min, x, max))
  }.ensuring(res => min <= res && res <= max)

  def main()(implicit state: State): Unit = {
    val choice = random(0, 10)

    var guess = random(0, 10)
    var top = 10
    var bot = 0
    var done = false

    (while(!done && bot < top) {
      decreases((if (done) 0 else 1, top - bot))
      if(isGreater(guess, choice)) {
        top = guess-1
        guess = random(bot, top)
      } else if(isSmaller(guess, choice)) {
        bot = guess+1
        guess = random(bot, top)
      } else {
        done = true
      }
    }) invariant(guess >= bot && guess <= top && bot >= 0 && top <= 10 && bot <= top && choice >= bot && choice <= top && (done ==> (guess == choice)))
    val answer = guess
    assert(answer == choice)
  }

  def isGreater(guess: Int, choice: Int): Boolean = guess > choice
  def isSmaller(guess: Int, choice: Int): Boolean = guess < choice

}
