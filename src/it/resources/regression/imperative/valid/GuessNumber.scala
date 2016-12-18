import stainless.lang._
import stainless.lang.synthesis._

object GuessNumber {

  case class State(var seed: BigInt)

  def random(min: Int, max: Int)(implicit state: State): Int = {
    state.seed += 1
    choose((x: Int) => min <= x && x <= max)
  }
  
  def main()(implicit state: State): Unit = {
    val choice = random(0, 10)

    var guess = random(0, 10)
    var top = 10
    var bot = 0

    (while(bot < top) {
      if(isGreater(guess, choice)) {
        top = guess-1
        guess = random(bot, top)
      } else if(isSmaller(guess, choice)) {
        bot = guess+1
        guess = random(bot, top)
      }
    }) invariant(guess >= bot && guess <= top && bot >= 0 && top <= 10 && bot <= top && choice >= bot && choice <= top &&
                 true)
    val answer = bot
    assert(answer == choice)
  }

  def isGreater(guess: Int, choice: Int): Boolean = guess > choice
  def isSmaller(guess: Int, choice: Int): Boolean = guess < choice

}
