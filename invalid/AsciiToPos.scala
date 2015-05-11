import leon.lang._
import leon.lang.synthesis._
import leon.lang.string._
import leon.collection._

object Justify {
  def tokenize(ascii: List[Char]): List[String] = tokenize0(ascii, "")
  def tokenize0(ascii: List[Char], wordAcc: String): List[String] = ascii match {
    case Nil() => Nil()
    case Cons(h, t) => if (h == ' ') {
      if (wordAcc.length == 0) {
        tokenize0(t, wordAcc)
      } else {
        Cons(wordAcc, tokenize0(t, ""))
      }
    } else {
      tokenize0(t, String(List(h)) + wordAcc)
    }
  }

  def asciiToPos(in: List[Char], index: Int): List[Int] = in match {
    case Nil() => Nil()
    case Cons(head, tail) => if(head == ' ') Cons(index, asciiToPos(tail, index+1)) else asciiToPos(tail, index+1)
  }

  def posToAscii(positions: List[Int], originalText: List[Char], currentPos: Int): List[Char] = positions match {
    case Cons(start, rest) =>
      if(start > currentPos) {
        Cons(' ', posToAscii(rest, originalText, currentPos+1))
      } else {
        originalText match {
          case Cons(l, ls) =>
            if(l == ' ') {
              Cons(' ', posToAscii(rest, ls, currentPos+1))
            } else {
              Cons(l, posToAscii(positions, ls, currentPos+1))
            }
          case Nil() => Nil()
        }
      }
    case Nil() => Nil()
  }

  def posToAsciiKeepTokens(ascii: List[Char]) = {
    posToAscii(asciiToPos(ascii, 0), ascii, 0)
  } ensuring(res => tokenize(res) == tokenize(ascii))
}
