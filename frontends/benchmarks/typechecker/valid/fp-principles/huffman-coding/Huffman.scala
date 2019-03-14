/* Copyright 2017- LARA, EPFL, Lausanne.
   Author: Dragana Milovancevic. */
package patmat

import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

/**
 * Assignment 4: Huffman coding
 *
 */
object Huffman {
  /**
   * A huffman code is represented by a binary tree.
   *
   * Every `Leaf` node of the tree represents one character of the alphabet that the tree can encode.
   * The weight of a `Leaf` is the frequency of appearance of the character.
   * The branches of the huffman tree, the `Fork` nodes, represent a set containing all the characters
   * present in the leaves below it. The weight of a `Fork` node is the sum of the weights of these
   * leaves.
   */
    sealed abstract class CodeTree(){
      lazy val chars: Set[Char] = {
        decreases(this)
        this match {
          case Fork(left, right) => left.chars ++ right.chars
          case Leaf(char, weight) => Set(char)
        }
      } ensuring(res => res != Set.empty[Char])
    }
    case class Fork(left: CodeTree, right: CodeTree) extends CodeTree
    case class Leaf(char: Char, weight: BigInt) extends CodeTree

    // Part 1: Basics
    def max(x: BigInt, y: BigInt) = if (x > y) x else y

    def weight(tree: CodeTree): BigInt = {
      decreases(tree)
      tree match {
        case Fork(left, right) => weight(left) + weight(right)
        case Leaf(char, weight) => weight
      }
    }

    def chars(tree: CodeTree): List[Char] = {
      decreases(tree)
      tree match  {
        case Fork(left, right) => chars(left) ++ chars(right)
        case Leaf(char, weight) => List(char)
      }
    } ensuring(res => !res.isEmpty)

    def chars(trees: List[CodeTree]): Set[Char] = {
      decreases(trees)
      if (trees.isEmpty) Set[Char]()
      else trees.head.chars ++ chars(trees.tail)
    } ensuring(res => trees.isEmpty || res != Set.empty[Char])

    def makeCodeTree(left: CodeTree, right: CodeTree) = {
      Fork(left, right)
    } ensuring(res => res.chars == chars(List[CodeTree](left, right)))

    def makeCodeTree(left: Leaf, right: Leaf) = {
      require(left.char != right.char && consistent(List[CodeTree](left,right)))
      Fork(left, right)
    } ensuring(res => consistent(res) && res.chars == chars(List[CodeTree](left, right)))

    def isLeaf(tree: CodeTree): Boolean = {
      tree match {
        case Leaf(c, w) => true
        case _ => false
      }
    }

    def isFork(tree: CodeTree): Boolean = {
      tree match {
        case Fork(_, _) => true
        case _ => false
      }
    }

  // Part 2: Generating Huffman trees

  /**
   * This function computes for each unique character in the list `chars` the number of
   * times it occurs.
   */
    def times(chars: List[Char]): List[(Char, BigInt)] = {
      require(!chars.isEmpty)
      val distinctList = distinct(chars, List())
      distinctList zip distinctList.map(elem => chars.count(e => e == elem))
    } ensuring(res => listEqu(distinct(chars, List()), distinct(chars, List()).map(elem => chars.count(e => e == elem)))
                     && distinct(chars, List()).content == chars.content)

    def distinct(chars: List[Char], acc: List[Char]): List[Char] = {
      require(isDistinctList(acc) && chars.size+acc.size>0)
      decreases(chars)
      chars match {
        case y::ys => {
          if (isDistinctList(y::acc)) distinct(ys, y::acc)
          else distinct(ys, acc)
        }
        case _ => acc
      }
    } ensuring(res => isDistinctList(res) && res.content == acc.content ++ chars.content)

    def listEqu(list: List[Char], zipWith: List[BigInt]): Boolean = {
      require(list.size == zipWith.size)
      decreases(list)
      (list zip zipWith).map(elem => elem._1) == list because {
        if (list.isEmpty) true
        else listEqu(list.tail, zipWith.tail)
      }
    }.holds

    def isDistinctList(list: List[Char]): Boolean = {
      decreases(list)
      list match {
        case x::xs => !(xs.contains(x)) && isDistinctList(xs)
        case _ => true
      }
    }

    def isDistinctList(list: List[CodeTree]): Boolean = {
      decreases(list)
      list match {
        case x::xs => xs.forall(elem => (elem.chars & x.chars) == Set.empty[Char]) && isDistinctList(xs)
        case _ => true
      }
    }

    def sortedByWeight(list: List[CodeTree]): Boolean = ListOps.isSorted(list.map(weight))

    def insert(l:CodeTree, list: List[CodeTree]): List[CodeTree] = {
      require(sortedByWeight(list))
      decreases(list)
      list match {
        case y::ys => if (weight(l) < weight(y)) l::list
                      else y::insert(l, ys)
        case _ => List(l)
      }
    } ensuring(res => res.size == list.size+1 && sortedByWeight(res) &&
                     (l::list).content == res.content && chars(res) == chars(list) ++ l.chars)


    def sortLeafList(list: List[CodeTree]): List[CodeTree] = {
      decreases(list)
      list match {
        case l::ls => insert(l, sortLeafList(list.tail))
        case _ => List[CodeTree]()
      }
    } ensuring(res => chars(res) == chars(list) && sortedByWeight(res)
                     && res.content == list.content && res.size == list.size)


  /**
   * Returns a list of `Leaf` nodes for a given frequency table `freqs`.
   *
   * The returned list should be ordered by ascending weights (i.e. the
   * head of the list should have the smallest weight), where the weight
   * of a leaf is the frequency of the character.
   */
    def makeOrderedLeafList(freqs: List[(Char, BigInt)]): List[CodeTree] = {
      require(!freqs.isEmpty && isDistinctList(freqs.map(elem => elem._1)))
      def foreach(freqs: List[(Char, BigInt)]): List[CodeTree] = {
        require(isDistinctList(freqs.map(elem => elem._1)))
        decreases(freqs)
        if (freqs.isEmpty) List[CodeTree]()
        else new Leaf(freqs.head._1, freqs.head._2) ::foreach(freqs.tail)
      } ensuring(res => chars(res) == freqs.map(elem => elem._1).content && res.size == freqs.size)
      sortLeafList(foreach(freqs))
    } ensuring(res => sortedByWeight(res) &&
                     chars(res) == freqs.map(elem => elem._1).content && res.size == freqs.size)


  /**
   * Checks whether the list `trees` contains only one single code tree.
   */
    def singleton(trees: List[CodeTree]): Boolean = {
      trees.size == 1
    }

  /**
   * The parameter `trees` of this function is a list of code trees ordered
   * by ascending weights.
   *
   * This function takes the first two elements of the list `trees` and combines
   * them into a single `Fork` node. This node is then added back into the
   * remaining elements of `trees` at a position such that the ordering by weights
   * is preserved.
   *
   * If `trees` is a list of less than two elements, that list should be returned
   * unchanged.
   */
    def combine(trees: List[CodeTree]): List[CodeTree] = {
      require(sortedByWeight(trees))
      if (trees.size < 2) trees
      else insert(makeCodeTree(trees.head, trees.tail.head), trees.tail.tail)
    } ensuring(res => sortedByWeight(res) &&
                     chars(res) == chars(trees) && (trees.size<2 || res.size == trees.size-1))


  /**
   * This function will be called in the following way:
   *
   *   until(trees)
   *
   * where `trees` is of type `List[CodeTree]`.
   *
   * In such an invocation, `until` calls the functions `singleton` and `combine` until the list of
   * code trees contains only one single tree, and then return that singleton list.
   *
   */
    def until(trees: List[CodeTree]): List[CodeTree] = {
      require(!trees.isEmpty && sortedByWeight(trees))
      decreases(trees.size)
      if (singleton(trees)) trees
      else until(combine(trees))
    } ensuring(res => res.size <= trees.size && singleton(res) && !res.isEmpty && chars(trees) == chars(res))


  /**
   * This function creates a code tree which is optimal to encode the text `chars`.
   *
   * The parameter `charsList` is an arbitrary text. This function extracts the character
   * frequencies from that text and creates a code tree based on them.
   */
    def createCodeTree(charsList: List[Char]): CodeTree = {
      require(!charsList.isEmpty && sortedByWeight(makeOrderedLeafList(times(charsList))))
      until(makeOrderedLeafList(times(charsList))).head
    } ensuring(res => res.chars == charsList.content)


  // Part 3: Decoding

  /**
   * This function decodes the bit sequence `bits` using the code tree `tree` and returns
   * the resulting list of characters.
   */
    def decode(tree: CodeTree, bits: List[Boolean]): List[Char] = {
      require(isFork(tree))
      decreases(bits.size)

      if (bits.isEmpty) List()
      else {
        assert(decodeCharLength(tree, bits))
        decodeChar(tree, bits) match {
          case Some((c, rest)) => c :: decode(tree, rest)
          case None() => List()
        }
      }
    }

    def decodeCharLength(tree: CodeTree, bits: List[Boolean]): Boolean = {
      decreases(tree)

      check(
        tree match  {
          case Fork(left, right) => {
            if (bits.isEmpty) true
            else if (!bits.head) decodeCharLength(left, bits.tail)
            else decodeCharLength(right, bits.tail)
          }
          case Leaf(char, weight) => true
        }
      )

      decodeChar(tree, bits) match {
        case Some((_, rest)) =>
          rest.size <= bits.size && (isFork(tree) ==> rest.size < bits.size)
        case _ => true
      }
    }.holds

    def decodeChar(tree: CodeTree, bits: List[Boolean]): Option[(Char, List[Boolean])] = {
      decreases(tree)
      tree match {
        case Fork(left, right) => {
          if (bits.isEmpty) None()
          else if (!bits.head) decodeChar(left, bits.tail)
          else decodeChar(right, bits.tail)
        }
        case Leaf(char, weight) => Some(char, bits)
      }
    }

  /**
   * A Huffman coding tree for the French language.
   * Generated from the data given at
   *   http://fr.wikipedia.org/wiki/Fr%C3%A9quence_d%27apparition_des_lettres_en_fran%C3%A7ais
   */
    val frenchCode: CodeTree = {
    Fork(Fork(Fork(Leaf('s',121895),Fork(Leaf('d',56269),Fork(Fork(Fork(Leaf('x',5928),Leaf('j',8351)),Leaf('f',16351)),Fork(Fork(Fork(Fork(Leaf('z',2093),Fork(Leaf('k',745),Leaf('w',1747))),Leaf('y',4725)),Leaf('h',11298)),Leaf('q',20889))))),Fork(Fork(Leaf('o',82762),Leaf('l',83668)),Fork(Fork(Leaf('m',45521),Leaf('p',46335)),Leaf('u',96785)))),Fork(Fork(Fork(Leaf('r',100500),Fork(Leaf('c',50003),Fork(Leaf('v',24975),Fork(Leaf('g',13288),Leaf('b',13822))))),Fork(Leaf('n',108812),Leaf('t',111103))),Fork(Leaf('e',225947),Fork(Leaf('i',115465),Leaf('a',117110)))))
  }

  /**
   * What does the secret message say? Can you decode it?
   * For the decoding use the `frenchCode' Huffman tree defined above.
   */
  //val secret: List[BigInt] = List(0,0,1,1,1,0,1,0,1,1,1,0,0,1,1,0,1,0,0,1,1,0,1,0,1,1,0,0,1,1,1,1,1,0,1,0,1,1,0,0,0,0,1,0,1,1,1,0,0,1,0,0,1,0,0,0,1,0,0,0,1,0,1)
    val secret: List[Boolean] = List(false,false,true,true,true,false,true,false,true,true,true,false,false,true,true,false,true,false,false,true,true,false,true,false,true,true,false,false,true,true,true,true,true,false,true,           false,true,true,false,false,false,false,true,false,true,true,true,false,false,true,false,false,true,false,false,false,true,false,false,false,true,false,true)


  /**
   * Write a function that returns the decoded secret
   */
    def decodedSecret: List[Char] = {
      decode(frenchCode, secret)
    }


  // Part 4a: Encoding using Huffman tree

  /**
   * This function encodes `text` using the code tree `tree`
   * into a sequence of bits.
   */
    def encode(tree: CodeTree)(text: List[Char]): List[Boolean] = {
      require(text.content subsetOf tree.chars)
      text.flatMap(elem => encodeChar(tree, elem))
    }

    def encodeChar(tree: CodeTree, cx: Char): List[Boolean] = {
      decreases(tree)
      tree match  {
        case Fork(left, right) => {
          if (!tree.chars.contains(cx)) List()
          else if (left.chars.contains(cx)) false::encodeChar(left, cx)
          else true::encodeChar(right, cx)
        }
        case Leaf(chars, weight) => List()
      }
    }


  // Encoding/decoding proof

    def decodeOneChar(tree: CodeTree, cx: Char, bits: List[Boolean]): Boolean = {
      require(tree.chars.contains(cx) && isFork(tree))
      decreases(tree)

      tree match {
        case Fork(left, right) => {
          if (encodeChar(tree, cx).isEmpty) ()
          else if (!encodeChar(tree, cx).head) {
            check(isLeaf(left) || decodeOneChar(left, cx, bits))
          } else {
            check(isLeaf(right) || decodeOneChar(right, cx, bits))
          }
        }
        case Leaf(char, weight) => ()
      }

      decodeChar(tree, encodeChar(tree, cx) ++ bits) match {
        case Some((c, rest)) => c == cx && rest == bits
        case None() => false
      }
    }.holds

    def decodeEncode(tree: CodeTree, text: List[Char]): Boolean = {
      require(
        text.content.subsetOf(tree.chars) &&
        isFork(tree)
      )
      decreases(text)

      if (text.isEmpty) {
        ()
      } else {
        check(decodeOneChar(tree, text.head, encode(tree)(text.tail)))
        check(decodeEncode(tree, text.tail))
      }

      decode(tree, encode(tree)(text)) == text
    }.holds

    def decodeEncode(text: List[Char]): Boolean = {
      require(!text.isEmpty && isFork(createCodeTree(text)))
      val tree = createCodeTree(text)
      check(decodeEncode(tree, text))
      decode(tree, encode(tree)(text)) == text
    }.holds

  /**
    * CodeTree functions
    */
    def consistent(tree: CodeTree): Boolean = {
      decreases(tree)
      tree match{
        case Fork(left, right) => consistent(left) && consistent(right) && isDistinctList(List(left, right))
        case Leaf(char, weight) => true
      }
    }

    def consistent(trees: List[CodeTree]): Boolean = {
      decreases(trees)
      if (trees.size == 0) true
      else consistent(trees.head) && consistent(trees.tail) && isDistinctList(trees)
    }

    def depth(tree: CodeTree, char: Char): BigInt = {
      decreases(tree)
      tree match{
        case Fork(left, right) => {
          if (left.chars.contains(char))
            depth(left,char) + 1
          else if (right.chars.contains(char))
            depth(right, char) + 1
          else
            0
        }
        case Leaf(char, weight) => 0
      }
    }

    def height(tree: CodeTree): BigInt = {
      decreases(tree)
      tree match {
        case Fork(left, right) => {
          val hl = height(left)
          val hr = height(right)
          max(hl, hr) + 1
        }
        case Leaf(char, weight) => 0
      }
    }

    def height(trees: List[CodeTree]): BigInt = {
      decreases(trees)
      if (trees.isEmpty) 0
      else {
        val headHeight = height(trees.head)
        val tailHeight = height(trees.tail)
        max(headHeight, tailHeight)
      }
    }

    def checkCharDiff(char1: Char, char2: Char, tree: CodeTree): Boolean = {
      require(char1 != char2)
      decreases(tree)
      (isLeaf(tree) || encodeChar(tree, char1).isEmpty || encodeChar(tree, char1) != encodeChar(tree, char2)) because {
        tree match {
          case Leaf(c, w) => true
          case Fork(left, right) => checkCharDiff(char1, char2, left) && checkCharDiff(char1, char2, right)
        }
      }
    }.holds

 // Part 4b: Encoding using code table


  /**
   * This function returns the bit sequence that represents the character `char` in
   * the code table `table`.
   */
    def codeBits(table: Map[Char, List[Boolean]])(char: Char): List[Boolean] = {
      table.getOrElse(char, List())
    }

  /**
   * Given a code tree, create a code table which contains, for every character in the
   * code tree, the sequence of bits representing that character.
   *
   */
    def convert(tree: CodeTree): Map[Char, List[Boolean]] = {
      val text = chars(tree)

      def convertHelp(tree: CodeTree, acc: List[Boolean]): Map[Char, List[Boolean]] = {
        decreases(tree)
        val text = chars(tree)
        tree match  {
          case Fork(left, right) => mergeCodeTables(convertHelp(left, (acc++List(false))),convertHelp(right, (acc++List(true))), text)
          case Leaf(char, weight) => Map((char, acc))
        }
      }

      tree match  {
        case Fork(left, right) => mergeCodeTables(convertHelp(left, List(false)), convertHelp(right, List(true)), text)
        case Leaf(char, weight) => Map((char, List(false)))
      }
    }

  /**
   * This function takes two code tables and merges them into one. Depending on how you
   * use it in the `convert` method above, this merge method might also do some transformations
   * on the two parameter code tables.
   */
    def mergeCodeTables(a: Map[Char, List[Boolean]], b: Map[Char, List[Boolean]], text: List[Char]): Map[Char, List[Boolean]] = {
      decreases(text)
   //   a++b

      if (text.isEmpty) Map[Char, List[Boolean]]()
      else {
        val c = text.head
        val tab = mergeCodeTables(a, b, text.tail)
        if (a.contains(c)) tab + (c, a(c))
        else if (b.contains(c)) tab + (c, b(c))
        else tab
      }

    }

  /**
   * This function encodes `text` according to the code tree `tree`.
   *
   * To speed up the encoding process, it first converts the code tree to a code table
   * and then uses it to perform the actual encoding.
   */
    def quickEncode(tree: CodeTree)(text: List[Char]): List[Boolean] = {
      encodeTable(convert(tree), text)
    }

    def encodeTable(table: Map[Char, List[Boolean]], text: List[Char]): List[Boolean] = {
      decreases(text)
      if (text.isEmpty) List[Boolean]()
      else codeBits(table)(text.head) ++ encodeTable(table, text.tail)
    }
}
