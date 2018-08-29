object Example{

  import stainless.lang._
  import stainless.annotation._
  import stainless.collection._
  import stainless.math.{max,min,abs}

/* 
  /*
    This example shows that lexicographic orders are not totally synthesized
    in fact the RelationProcessor only check for lexicographic orders in the 
    order of the given parameters. The paper:

      Finding lexicographic orders for termination proofs in Isabelle/Hol

    may be useful to synthesize this orders.  
  */

  def ackermann(n: BigInt, m: BigInt): BigInt = {
    require(m >= 0 && n >= 0)
    decreases(m,n)
    if (m == 0) n + 1
    else if (n == 0) ackermann(1,m-1)
    else ackermann(ackermann(n - 1,m),m-1)
  } ensuring (_ >= 0)
*/  

  /*
    An example function that cannot be proved terminating with the current implementation.
    Chi et alii. claim that their method synthesizes this kind of function. 

    The problem that remains to be solved is that of complexity, which was reduced in the 
    second part of Chi's paper and further reduced by his coauthor. We still need to precise
    if this reduction is general of for specific functions.

    Here there is one evidence, in normal programs, linear combinations me be sufficient to prove
    termination. Here the if-condition is quite disturbing for the solver?
  */
/*
  def ackermann(m:BigInt, n: BigInt): BigInt = {
    require(m >= 0 && n >= 0)
    if (m == 0) n + 1
    else if (n == 0) ackermann(m - 1, 1)
    else ackermann(m - 1, ackermann(m, n - 1))
  } ensuring (_ >= 0)  
 

  def f(x: BigInt, y: BigInt): BigInt = {
    require(x >= 0 && y >= 0)
    decreases(max(BigInt(2)*x - 1,BigInt(2)*y))
    if(x == 0 || y == 0){
      BigInt(0)
    } else {
      if(ackermann(x,y) == 1) {
        f(y,y-1)
      } else {
        f(y,x-1)
      }  
    }  
  }  
  */

 // a decrease with linear non classic formula
 //a size decrease that happens in recursive call

/*

  /*
    An example program where we need to resort to the chain processor
  */
  def ackermann(m:BigInt, n: BigInt): BigInt = {
    require(m >= 0 && n >= 0)
    if (m == 0) n + 1
    else if (n == 0) ackermann(m - 1, 1)
    else ackermann(m - 1, ackermann(m, n - 1))
  } ensuring (_ >= 0)  
 
  def h(n: BigInt): BigInt = { 
    g(n-1)
  }

  def g(n: BigInt): BigInt = {
    require(n >= 0)
    if(n == 0){ 
      BigInt(0)
    } else { 
      if(ackermann(n,n+1) == 1){
        h(n)
      } else {
        g(n-1)
      }  
    }
  }
*/  

  /*
    Certain simple instances of this problem are automatically solved (see paper for non-determined values)
    As always it is necessary to put a non-trivial condition in the if construct to avoid the automatic proof. 
    Note the need to write an external measure function being max{(x,z),(y,w)}
  */
  /* 
  def ackermann(m:BigInt, n: BigInt): BigInt = {
    require(m >= 0 && n >= 0)
    if (m == 0) n + 1
    else if (n == 0) ackermann(m - 1, 1)
    else ackermann(m - 1, ackermann(m, n - 1))
  } ensuring (_ >= 0)  
 
  def measure(x: BigInt, y: BigInt,z: BigInt,w: BigInt) = {
    val cond = (x < y) || (x == y && z < w)
    val m = if(cond) y else x
    val n = if(cond) w else z
    (m,n)
  }

  def f(x: BigInt, y: BigInt,z: BigInt,w: BigInt): BigInt = {
    require(x >= 0 && y >= 0 && z >= 0 && w >= 0)
    decreases(measure(x,y,z,w)._1,measure(x,y,z,w)._2)
    if(x == 0 || y == 0 || z == 0 || w == 0){
      BigInt(0)
    } else {
      if(ackermann(x,y) == 1) {
        f(x,x-1,z-1,y)
      } else {
        f(y-1,y,x,w-1)
      }  
    }  
  }  
  */

  /*
    Another example not checked automatically by the system
  */

/*
  def mn(x: BigInt, y: BigInt): BigInt = {
    require(x >= 0 && y >= 0)
    //decreases(min(x,y))
    decreases(true)
    if(x == 0 || y == 0){
      BigInt(0)
    } else {
      if(x < y) mn(x-1,y)
      else mn(x+1,y-1)  
    }
  }
*/

 /*
   Examples from the context of linear ranking functions.
   Use irankFinder
 */
/*
  def fi(fi: BigInt, fj: BigInt, fk: BigInt): BigInt = {
    var i = fi
    var j = fj
    var k = fk
    
    while((i <= 100) && (j <= k)){
     i = j
     j = i+1
     k = k-1
    }
    i+j+k
  } 
*/   
/*
  def f(i: BigInt, j: BigInt, k: BigInt): BigInt = {
    if(i > 100 || j > k){
      BigInt(0)
    } else {
      f(j,i+1,k-1)
    }
  }
}
 */


// checking true
// we will use zero as the trivial measure
/*
  def f(n: BigInt): BigInt = {
    decreases(BigInt(0))
    n
  }
*/
/*
  def fun(l: List[Int]): Int = {
    decreases(0)
    l match {
      case Nil() => 0
      case Cons(x,xs) => 1 + fun(xs)  
    } 
  }
*/
/*
  def tryBitVectors(){
    val v: Int = 0
    v.toBigInt
  }
*/  
/*
  def f(n: BigInt): BigInt = {
    require(n >= 0)
    if(n == 0){
      BigInt(0)
    } else {
      if(n >= 5 && n <= 10) {
        f(n-1)
      } else {
        g(n)
      }    
    }       
  }

  def g(n: BigInt): BigInt = {
    require(n >= 0)

    val i: Long = 8
    if(n == 0){
      BigInt(0)
    } else {
      g(n-1)
    }
  }
*/  

 // Quicksort example

/*
  def isSorted(list: List[BigInt]): Boolean = {
    list match {
      case Cons(x, xs @ Cons(y, _)) => x <= y && isSorted(xs)
      case _ => true
    }
  }

  def appendSorted(l1: List[BigInt], l2: List[BigInt]): List[BigInt] = {
    require(isSorted(l1) && isSorted(l2) && (l1.isEmpty || l2.isEmpty || l1.last <= l2.head))
    l1 match {
      case Nil() => l2
      case Cons(x, xs) => Cons(x, appendSorted(xs, l2))
    }
  } ensuring { res =>
    isSorted(res) &&
    res.content == l1.content ++ l2.content &&
    res.size == l1.size + l2.size
  }

  def quickSort(list: List[BigInt]): List[BigInt] = {
    //decreases(list.size, 0)
    list match {
      case Nil() => Nil[BigInt]()
      case Cons(x, xs) => par(x, Nil(), Nil(), xs)
    }
  } ensuring { res =>
    isSorted(res) &&
    res.content == list.content &&
    res.size == list.size
  }

  def par(x: BigInt, l: List[BigInt], r: List[BigInt], ls: List[BigInt]): List[BigInt] = {
    require(
      forall((a: BigInt) => l.contains(a) ==> a <= x) &&
      forall((a: BigInt) => r.contains(a) ==> x < a)
    )
    //decreases(l.size + r.size + ls.size, ls.size + 1)

    ls match {
      case Nil() => appendSorted(quickSort(l), Cons(x, quickSort(r)))
      case Cons(x2, xs2) => if (x2 <= x) par(x, Cons(x2, l), r, xs2) else par(x, l, Cons(x2, r), xs2)
    }
  }
*/

  /*
    This is a kind of situation the chain processor can't handle, probably because it 
    designed for global termination rather than local termination. Here the algorithm would
    construct a loop around the chains on g and check for decreases. 
  */
/*
  def f(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n,BigInt(0))
    }   
  } 

  def g(n: BigInt,where: BigInt): BigInt = {
    require(n >= BigInt(0) && where >= BigInt(0))
    if(where == BigInt(0)){
      f(n-1)
    } else {
      g(n+1,BigInt(1))
    }
  } 
*/

  /*
    This example cannot be handled by the relation processor but by the chain processor. (EX-C1)
  */
/*
  def f(n: BigInt): BigInt = {
    require(n >= BigInt(2))
    decreases(n-1,0)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n-2)
    }   
  } 

  def g(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n,1)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      f(n+1) 
    }
  }
*/
 
  /*
    Applying D.W. heuristic
  */
/*
  def f(n: BigInt): BigInt = {
    require(n >= BigInt(2))
    decreases(3*n)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n-2)
    }   
  } 

  def g(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(3*n+5)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      h(n+3)
    }
  }

  def h(n: BigInt): BigInt = {
    require(n >= BigInt(2))
    decreases(3*n-5)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      f(n-2)
    }
  }
*/

 /*
  Nicolas Example
  */
/*
def f(n: BigInt): BigInt = {
    require(n >= BigInt(2))
    decreases(n-1,2)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n-1)
    }   
  } 

  def g(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n,1)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      h(n-1)
    }
  }

  def h(n: BigInt): BigInt = {
    require(n >= BigInt(2))
    decreases(n+1,0)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      f(n+1)
    }
  }
*/  

  /*
    Variation of Nicolas example with linear shift
  */  

  def f(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n+3,2)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      g(n+3)
    }   
  } 

  def g(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n,1)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      h(n-2)
    }
  }

  def h(n: BigInt): BigInt = {
    require(n >= BigInt(0))
    decreases(n+2,0)
    if(n == BigInt(0)){
      BigInt(0)
    } else {
      f(n-2)
    }
  }


  /*
    How to use the recursion processor. 

    Here for l.tail we need to write either of the following:

     l.asInstanceOf[Cons[BigInt]].t
     n match { case Cons(x, xs) => ...xs... }

    where in the second we have already checked it is non-empty. 

    The problem comes because RecursionProcessor does not look into
    the definition of function tail and therefore does not see that 
    in fact it returns an ADTSelector and therefore a subtree.

    Preliminary tests indicated option 1 is not supported?
  */
/*  
  def f(l: List[BigInt]): BigInt = {
    //decreases(n.size)
    if(l.isEmpty){
      BigInt(0)
    } else {    
      l match { case Cons(x, xs) => f(xs) }
      //f(l.asInstanceOf[Cons[BigInt]].t)
    }   
  } 
*/

}
