/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.concurrent.duration._
import scala.annotation.tailrec
import scala.collection._
import scala.collection.mutable.{ Map => MutableMap, Set => MutableSet }

import trees._
/**
 * A context-insensitive control-flow analysis that computes
 * the closures that are passed to call backs of given function.
 */
trait CICFA { 
  
  val program: Program { val trees: Trees }
  
  import program._
  import program.trees._
  import program.symbols._
  import program.trees.exprOps._  
  
  val rootfun: program.trees.FunDef
  
  // Abstract values and closures
  sealed abstract class AbsValue 
//  {
//    def greaterEquals(other: AbsValue): Boolean
//  }
  case class Closure(lam: program.trees.Lambda) extends AbsValue 
//    env: AbsEnv
//    def greaterEquals(other: AbsValue) = other match {
//      case Closure(lam2, env2) => lam2 == lam && env.greater(env2)
//      case _ => false
//    }    
//    override def hashCode = lam.hashCode // this works also for >= check
//  }
  case class External() extends AbsValue 
//  {
//    def greaterEquals(other: AbsValue) = other.isInstanceOf[External]
//  }
  
  case class AbsEnv(store: Map[Variable,Set[AbsValue]]) { // mapping from a set of live variables to their value
    // checks if this >= AbsElem
    def greaterEquals(other: AbsEnv): Boolean = {
      other.store.forall { (k,v) => store.contains(k) && 
        other.store(k).subsetOf(store(k))
      }
    }
    
    def join(other: AbsEnv): AbsEnv = {
      val ikeys = store.keySet.intersect(other.store.keySet)
      AbsEnv((store.keySet ++ other.store.keyset).map{ 
        case v if ikeys(v) => (v -> (store(v) ++ other.store(v)))
        case v if store.contains(v) => (v -> store(v))
        case v if other.store.contains(v) => (v -> other.store(v))
      })       
    }
  }
   
  case class Summary(in: AbsEnv, out: AbsEnv) {
    def get(fact: AbsEnv): Option[AbsEnv] = {
      if(in.greaterEquals(fact))  Some(out) else None
    }
  }
  
  val tabulation = MutableMap[program.trees.FunDef, Summary] // summary of each function
  val callers = Map[FunDef, Set[FunDef]]
  
  // initialize summaries to identity function from bot to bot 
  program.definedFunctions.foreach { fd: FunDef => 
    val bot = AbsEnv(fd.params.map { vd => vd.id.toVariable -> Set[AbsValue]() })
    tabulation += (fd -> Summary(bot, bot))    
  }
  
  var worklist = List(rootfun)
  
  // iteratively process functions from the worklist.
  // (a) at every function call, join the arguments passed in with the in fact in the summary
  //       -- if the join results in a greater value, add the function back to the worklist  
  // (b) use the summary in the tabulation to complete the intra-procedural analysis
  // (c) Update the caller information on seeing a function call.
  // (d) if the return value of the function is found to be different from the return value in the tabulation   
  //       -- update the entry in the tabulation to a the new value
  //       -- add all callers of the function to the worklist
  // Repeat this until a fix point is reached
  
  def analyze() = {
    var currfun = worklist.head 
    worklist = worklist.tail
    
    // the order of traversal is very important here, so using a custom traversal
    
  }
}
