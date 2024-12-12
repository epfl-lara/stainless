package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._
import scala.collection.mutable

final class TailRecIFOTransformer(val ctx: inox.Context) extends Transformer(SIR, TIR) with NoEnv {
  import from._

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  /* 
  * Find mutually recursive functions in a program
  * 
  * Example:
  *
  * def odd(n: Int): Boolean = if (n == 0) false else even(n - 1)
  * def even(n: Int): Boolean = if (n == 0) true else odd(n - 1)
  * 
  * Steps:
  * [x] for every function collect all the tail calls
  * [x] for every function collect all function references
  * [x] check that all self recursive references are tail calls
  * [x] group functions that tail recursively call each other
  */
  private def findMutuallyRecursive(prog: Prog): Seq[Seq[FunDef]] = { // TODO: abstract this to some tial rec utils/commons (not that easy because of the IR path dependency)
    val refsMap = prog.functions.map { fd =>
      var functionRefs = mutable.ListBuffer.empty[FunDef]
      val functionRefVisitor = new ir.Visitor(from) {
        override protected def visit(expr: Expr): Unit = expr match {
          case FunVal(fd) => functionRefs += fd
          case _ =>
        }
      }
      var tailFunctionRefs = mutable.ListBuffer.empty[FunDef]
      val tailRecCallVisitor = new ir.Visitor(from) {
        override protected def visit(expr: Expr): Unit = expr match {
          case Return(App(FunVal(fdcall), _, _)) => tailFunctionRefs += fdcall
          case _ =>
        }
      }
      functionRefVisitor(fd)
      tailRecCallVisitor(fd)
      fd -> (functionRefs, tailFunctionRefs)
    }.filter { case (fd, (functionRefs, tailFunctionRefs)) =>
      functionRefs.contains(fd) && functionRefs.filter(_ == fd).size == tailFunctionRefs.filter(_ == fd).size
    }.map { case (fd, (_, tailFunctionRefs)) =>
      fd -> tailFunctionRefs
    }

    val grouped: mutable.ListBuffer[Seq[from.FunDef]] = mutable.ListBuffer.from(refsMap.map(_(0)).map(Seq(_)))

    refsMap.foreach { case (fd, tailFunctionRefs) =>
      val myGroup = grouped.find(_.contains(fd))
      val referencedGroups = grouped.filter(_.exists(tailFunctionRefs.contains))
      val allGroups = (myGroup.toList ++ referencedGroups).distinct
      val newGroup = allGroups.flatten.distinct
      grouped --= allGroups
      grouped += newGroup
    }

    grouped.toSeq
  }

  override protected def rec(prog: from.Prog)(using Unit): to.Prog = {
    super.rec {
      val mutuallyRecursive = findMutuallyRecursive(prog)
      given printer.Context = printer.Context(0)
      mutuallyRecursive.foreach { fds =>
        println("Mutually recursive functions:")
        fds.foreach { fd =>
          println(printer(fd))
        }
      }
      prog
    }
  }

  private def freshId(id: String): to.Id = id + "_" + freshCounter.next(id)

  private val freshCounter = new utils.UniqueCounter[String]()
}
