/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import transformers.CollectorWithPC
import scala.collection.mutable.{Map => MutableMap}

trait RelationBuilder { self: Strengthener =>

  import checker.program.trees._
  import checker.program.symbols._

  case class Relation(fd: FunDef, path: Path, call: FunctionInvocation, inLambda: Boolean) {
    override def toString : String = "Relation(" + fd.id + "," + path + ", " +
      call.tfd.id + call.args.mkString("(",",",")") + "," + inLambda + ")"
  }

  protected type RelationSignature = (FunDef, Expr, Boolean, Set[(FunDef, Boolean)])

  protected def funDefRelationSignature(fd: FunDef): RelationSignature = {
    val strengthenedCallees = callees(fd).map(fd => fd -> strengthened(fd))
    (fd, fd.fullBody, checker.terminates(fd).isGuaranteed, strengthenedCallees)
  }

  private val relationCache : MutableMap[FunDef, (Set[Relation], RelationSignature)] = MutableMap.empty

  def getRelations(funDef: FunDef): Set[Relation] = relationCache.get(funDef) match {
    case Some((relations, signature)) if signature == funDefRelationSignature(funDef) => relations
    case _ => {
      object collector extends CollectorWithPC {
        type Result = Relation
        val trees: self.checker.program.trees.type = self.checker.program.trees
        val symbols: self.checker.program.symbols.type = self.checker.program.symbols

        var inLambda: Boolean = false

        override protected def rec(e: Expr, path: Path): Expr = e match {
          // @nv: instead of injecting the path condition here, we could collect the relations on
          //      a transformed program. However, special care would need to be taken to make sure
          //      FunDef pointers make sense, so I'm keeping this hacky solution for know.
          case FunctionInvocation(id, tps, args) =>
            accumulate(e, path)
            val funDef = getFunction(id)
            FunctionInvocation(id, tps, (funDef.params.map(_.id) zip args) map { case (id, arg) =>
              rec(arg, path withCond self.applicationConstraint(funDef, id, arg, args))
            })

          case _: Lambda =>
            val old = inLambda
            inLambda = true
            val res = super.rec(e, path)
            inLambda = old
            res

          case _ =>
            super.rec(e, path)
        }

        protected def step(e: Expr, path: Path): List[Result] = e match {
          // XXX: filter out certain function calls ??
          case fi: FunctionInvocation =>
            List(Relation(funDef, path, fi, inLambda))
          case _ => Nil
        }
      }

      val relations = collector.collect(funDef).toSet
      relationCache(funDef) = (relations, funDefRelationSignature(funDef))
      relations
    }
  }
}
