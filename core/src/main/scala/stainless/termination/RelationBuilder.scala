/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import transformers.CollectorWithPC
import scala.collection.mutable.{Map => MutableMap}

trait RelationBuilder { self: Strengthener =>

  import checker.program.trees._
  import checker.program.symbols._

  val cfa: CICFA { val program: checker.program.type }

  case class Relation(fd: FunDef, path: Path, call: FunctionInvocation, inLambda: Boolean) {
    override def toString : String = "Relation(" + fd.id + "," + path + ", " +
      call.tfd.id + call.args.mkString("(",",",")") + "," + inLambda + ")"

    def compose(that: Relation): Relation = {
      val tfd = call.tfd
      val instPath = that.path.instantiate(tfd.tpSubst)
      assert(that.fd == tfd.fd, "Cannot compose relations with incompatible functions")

      val freeVars = instPath.freeVariables -- tfd.params.map(_.toVariable).toSet
      val freeSubst = (freeVars.map(_.toVal) zip freeVars.map(_.freshen)).toMap

      val freshParams = tfd.params.map(_.freshen)
      val paramPath = Path.empty withBindings (freshParams zip call.args)
      val subst: Map[ValDef, Expr] = (tfd.params zip freshParams.map(_.toVariable)).toMap

      val freshSubst = (instPath.bounds map { vd => vd -> vd.freshen }).toMap
      val newSubst = subst ++ freshSubst.mapValues(_.toVariable) ++ freeSubst
      val newPath = instPath.map(freshSubst, exprOps.replaceFromSymbols(newSubst, _))

      val newCall = exprOps.replaceFromSymbols(newSubst, tfd.instantiate(that.call)).asInstanceOf[FunctionInvocation]

      Relation(fd, path merge paramPath merge newPath, newCall, inLambda || that.inLambda)
    }
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
      val analysis = cfa.analyze(funDef.id)

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

          case l: Lambda =>
            if (analysis.isApplied(l)) {
              val old = inLambda
              inLambda = true
              val res = super.rec(e, path)
              inLambda = old
              res
            } else {
              l
            }

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
