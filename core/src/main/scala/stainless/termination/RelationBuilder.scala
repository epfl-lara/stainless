/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

trait RelationBuilder { self: Strengthener with OrderingRelation =>

  import checker.program.trees._
  import checker.program.symbols.{given, _}

  val cfa: CICFA { val program: checker.program.type }

  case class Relation(fd: FunDef, path: Path, call: FunctionInvocation, inLambda: Boolean) {
    override def toString: String =
      "Relation(" + fd.id + "," + path.toClause + ", " +
        call.tfd.id + call.args.mkString("(", ",", ")") + "," + inLambda + ")"

    def compose(that: Relation): Relation = {
      val tfd = call.tfd
      val instPath = that.path.instantiate(tfd.tpSubst)
      assert(that.fd == tfd.fd, "Cannot compose relations with incompatible functions")

      val freshParams = tfd.params.map(_.freshen)
      val paramPath = Path.empty withBindings (freshParams zip call.args)
      val subst: Map[ValDef, Expr] = (tfd.params zip freshParams.map(_.toVariable)).toMap

      val freshSubst = (instPath.bound map { vd =>
        vd -> vd.freshen
      }).toMap
      val newSubst = subst ++ freshSubst.view.mapValues(_.toVariable)
      val newPath = instPath.map(freshSubst, exprOps.replaceFromSymbols(newSubst, _))

      val newCall =
        exprOps.replaceFromSymbols(newSubst, tfd.instantiate(that.call)).asInstanceOf[FunctionInvocation]

      Relation(fd, path merge paramPath merge newPath, newCall, inLambda || that.inLambda)
    }
  }

  protected type RelationSignature = (FunDef, Expr, Boolean, Set[(FunDef, Boolean)])

  protected def funDefRelationSignature(fd: FunDef): RelationSignature = {
    val strengthenedCallees = callees(fd).map(fd => fd -> strengthened(fd))
    (fd, fd.fullBody, checker.terminates(fd).isGuaranteed, strengthenedCallees)
  }

  private val relationCache: MutableMap[FunDef, (Set[Relation], RelationSignature)] = MutableMap.empty

  def getRelations(funDef: FunDef): Set[Relation] = relationCache.get(funDef) match {
    case Some((relations, signature)) if signature == funDefRelationSignature(funDef) => relations
    case _ => {
      val analysis = cfa.analyze(funDef.id)

      class Collector(override val s: self.checker.program.trees.type,
                      override val t: self.checker.program.trees.type)
                     (using override val symbols: self.checker.program.symbols.type)
        extends transformers.TransformerWithPC
           with transformers.DefinitionTransformer {
        type Env = Path
        val initEnv = Path.empty
        val pp = Path

        var inLambda: Boolean = false
        val relations: ListBuffer[Relation] = new ListBuffer

        override def transform(e: Expr, path: Path): Expr = e match {
          case fi @ FunctionInvocation(_, _, args) =>
            relations += Relation(funDef, path, fi, inLambda)

            fi.copy(args = (getFunction(fi.id).params.map(_.id) zip args).map {
              case (id, l @ Lambda(largs, body)) if analysis.isApplied(l) =>
                val cnstr = self.applicationConstraint(fi.id, id, largs, args)
                insertedApps += ((funDef.id, fi.id, id) -> (largs => self.applicationConstraint(fi.id, id, largs, args)))
                val old = inLambda
                inLambda = true
                val res = Lambda(largs, transform(body, path withBounds largs withCond cnstr))
                inLambda = old
                res
              case (_, arg) => transform(arg, path)
            })

          case l: Lambda =>
            if (analysis.isApplied(l)) {
              val old = inLambda
              inLambda = true
              val res = super.transform(e, path)
              inLambda = old
              res
            } else {
              l
            }

          case _ =>
            super.transform(e, path)
        }
      }

      val collector = new Collector(self.checker.program.trees, self.checker.program.trees)(using self.checker.program.symbols)
      collector.transform(funDef)
      val relations = collector.relations.toSet
      relationCache(funDef) = (relations, funDefRelationSignature(funDef))
      relations
    }
  }

  // Holds values of the form (fd.id, fi.id, param.id) -> lemma
  val insertedApps: MutableMap[(Identifier, Identifier, Identifier), Seq[ValDef] => Expr] = 
    MutableMap.empty
}
