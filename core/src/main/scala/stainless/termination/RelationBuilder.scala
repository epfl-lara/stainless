/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap, ListBuffer}

trait RelationBuilder { self: Strengthener & OrderingRelation =>

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

      val (freshParams, subst) = freshenBindings(tfd.params, Map.empty)
      val paramPath = Path.empty `withBindings` (freshParams zip call.args)

      val (freshBound, newSubst) = freshenBindings(instPath.bound, subst)
      val freshSubst = (instPath.bound zip freshBound).toMap
      val newPath = instPath.map(freshSubst, exprOps.replaceFromSymbols(newSubst, _))

      val newCall =
        exprOps.replaceFromSymbols(newSubst, tfd.instantiate(that.call)).asInstanceOf[FunctionInvocation]

      Relation(fd, path `merge` paramPath `merge` newPath, newCall, inLambda || that.inLambda)
    }
  }

  /** Freshens the bindings `vds`, whose types may refer to the previous bindings (as dependent parameter
    * types do), or to the bindings substituted by `subst`. Returns the fresh bindings and the extended substitution. */
  def freshenBindings(vds: Seq[ValDef], subst: Map[ValDef, Expr]): (Seq[ValDef], Map[ValDef, Expr]) =
    vds.foldLeft((Seq.empty[ValDef], subst)) { case ((fresh, subst), vd) =>
      val fvd = ValDef(vd.id.freshen, typeOps.replaceFromSymbols(subst, vd.tpe), vd.flags).copiedFrom(vd)
      (fresh :+ fvd, subst + (vd -> fvd.toVariable))
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
                val res = Lambda(largs, transform(body, path `withBounds` largs `withCond` cnstr))
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
      // In the order of the calls in the body, as the queries about them are made in that order
      val relations: Set[Relation] = scala.collection.immutable.ListSet.from(collector.relations)
      relationCache(funDef) = (relations, funDefRelationSignature(funDef))
      relations
    }
  }

  // Holds values of the form (fd.id, fi.id, param.id) -> lemma
  val insertedApps: MutableMap[(Identifier, Identifier, Identifier), Seq[ValDef] => Expr] = 
    MutableMap.empty
}
