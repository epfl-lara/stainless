package stainless
package utils

// Utility for processing counter-examples.
// The main function is `tryRemapCtex` which attempts to map a counter-example back to the function it originated from
// by ordering the ctex variables according to the ordering of the function parameters, by instantiating generic types
// to a given numeric type (TyParamSubst) and by providing default values for function parameters missing in the ctex.
trait CtexRemapping { self =>
  val trees: ast.Trees
  import trees._

  // Type parameters will be replaced with the given `numericTpe` and generic values with `numericExprCtor`
  // (provided it succeeds by returning `Some`).
  case class TyParamSubst(numericTpe: Type, numericExprCtor: BigInt => Option[Expr])

  enum RemappedCtex {
    case Success(args: Seq[Expr], tparams: Seq[Type])
    case Failure(reason: FailureReason)
  }
  enum FailureReason {
    case NonUniqueParams(name: String, vds: Seq[ValDef])
    case NonUniqueCtexVars(name: String, vds: Seq[ValDef])
    case NonUniqueTypeParams(name: String, vds: Seq[TypeParameterDef])
    case UnmappedCtexVars(vds: Seq[ValDef])
    case ExprRewrite(exprs: Seq[Expr])
    case NoSimpleValue(tpes: Seq[Type])
  }

  def tryRemapCtex(params: Seq[ValDef], tparams: Seq[TypeParameterDef], p: StainlessProgram)
                  (ctex: Map[p.trees.ValDef, p.trees.Expr])
                  (using tyParamSubst: TyParamSubst, ctx: inox.Context): RemappedCtex = {
    // First, ensure that the vds in `params` and `vars` are uniquely identifiable by their string name
    // (note that we cannot use the Identifiers because they are generally not the same due to freshening)
    val paramsName2Vds = params.groupBy(_.id.name)
    paramsName2Vds.find(_._2.size > 1) match {
      case Some((name, vds)) =>
        return RemappedCtex.Failure(FailureReason.NonUniqueParams(name, vds))
      case None => ()
    }
    val ctexName2Vds = ctex.keySet.groupBy(_.id.name)
    ctexName2Vds.find(_._2.size > 1) match {
      case Some((name, vds)) =>
        return RemappedCtex.Failure(FailureReason.NonUniqueCtexVars(name, vds.toSeq.map(prog2self(p)(_))))
      case None => ()
    }
    // Do the same for tparams
    val tparamsNames2Tpds = tparams.groupBy(_.id.name)
    tparamsNames2Tpds.find(_._2.size > 1) match {
      case Some((name, tpds)) =>
        return RemappedCtex.Failure(FailureReason.NonUniqueTypeParams(name, tpds))
      case None => ()
    }

    val ctexName2Vd = ctexName2Vds.view.mapValues(_.head).toMap
    val paramsName2Vd = paramsName2Vds.view.mapValues(_.head).toMap

    val extra = ctexName2Vd.keySet -- paramsName2Vd.keySet
    if (extra.nonEmpty) {
      // Extra variables in the counter-examples, we do not know what they correspond to
      return RemappedCtex.Failure(FailureReason.UnmappedCtexVars(extra.toSeq.map(e => prog2self(p)(ctexName2Vd(e)))))
    }

    // It may be the case that the ctex does not contain values for all params, in which case we will try to find a default value
    val missing = paramsName2Vd.keySet -- ctexName2Vd.keySet
    val (noSimpleVals, simpleVals0) = missing.partitionMap { m =>
      val vd = paramsName2Vd(m)
      val tpe = substTypeParams(tparams, vd.tpe)
      tryFindDefaultValue(p, tpe).map(m -> _).toRight(tpe)
    }
    if (noSimpleVals.nonEmpty) {
      return RemappedCtex.Failure(FailureReason.NoSimpleValue(noSimpleVals.toSeq))
    }
    val simpleVals = simpleVals0.toMap
    val (notRewrittenss, rewritten0) = ctex.toSeq.partitionMap { case (vd, e) =>
      tryRewriteExpr(tparams, prog2self(p)(e)).map(vd.id.name -> _)
    }
    if (notRewrittenss.nonEmpty) {
      return RemappedCtex.Failure(FailureReason.ExprRewrite(notRewrittenss.flatten))
    }
    val rewritten = rewritten0.toMap
    assert(rewritten.keySet.intersect(simpleVals.keySet).isEmpty)
    val allUnord = rewritten ++ simpleVals
    assert(allUnord.keySet == paramsName2Vd.keySet)
    val allOrd = params.map(vd => allUnord(vd.id.name))
    val newTparams = tparams.map(_ => tyParamSubst.numericTpe)
    RemappedCtex.Success(allOrd, newTparams)
  }

  def tryRewriteExpr(tparams: Seq[TypeParameterDef], expr: Expr)(using tyParamSubst: TyParamSubst): Either[Seq[Expr], Expr] = {
    if (tparams.isEmpty) Right(expr)
    else {
      val subst = new SubstTypeParamsAndGenericValues(tparams)
      val newExpr = subst.transform(expr)
      if (subst.failures.isEmpty) Right(newExpr)
      else Left(subst.failures)
    }
  }

  def substTypeParams(tparams: Seq[TypeParameterDef], tpe: Type)(using tyParamSubst: TyParamSubst): Type = {
    if (tparams.isEmpty) tpe
    else {
      val subst = new SubstTypeParamsAndGenericValues(tparams)
      val newTpe = subst.transform(tpe)
      assert(subst.failures.isEmpty, "failures are impossible when substituting for types (only for Expr)")
      newTpe
    }
  }

  // Note: assumes that `tpe` has already been rewritten to not contain generic values
  def tryFindDefaultValue(p: StainlessProgram, tpe: Type)(using inox.Context): Option[Expr] = {
    try {
      val dlft = p.symbols.simplestValue(self2prog(p, tpe), allowSolver = false)(using p.getSemantics)
      Some(prog2self(p)(dlft))
    } catch {
      case _: p.symbols.NoSimpleValue => None
    }
  }

  def self2prog(pr: StainlessProgram, e: Expr): pr.trees.Expr = {
    class Impl(override val s: self.trees.type, override val t: pr.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    new Impl(trees, pr.trees).transform(e)
  }

  def self2prog(pr: StainlessProgram, tpe: Type): pr.trees.Type = {
    class Impl(override val s: self.trees.type, override val t: pr.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    new Impl(trees, pr.trees).transform(tpe)
  }

  def prog2self(pr: StainlessProgram)(tpe: pr.trees.Type): Type = {
    class Impl(override val s: pr.trees.type, override val t: self.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    new Impl(pr.trees, trees).transform(tpe)
  }

  def prog2self(pr: StainlessProgram)(tpd: pr.trees.TypeParameterDef): TypeParameterDef = {
    class Impl(override val s: pr.trees.type, override val t: self.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    new Impl(pr.trees, trees).transform(tpd)
  }

  def prog2self(pr: StainlessProgram)(vd: pr.trees.ValDef): ValDef = {
    class Impl(override val s: pr.trees.type, override val t: self.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    new Impl(pr.trees, trees).transform(vd)
  }

  def prog2self(pr: StainlessProgram)(e: pr.trees.Expr): Expr = {
    class Impl(override val s: pr.trees.type, override val t: self.trees.type) extends transformers.ConcreteTreeTransformer(s, t)
    new Impl(pr.trees, trees).transform(e)
  }

  private class SubstTypeParamsAndGenericValues(tparams: Seq[TypeParameterDef])(using tyParamSubst: TyParamSubst) extends ConcreteSelfTreeTransformer {
    var failures: List[Expr] = Nil

    override def transform(tpe: Type): Type = tpe match {
      case tp: TypeParameter if tparams.exists(_.tp.id.name == tp.id.name) => tyParamSubst.numericTpe
      case _ => super.transform(tpe)
    }

    override def transform(expr: Expr): Expr = expr match {
      case GenericValue(tp, id) =>
        val newExpr = tparams.zipWithIndex
          .find((tpDef, _) => tpDef.tp.id.name == tp.id.name)
          .flatMap { (_, tpIx) =>
            tyParamSubst.numericExprCtor(BigInt(id) * BigInt(tparams.size) + BigInt(tpIx))
          }
        newExpr match {
          case Some(e) => e
          case None =>
            failures = expr :: failures
            expr
        }
      case _ => super.transform(expr)
    }
  }

}
