package stainless
package testgen

import stainless.ast.SymbolIdentifier
import stainless.extraction.xlang.trees as xt
import stainless.verification.*

object XLangTestGen {
  import stainless.trees._

  case class TyParamSubst(numericTpe: Type, numericExprCtor: BigInt => Option[Expr])

  case class TestCaseCtx(origSyms: xt.Symbols,
                         p: inox.Program {val trees: stainless.trees.type},
                         vc: VC[stainless.trees.type])
                        // For some reasons, this needs to be put as val, otherwise it is inaccessible...
                        (val cex: p.Model) {
    // We override hashCode and equals because, for some reasons, the synthesized methods do not use `cex`

    override def canEqual(that: Any): Boolean = that.isInstanceOf[TestCaseCtx]

    override def equals(other: Any): Boolean = other match {
      case that: TestCaseCtx => p == that.p && vc == that.vc && cex == that.cex
      case _ => false
    }

    override def hashCode(): Int = java.util.Objects.hash(p, vc, cex)
  }

  case class FaultyFd(fd: FunDef)

  /////////////////////////////////////////////////////////////////////////////////////////////////

  // TODO: If a falsified VC is reported for the following
  //  -local fns
  //  -local classes
  //  -loops
  //  then the translation is a bit too naive (we need to call the "enclosing" function of the faulty fn,
  //  not the faulty fn as it is inaccessible from outside)

  def generateTestCase(testCaseNbr: Int)(using tyParamSubst: TyParamSubst, tcCtx: TestCaseCtx, ctx: inox.Context): Option[(xt.FunDef, xt.FunDef)] = {
    import tcCtx._

    if (cex.chooses.nonEmpty) {
      recognizeFailure("due to the presence of 'chooses' in the model")
      return None
    }

    val faultyFd: FunDef = {
      try p.symbols.getFunction(vc.fid)
      catch {
        case _: FunctionLookupException =>
          recognizeFailure(s"due to the inability of recovering the function definition of ${vc.fid}")
          return None
      }
    }
    given FaultyFd = FaultyFd(faultyFd)

    if ((cex.vars.keys ++ faultyFd.params).exists(vd => vd.tpe match {
      case PiType(_, _) => true
      case _ => false
    })) {
      recognizeFailure("due to the presence of dependant-types")
      return None
    }

    val vdMapping: Map[ValDef, (ValDef, Int)] = cex.vars.keySet.flatMap(cexVd =>
      faultyFd.params.zipWithIndex.find(_._1.id.name == cexVd.id.name).map(fnVd => cexVd -> fnVd)).toMap
    if (vdMapping.size != cex.vars.size) {
      recognizeFailure(s"due to the inability of reconciling the variables of the model and the parameters of ${vc.fid}")
      return None
    }
    if (vdMapping.keys.size != cex.vars.size) {
      recognizeFailure(s"due to name collision with the parameters of ${vc.fid}")
      return None
    }

    val missingMapping: Set[(ValDef, Int)] = faultyFd.params.zipWithIndex.toSet -- vdMapping.values.toSet
    val (defaultArgsErrs, defaultArgs) = missingMapping.toSeq.partitionMap {
      case (fnVd, pos) =>
        val expr = tryFindDefaultValue(substTypeParams(fnVd.tpe))
        expr.map(e => pos -> e)
    }
    if (defaultArgsErrs.nonEmpty) {
      recognizeFailure(
        s"""due to:
           |${defaultArgsErrs.flatten.mkString("  - ", "\n", "")}""".stripMargin)
      return None
    }

    val (cexArgsErr, cexArgs) = cex.vars.toSeq.partitionMap {
      case (cexVd, expr) =>
        val pos = vdMapping(cexVd)._2
        val rewrittenExpr = tryRewriteExpr(expr)
        rewrittenExpr.map(e => pos -> e)
    }
    if (cexArgsErr.nonEmpty) {
      recognizeFailure(
        s"""due to:
           |${cexArgsErr.flatten.mkString("  - ", "\n", "")}""".stripMargin)
      return None
    }
    val args = (defaultArgs ++ cexArgs).sortBy(_._1).map(_._2)

    val testCaseBody = FunctionInvocation(vc.fid, faultyFd.tparams.map(_ => IntegerType()), args)
    val testCaseId = SymbolIdentifier(s"testCase$testCaseNbr")
    val testCaseFd = FunDef(testCaseId, Seq.empty, Seq.empty, UnitType(), testCaseBody, Seq.empty)

    val adtToClass = new AdtToClass(origSyms)
    val xtFaultyFdNoBody = adtToClass.transform(unlowering.transform(faultyFd.copy(fullBody = NoTree(faultyFd.returnType))))
    val xtTestCaseFd = adtToClass.transform(unlowering.transform(testCaseFd))
    if (adtToClass.failures.nonEmpty) {
      val msgs = adtToClass.failures.map(adtTpe => s"  - the inability of rewriting $adtTpe into a class").mkString("\n")
      recognizeFailure(
        s"""due to:
           |$msgs""".stripMargin)
      return None
    }
    Some((xtFaultyFdNoBody, xtTestCaseFd))
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////

  def recognizeFailure(msg: String)(using tcCtx: TestCaseCtx, ctx: inox.Context): Unit = {
    ctx.reporter.warning(tcCtx.vc.getPos,
      s"""Could not generate a test case from the following counter-example:
         |  ${tcCtx.cex.asString(using PrinterOptions()).replaceAll("\n", "\n  ")}
         |$msg""".stripMargin)
  }

  def tryFindDefaultValue(tpe: Type)(using faultyFd: FaultyFd, tcCtx: TestCaseCtx, tps: TyParamSubst, ctx: inox.Context): Either[List[String], Expr] = {
    try {
      tryRewriteExpr(tcCtx.p.symbols.simplestValue(tpe, allowSolver = false)(using tcCtx.p.getSemantics))
    } catch {
      case _: tcCtx.p.symbols.NoSimpleValue => Left(s"the inability of finding a default value for $tpe" :: Nil)
    }
  }

  def substTypeParams(tpe: Type)(using faultyFd: FaultyFd, tps: TyParamSubst): Type = {
    val subst = new SubstTypeParamsAndGenericValues(faultyFd.fd.tparams)
    val newTpe = subst.transform(tpe)
    assert(subst.failures.isEmpty, "failures are impossible when substituting for types (only for Expr)")
    newTpe
  }

  def tryRewriteExpr(expr: Expr)(using faultyFd: FaultyFd, tps: TyParamSubst): Either[List[String], Expr] = {
    val subst = new SubstTypeParamsAndGenericValues(faultyFd.fd.tparams)
    val newExpr = subst.transform(expr)
    if (subst.failures.isEmpty) Right(newExpr)
    else Left(subst.failures.map(e => s"the inability of rewriting $e"))
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////

  private val unlowering = new UnloweringImpl(trees, xt)

  private class UnloweringImpl(override val s: trees.type, override val t: xt.type)
    extends transformers.ConcreteTreeTransformer(s, t)


  private class AdtToClass(val origSyms: xt.Symbols) extends xt.ConcreteOOSelfTreeTransformer {
    var failures: List[xt.ADTType] = Nil

    override def transform(tpe: xt.Type): xt.Type = tpe match {
      case adtTpe: xt.ADTType =>
        adtTypeToClassType(adtTpe) match {
          case Some(ct) => ct
          case None =>
            failures = adtTpe :: failures
            adtTpe
        }
      case _ => super.transform(tpe)
    }

    override def transform(e: xt.Expr): xt.Expr = e match {
      case adt@xt.ADT(id, tps, args) =>
        val adtTpe = xt.ADTType(id, tps)
        adtTypeToClassType(adtTpe) match {
          case Some(ct) => xt.ClassConstructor(ct, args.map(transform))
          case None =>
            failures = adtTpe :: failures
            adt
        }
      case _ => super.transform(e)
    }

    def adtTypeToClassType(adtType: xt.ADTType): Option[xt.ClassType] = {
      origSyms.classes.find(_._1.name == adtType.id.name)
        .map((clsId, _) => xt.ClassType(clsId, adtType.tps.map(transform)))
    }
  }

  private class SubstTypeParamsAndGenericValues(tparams: Seq[TypeParameterDef])
                                               (using tyParamSubst: TyParamSubst) extends ConcreteSelfTreeTransformer {
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