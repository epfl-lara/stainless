package stainless
package testgen

import stainless.ast.SymbolIdentifier
import stainless.extraction.xlang.{trees => xt}
import stainless.verification._

object XLangTestGen extends utils.CtexRemapping {
  override val trees: stainless.trees.type = stainless.trees
  import trees._

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

    val (args, newTparams) = tryRemapCtex(faultyFd.params, faultyFd.tparams, tcCtx.p)(tcCtx.cex.vars) match {
      case RemappedCtex.Success(args, newTparams) => (args, newTparams)
      case RemappedCtex.Failure(FailureReason.NonUniqueParams(name, vds)) =>
        recognizeFailure(s"due to name collision with the parameters of ${faultyFd.id.name}: $name has multiple correspondances $vds")
        return None
      case RemappedCtex.Failure(FailureReason.NonUniqueCtexVars(name, vds)) =>
        recognizeFailure(s"due to name collision with the variables of the counter-examples: $name has multiple correspondances $vds")
        return None
      case RemappedCtex.Failure(FailureReason.NonUniqueTypeParams(name, tpds)) =>
        recognizeFailure(s"due to name collision with the type parameters of ${faultyFd.id.name}: $name has multiple correspondances $tpds")
        return None
      case RemappedCtex.Failure(FailureReason.UnmappedCtexVars(vds)) =>
        recognizeFailure(s"due to counter-example having extra unknown variables: $vds")
        return None
      case RemappedCtex.Failure(FailureReason.ExprRewrite(exprs)) =>
        recognizeFailure(s"the inability of rewriting ${exprs.mkString(", ")}")
        return None
      case RemappedCtex.Failure(FailureReason.NoSimpleValue(tps)) =>
        recognizeFailure(s"the inability of find a default values for ${tps.mkString(", ")}")
        return None
    }
    val testCaseBody = FunctionInvocation(vc.fid, newTparams, args)
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
}