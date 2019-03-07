/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

import scala.language.existentials

trait ContractLifting
  extends oo.SimplePhase
     with SimplyCachedFunctions
     with SimplyCachedSorts
     with oo.IdentityTypeDefs
     with oo.SimplyCachedClasses { self =>

  val s: Trees
  val t: self.s.type
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(symbols: s.Symbols) extends oo.TreeTransformer {
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    import exprOps.{Precondition, Postcondition}

    private def hasContracts(fd: FunDef): Boolean =
      exprOps.preconditionOf(fd.fullBody).isDefined ||
      exprOps.postconditionOf(fd.fullBody).isDefined

    private def hasPrecondition: Set[Identifier] =
      symbols.functions.values
        .filter(fd => exprOps.preconditionOf(fd.fullBody).isDefined)
        .map(_.id)
        .toSet

    private def hasPostcondition: Set[Identifier] =
      symbols.functions.values
        .filter(fd => exprOps.postconditionOf(fd.fullBody).isDefined)
        .map(_.id)
        .toSet

    private def toLift: Set[Identifier] = hasPrecondition ++ hasPostcondition

    private val transformer = new SelfTreeTransformer {
      override def transform(expr: Expr): Expr = expr match {
        case fi: FunctionInvocation if hasPrecondition(fi.id) =>
          super.transform(fi.copy(args = fi.args :+ UnitLiteral().copiedFrom(fi)))

        case mi: MethodInvocation if hasPrecondition(mi.id) =>
          super.transform(mi.copy(args = mi.args :+ UnitLiteral().copiedFrom(mi)))

        case a @ StaticAssert(pred, err, body) => // TODO: What to do with error message?
          val tpe = RefinementType(ValDef.fresh("_", UnitType()), super.transform(pred))
          val vd = ValDef.fresh("assert", tpe)
          Let(vd, UnitLiteral().copiedFrom(a), super.transform(body)).copiedFrom(a)

        case a @ Assert(pred, err, body) =>
          IfExpr(pred,
            body,
            Error(body.getType(symbols), err.getOrElse("assertion failed")).copiedFrom(body)
          ).copiedFrom(a)

        case _ => super.transform(expr)
      }
    }

    private def liftContracts(fd: FunDef): FunDef = {
      val pre = exprOps.preconditionOf(fd.fullBody)
      val post = exprOps.postconditionOf(fd.fullBody)

      val returnType = addPostcondition(fd.returnType, post)

      val proofParam = pre map { pre =>
        val proofType = RefinementType(ValDef.fresh("_", UnitType()), pre.expr).copiedFrom(pre.expr)
        ValDef.fresh("pre", proofType)
      }

      val lifted = fd.copy(
        params = fd.params ++ proofParam.toSeq,
        returnType = returnType,
        fullBody = exprOps.withoutSpecs(fd.fullBody).getOrElse(fd.fullBody),
      ).copiedFrom(fd)

      transformer.transform(lifted)
    }

    private def addPostcondition(returnType: Type, post: Option[Postcondition]): Type = returnType match {
      case RefinementType(vd, pred) =>
        val newPred = post.map { case Postcondition(post, isStatic) =>
          And(pred, post.withParamSubst(Seq(vd.toVariable), post.body))
        }.getOrElse(pred)
        RefinementType(vd, newPred)

      case tpe => post.map { case Postcondition(post, isStatic) =>
        val vd = ValDef.fresh("res", tpe)
        RefinementType(vd, post.withParamSubst(Seq(vd.toVariable), post.body))
      }.getOrElse(tpe)
    }

    override def transform(fd: FunDef): FunDef = {
      if (toLift(fd.id)) liftContracts(fd)
      else transformer.transform(fd)
    }
  }
}

object ContractLifting {
  def apply(trees: xlang.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new ContractLifting {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
