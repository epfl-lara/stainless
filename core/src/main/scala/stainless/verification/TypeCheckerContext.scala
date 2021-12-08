/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification
import trees._

import TypeCheckerUtils._

object TypeCheckerContext {
  val letWitness = "__letWitness"

  case class TypingContext(
    depth: Int,
    visibleFunctions: Set[Identifier],
    visibleADTs: Set[Identifier],
    typeVariables: Set[TypeParameter],
    termVariables: Seq[Variable],
    currentFid: Option[Identifier],
    currentADT: Option[Identifier],
    currentMeasure: Option[Expr],
    measureType: Option[Type],
    vcKind: VCKind,
    checkSAT: Boolean,
    emitVCs: Boolean,
  ) extends inox.utils.Positioned {

    def inc() = {
      copy(depth = depth + 1).setPos(this)
    }

    def checkFreshTermVariable(vd: ValDef)(using opts: PrinterOptions, ctx: inox.Context) = {
      if (termVariables.contains(vd.toVariable))
        ctx.reporter.internalError(s"Typing context already contains variable ${vd.id.asString}")
    }

    def checkFreshTermVariables(vds: Seq[ValDef])(using opts: PrinterOptions, ctx: inox.Context) = {
      vds.foreach(checkFreshTermVariable)
    }

    def checkFreshTypeVariable(tp: TypeParameter)(using opts: PrinterOptions, ctx: inox.Context) = {
      if (termVariables.contains(tp))
        ctx.reporter.internalError(s"Typing context already contains type variable ${tp.asString}")
    }

    def checkFreshTypeVariables(tps: Iterable[TypeParameter])(using opts: PrinterOptions, ctx: inox.Context) = {
      tps.foreach(checkFreshTypeVariable)
    }

    def bindWithValue(vd: ValDef, e: Expr)(using opts: PrinterOptions, ctx: inox.Context): TypingContext = {
      checkFreshTermVariable(vd)
      copy(termVariables = termVariables :+ vd.toVariable :+ Variable.fresh(letWitness, LetEquality(vd.toVariable,e))).setPos(this)
    }

    def bindWithValues(vds: Seq[ValDef], es: Seq[Expr])(using opts: PrinterOptions, ctx: inox.Context) = {
      checkFreshTermVariables(vds)
      vds.zip(es).foldLeft(this){
        case(tcAcc, (vd,e)) => tcAcc.bindWithValue(vd, e)
      }
    }

    def freshBindWithValue(vd: ValDef, e: Expr)(using opts: PrinterOptions, ctx: inox.Context): (TypingContext, Identifier) = {
      val freshVd = vd.freshen
      (
        copy(termVariables = termVariables :+ freshVd.toVariable :+ Variable.fresh(letWitness, LetEquality(freshVd.toVariable,e))).setPos(this),
        freshVd.id
      )
    }

    def freshBindWithValues(vds: Seq[ValDef], es: Seq[Expr])(using opts: PrinterOptions, ctx: inox.Context): (TypingContext, Substituter) = {
      if (vds.size != es.size)
        ctx.reporter.internalError("Function `freshBindWithValues` expects sequences with the same size")
      vds.zip(es).foldLeft((this, new Substituter(Map()))) {
        case ((tcAcc, freshener), (vd, e)) =>
          val (newTc, newId) = tcAcc.freshBindWithValue(freshener.transform(vd), freshener.transform(e))
          if (freshener.contains(vd.id)) {
            ctx.reporter.internalError(s"Substitution should not contain ${vd.id.asString}")
          }
          (newTc, freshener.enrich(vd.id, newId))
      }
    }

    def withTruth(cond: Expr) = {
      copy(termVariables = termVariables :+ Variable.fresh("__truthWitness", Truth(cond))).setPos(this)
    }

    def bind(vd: ValDef)(using opts: PrinterOptions, ctx: inox.Context): TypingContext = {
      checkFreshTermVariable(vd)
      copy(termVariables = termVariables :+ vd.toVariable).setPos(this)
    }

    def bind(vds: Seq[ValDef])(using opts: PrinterOptions, ctx: inox.Context): TypingContext = {
      checkFreshTermVariables(vds)
      copy(termVariables = termVariables ++ vds.map(_.toVariable)).setPos(this)
    }

    def freshBind(vd: ValDef)(using opts: PrinterOptions, ctx: inox.Context): (TypingContext, Identifier) = {
      val freshVd = vd.freshen
      (
        copy(termVariables = termVariables :+ freshVd.toVariable).setPos(this),
        freshVd.id
      )
    }

    def withTypeVariables(vars: Set[TypeParameter])(using opts: PrinterOptions, ctx: inox.Context): TypingContext = {
      checkFreshTypeVariables(vars)
      copy(typeVariables = typeVariables ++ vars).setPos(this)
    }

    def withIdentifiers(ids: Set[Identifier])(using s: Symbols) = {
      val (fids, sorts) = ids.partition(id => s.lookupFunction(id).isDefined)
      copy(
        visibleFunctions = visibleFunctions ++ fids,
        visibleADTs = visibleADTs ++ sorts
      ).setPos(this)
    }

    def inFunction(id: Identifier) = {
      copy(currentFid = Some(id)).setPos(this)
    }

    def inADT(id: Identifier) = {
      copy(currentADT = Some(id)).setPos(this)
    }

    def withMeasureType(t: Option[Type]) = {
      copy(measureType = t).setPos(this)
    }

    def withMeasure(m: Option[Expr]) = {
      copy(currentMeasure = m).setPos(this)
    }

    def withVCKind(kind: VCKind) = {
      copy(vcKind = kind).setPos(this)
    }

    def withCheckSAT(checkSAT: Boolean) = {
      copy(checkSAT = checkSAT).setPos(this)
    }

    def withEmitVCs(emitVCs: Boolean) = {
      copy(emitVCs = emitVCs).setPos(this)
    }

    def indent: String = "  " * depth

    def asString(indent: String = "")(using PrinterOptions) = {
      (if (indent != "") s"${indent}Depth: $depth\n" else "") +
      s"""|${indent}Kind: ${vcKind}
          |${indent}Check SAT: ${checkSAT}
          |${indent}Emit VCs: ${emitVCs}
          |${indent}Functions: ${visibleFunctions.map(_.asString).mkString(", ")}
          |${indent}ADTs: ${visibleADTs.map(_.asString).mkString(", ")}
          |${indent}Type Variables: ${typeVariables.map(_.asString).mkString(", ")}
          |${indent}Term Variables:\n${indent}${termVariables.map(v => "  " + pp(v)).mkString("\n" + indent)}
          |""".stripMargin
    }
  }

  object TypingContext {
    def empty = TypingContext(
      depth = 0,
      visibleFunctions = Set(),
      visibleADTs = Set(),
      typeVariables = Set(),
      termVariables = Seq(),
      currentFid = None,
      currentADT = None,
      currentMeasure = None,
      measureType = None,
      vcKind = VCKind.CheckType,
      checkSAT = false,
      emitVCs = true,
    )
  }
}
