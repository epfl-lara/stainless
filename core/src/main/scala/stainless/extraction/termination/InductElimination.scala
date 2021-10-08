/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package termination

class InductElimination(override val s: Trees)(override val t: s.type)
                       (using override val context: inox.Context)
  extends CachingPhase
     with SimpleFunctions
     with SimplyCachedFunctions
     with IdentitySorts { self =>

  /* ====================================
   *       Context and caches setup
   * ==================================== */

  import s._
  import s.exprOps._
  import dsl._

  protected class TransformerContext(using val symbols: Symbols)
  override protected def getContext(syms: Symbols) = new TransformerContext()(using syms)

  override protected def extractFunction(tcontext: TransformerContext, fd: FunDef): FunDef = {
    val syms = tcontext.symbols
    import syms.given

    def canInductOn(tpe: Type): Boolean = tpe match {
      case ADTType(_, _) => true
      case IntegerType() => true
      case BVType(_, _)  => true
      case _             => false
    }

    // @induct on the function refers to induction on the first parameter for which `canInductOn` returns true
    val firstInductionParam =
      if (fd.flags.contains(Induct)) {
        fd.params.find(vd => canInductOn(vd.getType)) match {
          case Some(vd) => Seq(vd)
          case None =>
            context.reporter.fatalError(
              fd.getPos,
              s"In ${fd.id.asString}, could not find an argument on which to do induction"
            )
        }
      } else {
        Seq()
      }

    val inductionParams =
      firstInductionParam ++
        fd.params.filter { vd =>
          !firstInductionParam.contains(vd) && vd.flags.contains(Induct)
        }

    if (inductionParams.isEmpty) {
      return fd
    }

    // TODO: Decide what we want to do with multiple inductions and implement it
    if (inductionParams.size > 1) {
      context.reporter
        .fatalError(fd.getPos, s"In ${fd.id.asString}, induction on multiple parameters is not supported")
    }

    var specced = BodyWithSpecs(fd.fullBody)

    if (!inductionParams.isEmpty)
      specced.specs.foreach {
        case Measure(_) =>
          context.reporter.warning(
            fd.getPos,
            s"Ignoring decreases clause of ${fd.id.asString}. The @induct annotation automatically inserts a decreases clause corresponding to the argument"
          )
        case _ => ()
      }

    val inductionBodyOpt = specced.bodyOpt.map(oldBody =>
      inductionParams.foldRight(oldBody) {
        case (vd, currentBody) =>
          vd.getType match {
            case ADTType(id, tps) =>
              val sort = syms.getSort(id)
              MatchExpr(
                vd.toVariable,
                sort.typed(tps).constructors.map {
                  cons =>
                    val freshBinders = cons.fields.map(vd => vd.freshen.setPos(oldBody))
                    val recursionBinders = freshBinders.filter(binder => binder.getType == vd.getType)
                    val rhs = recursionBinders.foldLeft(currentBody) {
                      (letBody, binder) =>
                        val newParams = fd.params.map(param =>
                          if (param == vd) binder.toVariable
                          else param.toVariable
                        )
                        // FIXME: When fd.returnType is a dependent type, we must bind its variables with newParams
                        Let(
                          ValDef.fresh("inductVal", fd.returnType).setPos(oldBody),
                          FunctionInvocation(fd.id, fd.tparams.map(_.tp), newParams).setPos(oldBody),
                          letBody
                        ).setPos(oldBody)
                    }
                    MatchCase(
                      ADTPattern(
                        None,
                        cons.id,
                        tps,
                        freshBinders.map(binder => WildcardPattern(Some(binder)).setPos(oldBody))
                      ).setPos(oldBody),
                      None,
                      rhs
                    ).setPos(oldBody)
                }
              ).setPos(oldBody)

            case IntegerType() =>
              // FIXME: When fd.returnType is a dependent type, we must bind its variables with newParams
              val inductionVd = ValDef.fresh("inductVal", fd.returnType).setPos(oldBody)
              val newParams = fd.params.map(param =>
                if (param == vd) Minus(param.toVariable, IntegerLiteral(1)).setPos(oldBody)
                else param.toVariable
              )
              IfExpr(
                LessEquals(vd.toVariable, IntegerLiteral(0).setPos(oldBody)).setPos(oldBody),
                currentBody,
                Let(
                  inductionVd,
                  FunctionInvocation(fd.id, fd.tparams.map(_.tp), newParams).setPos(oldBody),
                  currentBody
                ).setPos(oldBody)
              ).setPos(oldBody)

            case BVType(sign, size) =>
              // FIXME: When fd.returnType is a dependent type, we must bind its variables with newParams
              val inductionVd = ValDef.fresh("inductVal", fd.returnType)
              val newParams = fd.params.map { param =>
                if (param == vd) Minus(param.toVariable, BVLiteral(sign, 1, size))
                else param.toVariable
              }
              IfExpr(
                LessEquals(vd.toVariable, BVLiteral(sign, 0, size).setPos(oldBody)).setPos(oldBody),
                currentBody,
                Let(
                  inductionVd,
                  FunctionInvocation(fd.id, fd.tparams.map(_.tp), newParams).setPos(oldBody),
                  currentBody
                ).setPos(oldBody)
              )

            case tpe =>
              context.reporter.fatalError(vd.getPos, s"Induction on type ${tpe.asString} is not supported")
          }
      }
    )

    // TODO(gsps): Clean all this up (inductionParams is never empty!)

    val newMeasure: Option[Specification] =
      if (inductionParams.isEmpty) None
      else if (inductionParams.size == 1) Some(Measure((inductionParams.head.toVariable)))
      else Some(Measure(Tuple(inductionParams.map(_.toVariable))))

    val newSpecced =
      if (inductionParams.isEmpty || newMeasure.isEmpty) specced
      else specced.withSpec(newMeasure.get)

    val newBody1 = newSpecced.withBody(inductionBodyOpt, fd.returnType).reconstructed

    // Remove @induct flag from parameters and replace those in the body to ensure well-formedness.
    val newParams = fd.params.map(vd => vd.copy(flags = vd.flags.filterNot(_ == Induct)).copiedFrom(vd))
    val newBody2 = exprOps.replaceFromSymbols(fd.params.zip(newParams.map(_.toVariable)).toMap, newBody1)

    new FunDef(
      fd.id,
      fd.tparams,
      newParams,
      fd.returnType,
      newBody2,
      fd.flags.filterNot(_ == Induct),
    ).setPos(fd)
  }
}

object InductElimination {
  def apply(tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = {
    class Impl(override val s: tt.type, override val t: tt.type) extends InductElimination(s)(t)
    new Impl(tt, tt)
  }
}
