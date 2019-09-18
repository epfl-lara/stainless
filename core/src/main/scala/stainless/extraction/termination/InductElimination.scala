/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package termination

trait InductElimination extends CachingPhase
  with SimpleFunctions
  with SimplyCachedFunctions
  with IdentitySorts
  { self =>
  val s: Trees
  val t: s.type

  /* ====================================
   *       Context and caches setup
   * ==================================== */

  import s._
  import s.exprOps._
  import dsl._

  protected class TransformerContext(implicit val symbols: Symbols)
  override protected def getContext(syms: Symbols) = new TransformerContext()(syms)

  override protected def extractFunction(tcontext: TransformerContext, fd: FunDef): FunDef = {
    implicit val syms = tcontext.symbols

    def canInductOn(tpe: Type): Boolean = tpe match {
      case ADTType(_, _) => true
      case IntegerType() => true
      case BVType(_, _) => true
      case _ => false
    }

    // @induct on the function refers to induction on the first parameter for which `canInductOn` returns true
    val firstInductionParam =
      if (fd.flags.exists(_.name == "induct")) {
        fd.params.find(vd => canInductOn(vd.getType)) match {
          case Some(vd) => Seq(vd)
          case None => context.reporter.fatalError(fd.getPos, s"In ${fd.id.asString}, could not find an argument on which to do induction")
        }
      } else {
        Seq()
      }

    val inductionParams =
      firstInductionParam ++
      fd.params.filter { vd =>
        !firstInductionParam.contains(vd) && vd.flags.exists(_.name == "induct")
      }

    if (inductionParams.isEmpty) {
      return fd
    }

    // TODO: Decide what we want to do with multiple inductions and implement it
    if (inductionParams.size > 1) {
      context.reporter.fatalError(fd.getPos, s"In ${fd.id.asString}, induction on multiple parameters is not supported")
    }

    val (specs, oldBodyOpt) = deconstructSpecs(fd.fullBody)

    if (!inductionParams.isEmpty)
      specs.foreach {
        case Measure(_) =>
          context.reporter.warning(fd.getPos, s"Ignoring decreases clause of ${fd.id.asString}. The @induct annotation automatically inserts a decreases clause corresponding to the argument")
        case _ => ()
      }

    val inductionBody = oldBodyOpt.map(oldBody =>
      inductionParams.foldRight(oldBody) { case (vd, currentBody) =>
        vd.getType match {
          case ADTType(id, tps) =>
            val sort = syms.getSort(id)
            MatchExpr(vd.toVariable, sort.typed(tps).constructors.map { cons =>
              val freshBinders = cons.fields.map(vd => vd.freshen.setPos(oldBody))
              val recursionBinders = freshBinders.filter(binder =>
                binder.getType == vd.getType
              )
              val rhs = recursionBinders.foldLeft(currentBody) { (letBody, binder) =>
                val newParams = fd.params.map(param =>
                  if (param == vd) binder.toVariable
                  else param.toVariable
                )
                // FIXME: When fd.returnType is a dependent type, we must bind its
                // variables with newParams
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
            }).setPos(oldBody)
          case IntegerType() =>
            // FIXME: When fd.returnType is a dependent type, we must bind its
            // variables with newParams
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
            // FIXME: When fd.returnType is a dependent type, we must bind its
            // variables with newParams
            val inductionVd = ValDef.fresh("inductVal", fd.returnType)
            val newParams = fd.params.map(param =>
              if (param == vd) Minus(param.toVariable, BVLiteral(sign, size, 1))
              else param.toVariable
            )
            IfExpr(
              LessEquals(vd.toVariable, BVLiteral(sign, size, 0).setPos(oldBody)).setPos(oldBody),
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

    val newMeasure: Option[Specification] =
      if (inductionParams.isEmpty) None
      else if (inductionParams.size == 1) Some(Measure((inductionParams.head.toVariable)))
      else Some(Measure(Tuple(inductionParams.map(_.toVariable))))

    val typeCheckerEnabled = context.options.findOptionOrDefault(verification.optTypeChecker)
    val newSpecs =
      if (inductionParams.isEmpty || !typeCheckerEnabled) specs
      else specs.filterNot(_.isInstanceOf[Measure]) ++ newMeasure

    val newBody = reconstructSpecs(newSpecs, inductionBody, fd.returnType)

    new FunDef(
      fd.id,
      fd.tparams,
      fd.params,
      // FIXME: fd.params should be
      //        `fd.params.map(vd => vd.copy(flags = vd.flags.filterNot(_.name == "induct")).copiedFrom(vd))`,
      //         but that creates a well-formedness exception
      fd.returnType,
      newBody,
      fd.flags
    ).setPos(fd)
  }
}

object InductElimination {
  def apply(tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = new InductElimination {
    override val s: tt.type = tt
    override val t: tt.type = tt
    override val context = ctx
  }
}
