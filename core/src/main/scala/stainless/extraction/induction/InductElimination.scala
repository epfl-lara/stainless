/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package induction

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
    if (fd.flags exists (_.name == "induct")) {
      context.reporter.fatalError(fd.getPos, "Annotation @induct is not supported on functions anymore, annotate the arguments on which you want to induct on instead")
    }

    implicit val syms = tcontext.symbols
    val inductionParams = fd.params.filter(vd => vd.flags.exists(_.name == "induct"))

    val (specs, oldBodyOpt) = deconstructSpecs(fd.fullBody)

    val inductionBody = oldBodyOpt.map(oldBody =>
      inductionParams.foldLeft(oldBody) { case (currentBody, vd) =>
        vd.getType match {
          case ADTType(id, tps) =>
            val sort = syms.getSort(id)
            MatchExpr(vd.toVariable, sort.constructors.map { cons =>
              val freshBinders = cons.fields.map(vd => vd.freshen)
              val rhs = freshBinders.foldLeft(currentBody) { (letBody, binder) =>
                val newParams = fd.params.map(param =>
                  if (param == vd) binder.toVariable
                  else param.toVariable
                )
                // FIXME: When fd.returnType is a dependent type, we must bind its
                // variables with newParams
                Let(ValDef.fresh("inductVal", fd.returnType), FunctionInvocation(fd.id, fd.tparams.map(_.tp), newParams), letBody)
              }
              MatchCase(
                ADTPattern(
                  None,
                  cons.id,
                  tps,
                  freshBinders.map(binder => WildcardPattern(Some(binder)))
                ),
                None,
                rhs
              )
            })
          case IntegerType() =>
            // FIXME: When fd.returnType is a dependent type, we must bind its
            // variables with newParams
            val inductionVd = ValDef.fresh("inductVal", fd.returnType)
            val newParams = fd.params.map(param =>
              if (param == vd) Minus(param.toVariable, IntegerLiteral(1))
              else param.toVariable
            )
            IfExpr(
              LessEquals(vd.toVariable, IntegerLiteral(0)),
              currentBody,
              Let(inductionVd, FunctionInvocation(fd.id, fd.tparams.map(_.tp), newParams), currentBody)
            )
          case BVType(sign, size) =>
            // FIXME: When fd.returnType is a dependent type, we must bind its
            // variables with newParams
            val inductionVd = ValDef.fresh("inductVal", fd.returnType)
            val newParams = fd.params.map(param =>
              if (param == vd) Minus(param.toVariable, BVLiteral(sign, size, 1))
              else param.toVariable
            )
            IfExpr(
              LessEquals(vd.toVariable, BVLiteral(sign, size, 0)),
              currentBody,
              Let(inductionVd, FunctionInvocation(fd.id, fd.tparams.map(_.tp), newParams), currentBody)
            )
          case tpe =>
            context.reporter.fatalError(vd.getPos, s"Induction on type ${tpe.asString} is not supported")
        }
      }
    )

    val newBody = reconstructSpecs(specs, inductionBody, fd.returnType)

    new FunDef(
      fd.id,
      fd.tparams,
      fd.params,
      // FIXME: fd.params should be fd.params.map(vd => vd.copy(flags = vd.flags.filterNot(_.name == "induct")).copiedFrom(vd)),
      // but that creates an well-formedness exception
      fd.returnType,
      newBody,
      fd.flags
    )
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
