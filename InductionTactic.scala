/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._
import purescala.Constructors._

class InductionTactic(vctx: VerificationContext) extends DefaultTactic(vctx) {
  override val description = "Induction tactic for suitable functions"

  val reporter = vctx.reporter

  private def firstAbsClassDef(args: Seq[ValDef]): Option[(AbstractClassType, ValDef)] = {
    args.map(vd => (vd.getType, vd)).collect {
      case (act: AbstractClassType, vd) => (act, vd)
    }.headOption
  }

  private def selectorsOfParentType(parentType: ClassType, cct: CaseClassType, expr: Expr): Seq[Expr] = {
    val childrenOfSameType = cct.fields.filter(_.getType == parentType)
    for (field <- childrenOfSameType) yield {
      caseClassSelector(cct, expr, field.id)
    }
  }

  override def generatePostconditions(fd: FunDef): Seq[VC] = {
    (fd.body, firstAbsClassDef(fd.params), fd.postcondition) match {
      case (Some(body), Some((parentType, arg)), Some(post)) =>
        for (cct <- parentType.knownCCDescendants) yield {
          val selectors = selectorsOfParentType(parentType, cct, arg.toVariable)

          val subCases = selectors.map { sel =>
            replace(Map(arg.toVariable -> sel),
              implies(precOrTrue(fd), application(post, Seq(body)))
            )
          }

          val vc = implies(
            and(IsInstanceOf(cct, arg.toVariable), precOrTrue(fd)),
            implies(andJoin(subCases), application(post, Seq(body)))
          )

          VC(vc, fd, VCKinds.Info(VCKinds.Postcondition, s"ind. on ${arg.asString} / ${cct.classDef.id.asString}")).setPos(fd)
        }

      case (body, _, post) =>
        if (post.isDefined && body.isDefined) {
          reporter.warning(fd.getPos, "Could not find abstract class type argument to induct on")
        }
        super.generatePostconditions(fd)
    }
  }

  override def generatePreconditions(fd: FunDef): Seq[VC] = {
    (fd.body, firstAbsClassDef(fd.params)) match {
      case (Some(b), Some((parentType, arg))) =>
        val body = b

        val calls = collectWithPC {
          case fi @ FunctionInvocation(tfd, _) if tfd.hasPrecondition => (fi, tfd.precondition.get)
        }(body)

        for {
          ((fi@FunctionInvocation(tfd, args), pre), path) <- calls
          cct <- parentType.knownCCDescendants
        } yield {
          val selectors = selectorsOfParentType(parentType, cct, arg.toVariable)

          val subCases = selectors.map { sel =>
            replace(Map(arg.toVariable -> sel),
              implies(precOrTrue(fd), tfd.withParamSubst(args, pre))
            )
          }

          val vc = implies(
            andJoin(Seq(IsInstanceOf(cct, arg.toVariable), precOrTrue(fd), path) ++ subCases),
            tfd.withParamSubst(args, pre)
          )

          // Crop the call to display it properly
          val fiS = sizeLimit(fi.asString, 25)

          VC(vc, fd, VCKinds.Info(VCKinds.Precondition, s"call $fiS, ind. on (${arg.asString} : ${cct.classDef.id.asString})")).setPos(fi)
        }

      case (body, _) =>
        if (body.isDefined) {
          reporter.warning(fd.getPos, "Could not find abstract class type argument to induct on")
        }
        super.generatePreconditions(fd)
    }
  }
}
