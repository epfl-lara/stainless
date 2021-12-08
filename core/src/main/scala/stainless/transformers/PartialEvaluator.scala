/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package transformers

trait PartialEvaluator extends SimplifierWithPC { self =>
  import trees._
  import symbols.{given, _}
  import exprOps._

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = e match {
    case fi @ FunctionInvocation(id, tps, args) =>
      val tfd = fi.tfd
      val (rargs, pargs) = args.map(simplify(_, path)).unzip

      def containsChoose(expr: Expr): Boolean = exists {
        case (_: Choose) | (_: NoTree) => true
        case _ => false
      } (expr)

      def isProductiveUnfolding(inlined: Expr): Boolean = {
        def isKnown(expr: Expr): Boolean = expr match {
          case BooleanLiteral(_) => true
          case _ => false
        }

        val invocationPaths = collectWithPC(inlined) {
          case (fi: FunctionInvocation, subPath) if transitivelyCalls(fi.id, id) =>
            transform(subPath.toClause, path)
        }

        dynBlocked.set(dynBlocked.get + id)
        val isProductive = if (tfd.fd.flags contains Synthetic) {
          invocationPaths.exists(isKnown)
        } else {
          invocationPaths.forall(isKnown)
        }
        dynBlocked.set(dynBlocked.get - id)
        isProductive
      }

      def unfold(inlined: Expr): (Expr, Boolean) = {
        dynSteps.set(dynSteps.get + (id -> (dynSteps.get()(id) - 1)))
        val res = simplify(inlined, path)
        dynSteps.set(dynSteps.get + (id -> (dynSteps.get()(id) + 1)))
        res
      }

      if (!isUnfoldable(id)) {
        return (
          FunctionInvocation(id, tps, rargs).copiedFrom(fi),
          pargs.foldLeft(isPureFunction(id))(_ && _)
        )
      }

      val inlined: Option[Expr] = {
        val specced = BodyWithSpecs(tfd.fullBody)

        specced.bodyOpt.map { body =>
          val bodyPost = specced.getSpec(PostconditionKind).map {
            case Postcondition(lambda @ Lambda(Seq(res), post)) =>
              Let(res, body, Assert(post,
                Some("Inlined postcondition of " + tfd.id.name), res.toVariable).copiedFrom(lambda)
              ).copiedFrom(body)
          } .getOrElse(body)

          val bodyPrePost = exprOps.preconditionOf(tfd.fullBody).map { case pre =>
            Assert(pre, Some("Inlined precondition of " + tfd.id.name), bodyPost).copiedFrom(pre)
          } .getOrElse(bodyPost)

          freshenLocals((tfd.params zip rargs).foldRight(bodyPrePost) {
            case ((vd, e), body) => Let(vd, e, body).copiedFrom(body)
          })
        }
      }

      inlined
        .filterNot(containsChoose)
        .filter(isProductiveUnfolding)
        .map(unfold)
        .getOrElse((
          FunctionInvocation(id, tps, rargs).copiedFrom(fi),
          pargs.foldLeft(isPureFunction(id))(_ && _)
        ))

    case _ => super.simplify(e, path)
  }

  protected val maxUnfoldingSteps: Int = 50

  private[this] val dynBlocked = new ThreadLocal[Set[Identifier]] { override def initialValue = Set.empty[Identifier] }
  private[this] val dynSteps = new ThreadLocal[Map[Identifier, Int]] {
    override def initialValue = Map.empty[Identifier, Int].withDefault(_ => maxUnfoldingSteps)
  }

  private[this] def isUnfoldable(id: Identifier): Boolean = !dynBlocked.get()(id) && (dynSteps.get()(id) > 0)
}

