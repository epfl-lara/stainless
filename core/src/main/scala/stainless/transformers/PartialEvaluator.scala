/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package transformers

import scala.language.existentials

trait PartialEvaluator extends SimplifierWithPC { self =>
  import trees._
  import symbols._
  import exprOps._

  protected def strictlyPositive(tpe: Type, e: Expr): Expr = (tpe match {
    case IntegerType() => GreaterThan(e, IntegerLiteral(0))
    case BVType(signed, size) => GreaterThan(e, BVLiteral(signed, 0, size))
    case TupleType(tps) => and((1 to tps.length).map(i => strictlyPositive(tps(i-1), TupleSelect(e,i))): _*)
    case _ => sys.error(s"Type $tpe is not supported for measures")
  }).setPos(e)

  override protected def simplify(e: Expr, path: Env): (Expr, Boolean) = e match {
    // case Annotated(e, Seq(Unchecked)) =>
    //   simplify(e, path)

    case fi @ FunctionInvocation(id, tps, args) =>
      val tfd = fi.tfd
      val (rargs, pargs) = args.map(simplify(_, path)).unzip

      def containsChoose(expr: Expr): Boolean = exists {
        case (_: Choose) | (_: NoTree) => true
        case _ => false
      } (expr)

      def validMeasure: Boolean = {
        measureOf(tfd.fullBody) match {
          case Some(measure) =>
            val nextMeasure = exprOps.replaceFromSymbols(tfd.params.zip(args).toMap, measure)
            val query = strictlyPositive(nextMeasure.getType, nextMeasure)
            path.implies(query)

          case None => false
        }
      }

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
        val (specs, body) = deconstructSpecs(tfd.fullBody)

        body.map { body =>
          val pre = specs.collectFirst { case Precondition(e) => e }.get
          val l @ Lambda(Seq(res), post) = specs.collectFirst { case Postcondition(e) => e }.get

          val newBody: Expr = Assert(pre, Some("Inlined precondition of " + tfd.id.name), Let(res, body,
            Assert(post, Some("Inlined postcondition of " + tfd.id.name), res.toVariable).copiedFrom(l)
          ).copiedFrom(body)).copiedFrom(pre)

          freshenLocals((tfd.params zip rargs).foldRight(newBody) {
            case ((vd, e), body) => Let(vd, e, body).copiedFrom(body)
          })
        }
      }

      inlined
        .filterNot(containsChoose)
        .filter(expr => validMeasure || isProductiveUnfolding(expr))
        .map(unfold)
        .getOrElse((
          FunctionInvocation(id, tps, rargs).copiedFrom(fi),
          pargs.foldLeft(isPureFunction(id))(_ && _)
        ))

    case _ => super.simplify(e, path)
  }

  protected val maxUnfoldingSteps: Int = 50

  private[this] val dynBlocked = new ThreadLocal[Set[Identifier]] { override def initialValue = Set.empty }
  private[this] val dynSteps = new ThreadLocal[Map[Identifier, Int]] {
    override def initialValue = Map.empty.withDefault(_ => maxUnfoldingSteps)
  }

  private[this] def isUnfoldable(id: Identifier): Boolean = !dynBlocked.get()(id) && (dynSteps.get()(id) > 0)
}

