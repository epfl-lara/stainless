/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.utils.Position

trait Instrumenter { self =>
  val trees: Trees
  val symbols: trees.Symbols

  import trees._
  import symbols._

  /* Basic types and interface */

  type Env <: AnyRef          /* the environment being aggregated in evaluation order */
  type VExpr = Expr           /* a value expression (i.e., the uninstrumented part) */
  type IExpr = Expr           /* an expression after instrumentation (*may* be instrumented) */
  // type IResult             /* explicitly distinguished result after instrumentation */
  type MExpr = Env => IResult /* an expression instrumented up to the concrete environment */

  def InstrumType(tpe: Type): Type  /* Instrum[T] */

  def instrument(e: Expr)(implicit pc: PurityCheck): MExpr

  /* Representation for explicit instrumentation */

  sealed abstract class IResult
  case class Uninstrum(ve: VExpr /* T-typed */, env: Env) extends IResult
  case class Instrum(ie: IExpr /* Instrum[T]-typed */) extends IResult

  def ensureInstrum(ir: IResult): IExpr

  // Merge various instrumented expressions, without instrumentation, if possible.
  // Assumes `cons` can deal with all instrumented or all value expressions.
  final protected def merge(irs: Seq[IResult])(f: Seq[IExpr] => IExpr): IResult = {
    val mustInstrument = irs.exists { case Instrum(_) => true; case _ => false }
    if (mustInstrument) {
      Instrum(f(irs.map(ensureInstrum)))
    } else {
      val (ves, envs) = irs.map { case Uninstrum(ve, env) => (ve, env); case _ => ??? } .unzip
      val env = envs.head
      assert(envs.forall(_ eq env))
      Uninstrum(f(ves), envs.head)
    }
  }

  /* Purity checking */

  sealed abstract class PurityCheck
  case object NoPurityCheck extends PurityCheck
  case class PurityCheckOn(what: String) extends PurityCheck

  def checkPurity(ir: IResult)(implicit pc: PurityCheck): IResult = {
    (ir, pc) match {
      case (Instrum(ie), PurityCheckOn(what)) =>
        throw IllegalImpureInstrumentation(s"A $what must not have an effect", ie.getPos)
      case _ =>
        ir
    }
  }

  // Only do the rewriting, but ensure that the result has no instrumentation (i.e. no effects)
  def instrumentPure(e: Expr, env0: Env): Expr =
    instrument(e)(PurityCheckOn("pure result"))(env0).asInstanceOf[Uninstrum].ve
}

case class IllegalImpureInstrumentation(msg: String, pos: Position) extends Exception(
  s"Purity check failed: $msg")

trait MonadicInstrumenter extends Instrumenter { self =>
  import trees._
  import symbols._

  /* Monadic interface */

  /* Override point */
  protected def pure(ve: VExpr): MExpr

  /* Override point */
  protected def bind(me: MExpr)(f: VExpr => MExpr)(implicit pc: PurityCheck): MExpr

  /* Override point */
  protected def choice(mes: Seq[MExpr])(f: Seq[IResult] => IResult): MExpr

  /* Helpers */

  final protected def bind(me1: MExpr, me2: MExpr)(f: (VExpr, VExpr) => MExpr)(
      implicit pc: PurityCheck): MExpr =
    bind(me1) { ve1 => bind(me2) { ve2 => f(ve1, ve2) } }

  final protected def bindMany(mes: Seq[MExpr])(f: Seq[VExpr] => MExpr)(
      implicit pc: PurityCheck): MExpr =
  {
    def rec(mes: Seq[MExpr], ves: Seq[VExpr]): MExpr = mes match {
      case Nil => f(ves.reverse)
      case me +: mes => bind(me)(ve => rec(mes, ve +: ves))
    }
    rec(mes, Seq.empty)
  }

  /* Default instrumentation (requiring no instrumentation) */

  override def instrument(e: Expr)(implicit pc: PurityCheck): MExpr = e match {
    case IfExpr(cond, thenn, elze) =>
      bind(instrument(cond)) { vcond =>
        choice(Seq(instrument(thenn), instrument(elze))) { case Seq(irthenn, irelze) =>
          merge(Seq(irthenn, irelze)) { case Seq(ithenn, ielze) =>
            IfExpr(vcond, ithenn, ielze).copiedFrom(e)
          }
        }
      }

    case MatchExpr(scrut, cses) =>
      bind(instrument(scrut)) { vscrut =>
        // NOTE: Case guards and patterns must be pure, so we can sequence them after the
        // scrutinee here without affecting any of the case bodies.
        val mguards = cses.map(cse => instrument(cse.optGuard.getOrElse(BooleanLiteral(true))))
        bindMany(mguards) { vguards =>
          val mbodies = cses.map(cse => instrument(cse.rhs))
          choice(mbodies) { irbodies =>
            merge(irbodies) { ibodies =>
              val newCses = (cses, vguards, ibodies).zipped.map { (oldCse, vguard, ibody) =>
                val vguardOpt = vguard match {
                  case BooleanLiteral(true) => None
                  case _ => Some(vguard)
                }
                MatchCase(oldCse.pattern, vguardOpt, ibody).copiedFrom(oldCse)
              }
              MatchExpr(vscrut, newCses).copiedFrom(e)
            }
          }
        }
      }

    case _: Lambda | _: Application =>
      ???

    case _: LetRec | _: ApplyLetRec =>
      ???

    case And(args) =>
      val ifExpr = args.reduceRight((arg, acc) =>
        IfExpr(arg, acc, BooleanLiteral(false).copiedFrom(arg)).copiedFrom(arg))
      instrument(ifExpr)

    case Or(args) =>
      val ifExpr = args.reduceRight((arg, acc) =>
        IfExpr(arg, BooleanLiteral(true).copiedFrom(arg), acc).copiedFrom(arg))
      instrument(ifExpr)

    case Implies(e1, e2) =>
      instrument(Or(Not(e1).copiedFrom(e1), e2).copiedFrom(e))

    // TODO: [According to a comment in ImperativeCodeElimination:]
    // These should be covered by Operator, but some bug requires them to be treated explicitly.
    case Assert(cond, msg, body) =>
      bind(instrument(cond), instrument(body)) { (vcond, vbody) =>
        pure(Assert(vcond, msg, vbody).copiedFrom(e))
      }
    case Assume(cond, body) =>
      bind(instrument(cond), instrument(body)) { (vcond, vbody) =>
        pure(Assume(vcond, vbody).copiedFrom(e))
      }

    case Operator(es, recons) =>
      bindMany(es.map(instrument)) { ves =>
        pure(recons(ves).copiedFrom(e))
      }
  }
}

trait StateInstrumenter extends MonadicInstrumenter {
  import trees._
  import symbols.{let => _, _}
  import dsl._

  type SExpr = Expr
  type Env = SExpr /* Our state is a single BigInt-typed counter */

  def stateTpe: Type

  final def InstrumType(tpe: Type) = T(tpe, stateTpe)

  def ensureInstrum(ir: IResult): IExpr =
    ir match {
      case Uninstrum(ve, s0) => E(ve, s0).copiedFrom(ve)
      case Instrum(ie) => ie
    }

  protected def pure(ve: VExpr): MExpr = { s0 =>
    Uninstrum(ve, s0)
  }

  protected def bind(me: MExpr)(f: VExpr => MExpr)(implicit pc: PurityCheck): MExpr = { s0 =>
    checkPurity(
      me(s0) match {
        case Uninstrum(ve1, _) =>
          f(ve1)(s0)
        case Instrum(ie1) =>
          Instrum(
            let("ie" :: ie1.getType, ie1)(
              ie1 => ensureInstrum(f(ie1._1)(ie1._2))
            ).copiedFrom(ie1)
          )
      }
    )
  }

  protected def choice(mes: Seq[MExpr])(f: Seq[IResult] => IResult): MExpr = { s0 =>
    f(mes.map(_.apply(s0)))
  }
}
