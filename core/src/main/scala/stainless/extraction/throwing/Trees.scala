/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package throwing

import inox.transformers.Transformer
import stainless.transformers.TreeTransformer
import stainless.transformers.TreeTraverser

trait Trees extends imperative.Trees { self =>

  protected def getExceptionType(using s: Symbols): Option[Type] =
    s.lookup.get[ClassDef]("stainless.lang.Exception").map(cd => ClassType(cd.id, Seq()))

  /** Throwing clause of an [[ast.Expressions.Expr]]. Corresponds to the Stainless keyword *throwing*
    *
    * @param body The body of the expression. It can contain at most one [[ast.Expressions.Require]] and
    *             one [[ast.Expressions.Ensuring]] sub-expression.
    * @param pred The predicate on exceptions to satisfy. It should be a function whose argument type
    *             is `stainless.lang.Exception` and defines the exceptional cases of this function.
    */
  sealed case class Throwing(body: Expr, pred: Lambda) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = (pred.getType, getExceptionType) match {
      case (FunctionType(Seq(expType), BooleanType()), Some(tpe)) => checkParamType(tpe, expType, body.getType)
      case _ => Untyped
    }
  }

  /** Throw expression. Corresponds to the Scala keyword *throw*
    *
    * @param ex The exception to be thrown.
    */
  sealed case class Throw(ex: Expr) extends Expr with CachingTyped {
    override protected def computeType(using Symbols): Type = getExceptionType match {
      case Some(tpe) => checkParamType(ex.getType, tpe, NothingType())
      case _ => Untyped
    }
  }

  /** Try-catch-finally block. Corresponds to Scala's *try { ... } catch { ... } finally { ... }* */
  sealed case class Try(body: Expr, cases: Seq[MatchCase], finallizer: Option[Expr]) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = getExceptionType match {
      case Some(tpe) if (
        cases.forall { case MatchCase(pat, guard, rhs) =>
          s.patternIsTyped(tpe, pat) &&
          guard.forall(g => s.isSubtypeOf(g.getType, BooleanType()))
        } && finallizer.forall(_.isTyped)
      ) => s.leastUpperBound(body.getType +: cases.map(_.rhs.getType))

      case _ => Untyped
    }
  }

  override val exprOps: ExprOps { val trees: self.type } = {
    class ExprOpsImpl(override val trees: self.type) extends ExprOps(trees)
    new ExprOpsImpl(self)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends imperative.Printer {
  protected val trees: Trees
  import trees._

  override def ppBody(tree: Tree)(using PrinterContext): Unit = tree match {
    case Throwing(Ensuring(body, post), pred) =>
      p"""|{
          |  $body
          |} ensuring {
          |  $post
          |} throwing {
          |  $pred
          |}"""

    case Throwing(body, pred) =>
      p"""|{
          |  $body
          |} throwing {
          |  $pred
          |}"""

    case Throw(ex) =>
      p"throw $ex"

    case Try(body, cases, fin) =>
      p"""|try {
          |  $body
          |}"""
      if (cases.nonEmpty) p"""| catch {
                              |  ${nary(cases, "\n")}
                              |}"""
      if (fin.nonEmpty) p"""| finally {
                            |  ${fin.get}
                            |}"""

    case _ => super.ppBody(tree)
  }

  override protected def noBracesSub(e: Tree): Seq[Expr] = e match {
    case Throwing(bd, pred) => Seq(bd, pred)
    case Try(e, _, f) => e +: f.toSeq
    case _ => super.noBracesSub(e)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: Throwing | _: Try)) => false
    case _ => super.requiresParentheses(ex, within)
  }
}

class ExprOps(override val trees: Trees) extends imperative.ExprOps(trees) { self =>
  import trees._

  object ExceptionsKind extends SpecKind("exceptions") { type Spec = Exceptions }

  case class Exceptions(expr: Lambda) extends Specification(ExceptionsKind) {
    def transform(tr: Transformer { val s: trees.type; val t: stainless.ast.Trees })(env: tr.Env): tr.t.exprOps.Specification = tr.t match {
      case tt: throwing.Trees =>
        // The goal is to work-around the following expression that causes scalac 2.13 to fail codegen
        // for the cast of tr.transform(expr, env) into tt.Lambda (probably due to `tt` being bound by a pattern match):
        //
        //      tt.exprOps.Exceptions(tr.transform(expr, env).asInstanceOf[tt.Lambda])
        //          .setPos(this).asInstanceOf[tr.t.exprOps.Specification]
        //
        val tLambda: tt.Lambda = tr.transform(expr, env) match {
          // doing case lam: tt.Lambda triggers a compile-time error, but not if we mix it with tr.t.Lambda...
          case lam: tr.t.Lambda with tt.Lambda => lam
        }
        tt.exprOps.Exceptions(tLambda).setPos(this).asInstanceOf[tr.t.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't transform exceptions into non-throwing trees")
    }

    def transform(tr: TreeTransformer { val s: trees.type; val t: stainless.ast.Trees }): tr.t.exprOps.Specification = tr.t match {
      case tt: throwing.Trees =>
        // Same story here
        val tLambda: tt.Lambda = tr.transform(expr) match {
          case lam: tr.t.Lambda with tt.Lambda => lam
        }
        tt.exprOps.Exceptions(tLambda).setPos(this).asInstanceOf[tr.t.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't transform exceptions into non-throwing trees")
    }

    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit =
      tr.traverse(expr)

    def isTrivial: Boolean = false
  }

  override def peelSpec(expr: Expr): Option[(Specification, Expr)] = expr match {
    case Throwing(body, pred) => Some((Exceptions(pred).setPos(expr), body))
    case _ => super.peelSpec(expr)
  }

  override def applySpec(spec: Specification, body: Expr): Expr = spec match {
    case Exceptions(pred) => Throwing(body, pred).setPos(spec.getPos)
    case _ => super.applySpec(spec, body)
  }

}

trait TreeDeconstructor extends imperative.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.Throwing(body, pred) =>
      (Seq(), Seq(), Seq(body, pred), Seq(), Seq(), (_, _, es, _, _) => t.Throwing(es(0), es(1).asInstanceOf[t.Lambda]))

    case s.Throw(ex) =>
      (Seq(), Seq(), Seq(ex), Seq(), Seq(), (_, _, es, _, _) => t.Throw(es.head))

    case s.Try(body, cases, fin) =>
      val (cids, cvs, ces, ctps, crecons) = deconstructCases(cases)
      (cids, cvs, (body +: ces) ++ fin, ctps, Seq(), (ids, vs, es, tps, _) => {
        val newBody +: rest = es
        val (nes, newFin) = if (fin.isEmpty) (rest, None) else (rest.init, rest.lastOption)
        t.Try(newBody, crecons(ids, vs, nes, tps), newFin)
      })

    case _ => super.deconstruct(e)
  }
}

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor