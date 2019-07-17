/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import scala.collection.mutable.{Map => MutableMap}

import inox.utils.{NoPosition, Position}

trait ExprOps extends inox.ast.ExprOps {
  protected val trees: Trees
  import trees._

  /* =================
   * Body manipulation
   * ================= */

  /** Abstraction over contracts and specifications. */
  abstract class Specification {
    val expr: Expr
    def map(trees: Trees)(f: Expr => trees.Expr): trees.exprOps.Specification

    final def map(f: Expr => Expr): Specification = map(trees)(f).asInstanceOf[Specification]

    final def foreach(f: Expr => Unit): Unit = f(expr)
  }

  /** Precondition contract that corresponds to [[Expressions.Require]]. */
  case class Precondition(expr: Expr) extends Specification {
    def map(trees: Trees)(f: Expr => trees.Expr): trees.exprOps.Precondition =
      trees.exprOps.Precondition(f(expr))
  }

  /** Postcondition contract that corresponds to [[Expressions.Ensuring]]. */
  case class Postcondition(expr: Lambda) extends Specification {
    def map(trees: Trees)(f: Expr => trees.Expr): trees.exprOps.Postcondition =
      trees.exprOps.Postcondition(f(expr).asInstanceOf[trees.Lambda])
  }

  case class Measure(expr: Expr) extends Specification {
    def map(trees: ast.Trees)(f: Expr => trees.Expr): trees.exprOps.Specification = trees match {
      case t: ast.Trees =>
        t.exprOps.Measure(f(expr).asInstanceOf[t.Expr]).asInstanceOf[trees.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't map measure into non-stainless trees")
    }
  }

  /** Returns an expression annotated with the provided spec. */
  def withSpec(expr: Expr, spec: Specification): Expr = spec match {
    case Precondition(pred) => withPrecondition(expr, Some(pred))
    case Postcondition(post) => withPostcondition(expr, Some(post))
    case Measure(meas) => withMeasure(expr, Some(meas))
  }

  /** Returns whether a particular [[Expressions.Expr]] contains specification
    * constructs, namely [[Expressions.Require]] and [[Expressions.Ensuring]].
    */
  def hasSpec(e: Expr): Boolean = e match {
    case Require(_, _) => true
    case Ensuring(_, _) => true
    case Decreases(_, _) => true
    case Let(i, e, b) => hasSpec(b)
    case _ => false
  }

  protected final def wrapSpec(vd: ValDef, e: Expr, b: Expr): Expr = {
    def withoutLet(expr: Expr): Expr = expr match {
      case Let(`vd`, `e`, b) if hasSpec(b) => withoutLet(b)
      case Let(i, e, b) if hasSpec(b) => Let(i, e, withoutLet(b))
      case _ => expr
    }

    Let(vd, e, withoutLet(b))
  }

  /** Replaces the precondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no precondition is provided, removes any existing precondition.
    * Else, wraps the expression with a [[Expressions.Require]] clause referring to the new precondition.
    *
    * @param expr The current expression
    * @param pred An optional precondition. Setting it to None removes any precondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPrecondition(expr: Expr, pred: Option[Expr]): Expr =
    (pred.filterNot(_ == BooleanLiteral(true)), expr) match {
      case (Some(newPre), Require(pre, b))                    => Require(newPre, b).copiedFrom(expr)
      case (Some(newPre), Ensuring(req @ Require(pre, b), p)) => Ensuring(Require(newPre, b).copiedFrom(req), p).copiedFrom(expr)
      case (Some(newPre), Ensuring(b, p))                     => Ensuring(Require(newPre, b).copiedFrom(newPre), p).copiedFrom(expr)
      case (Some(newPre), Let(i, e, b)) if hasSpec(b)         => wrapSpec(i, e, withPrecondition(b, pred)).copiedFrom(expr)
      case (Some(newPre), b)                                  => Require(newPre, b).copiedFrom(expr)
      case (None, Require(pre, b))                            => b
      case (None, Ensuring(Require(pre, b), p))               => Ensuring(b, p).copiedFrom(expr)
      case (None, Let(i, e, b)) if hasSpec(b)                 => wrapSpec(i, e, withPrecondition(b, pred)).copiedFrom(expr)
      case (None, b)                                          => b
    }

  /** Replaces the postcondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no postcondition is provided, removes any existing postcondition.
    * Else, wraps the expression with a [[Expressions.Ensuring]] clause referring to the new postcondition.
    *
    * @param expr The current expression
    * @param oie An optional postcondition. Setting it to None removes any postcondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPostcondition(expr: Expr, oie: Option[Lambda]): Expr =
    (oie.filterNot(_.body == BooleanLiteral(true)), expr) match {
      case (Some(npost), Ensuring(b, post))          => Ensuring(b, npost).copiedFrom(expr)
      case (Some(npost), Let(i, e, b)) if hasSpec(b) => wrapSpec(i, e, withPostcondition(b, oie)).copiedFrom(expr)
      case (Some(npost), b)                          => Ensuring(b, npost).copiedFrom(expr)
      case (None, Ensuring(b, p))                    => b
      case (None, Let(i, e, b)) if hasSpec(b)        => wrapSpec(i, e, withPostcondition(b, oie)).copiedFrom(expr)
      case (None, b)                                 => b
    }

  /** Adds a body to a specification
    *
    * @param e The specification expression [[Expressions.Ensuring]] or [[Expressions.Require]].
    * If none of these, the argument is discarded.
    * @param body An option of [[Expressions.Expr]] possibly containing an expression body.
    * @return The post/pre condition with the body. If no body is provided, returns [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withBody(e: Expr, body: Expr): Expr = e match {
    case Let(i, e, b) if hasSpec(b)            => wrapSpec(i, e, withBody(b, body)).copiedFrom(e)
    case Require(pre, d @ Decreases(meas, _)) =>
      Require(pre, Decreases(meas, body).copiedFrom(d)).copiedFrom(e)
    case Require(pre, _)                       => Require(pre, body).copiedFrom(e)
    case Decreases(meas, _) =>
      Decreases(meas, body).copiedFrom(e)
    case Ensuring(r @ Require(pre, d @ Decreases(meas, _)), post) =>
      Ensuring(Require(pre, Decreases(meas, body).copiedFrom(d)).copiedFrom(r), post).copiedFrom(e)
    case Ensuring(d @ Decreases(meas, _), post) =>
      Ensuring(Decreases(meas, body).copiedFrom(d), post).copiedFrom(e)
    case Ensuring(req @ Require(pre, _), post) =>
      Ensuring(Require(pre, body).copiedFrom(req), post).copiedFrom(e)
    case Ensuring(_, post)                      => Ensuring(body, post).copiedFrom(e)
    case _                                      => body
  }

  /** Extracts the body without its specification
    *
    * [[Expressions.Expr]] trees contain its specifications as part of certain nodes.
    * This function helps extracting only the body part of an expression
    *
    * @return An option type with the resulting expression if not [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withoutSpecs(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                             => withoutSpecs(b).map(Let(i, e, _).copiedFrom(expr))
    case Decreases(_, b)                          => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Require(_, Decreases(_, b))              => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Require(pre, b)                          => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(_, Decreases(_, b)), _) => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(pre, b), post)          => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Decreases(_, b), _)             => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(b, post)                        => Option(b).filterNot(_.isInstanceOf[NoTree])
    case b                                        => Option(b).filterNot(_.isInstanceOf[NoTree])
  }

  /** Returns the precondition of an expression wrapped in Option */
  def preconditionOf(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                 => preconditionOf(b).map(Let(i, e, _).copiedFrom(expr))
    case Require(pre, _)              => Some(pre)
    case Ensuring(Require(pre, _), _) => Some(pre)
    case b                            => None
  }

  /** Returns the postcondition of an expression wrapped in Option */
  def postconditionOf(expr: Expr): Option[Lambda] = expr match {
    case Let(i, e, b)      => postconditionOf(b).map(l => l.copy(body = Let(i, e, l.body).copiedFrom(expr)).copiedFrom(l))
    case Ensuring(_, post) => Some(post)
    case _                 => None
  }

  def measureOf(expr: Expr): Option[Expr] = expr match {
    // @nv: we allow lets to wrap decreases (and other contracts) to facilitate
    //      certain program transformations (eg. FunctionClosure) and avoid
    //      repeating the let chains in each contract and body
    case Let(i, e, b)                             => measureOf(b).map(Let(i, e, _).copiedFrom(expr))
    case Decreases(m, _)                          => Some(m)
    case Require(_, Decreases(m, _))              => Some(m)
    case Ensuring(Require(_, Decreases(m, _)), _) => Some(m)
    case Ensuring(Decreases(m, _), _)             => Some(m)
    case _                                        => None
  }

  def withMeasure(expr: Expr, meas: Option[Expr]): Expr = (meas, expr) match {
    case (_, Let(i, e, b)) if hasSpec(b) =>
      wrapSpec(i, e, withMeasure(expr, meas)).copiedFrom(expr)
    case (Some(newMeas), Ensuring(r @ Require(pre, d @ Decreases(_, b)), post)) =>
      Ensuring(Require(pre, Decreases(newMeas, b).copiedFrom(d)).copiedFrom(r), post).copiedFrom(expr)
    case (Some(newMeas), Ensuring(r @ Require(pre, b), post)) =>
      Ensuring(Require(pre, Decreases(newMeas, b).copiedFrom(b)).copiedFrom(r), post).copiedFrom(expr)
    case (Some(newMeas), Ensuring(d @ Decreases(_, b), post)) =>
      Ensuring(Decreases(newMeas, b).copiedFrom(d), post).copiedFrom(expr)
    case (Some(newMeas), Ensuring(b, post)) =>
      Ensuring(Decreases(newMeas, b).copiedFrom(b), post).copiedFrom(expr)
    case (Some(newMeas), Require(pre, d @ Decreases(_, b))) =>
      Require(pre, Decreases(newMeas, b).copiedFrom(d)).copiedFrom(expr)
    case (Some(newMeas), Require(pre, b)) =>
      Require(pre, Decreases(newMeas, b).copiedFrom(b)).copiedFrom(expr)
    case (Some(newMeas), Decreases(_, b)) =>
      Decreases(newMeas, b).copiedFrom(expr)
    case (Some(newMeas), b) =>
      Decreases(newMeas, b).copiedFrom(expr)
    case (None, Ensuring(r @ Require(pre, Decreases(_, b)), post)) =>
      Ensuring(Require(pre, b).copiedFrom(r), post).copiedFrom(expr)
    case (None, Ensuring(Decreases(_, b), post)) =>
      Ensuring(b, post).copiedFrom(expr)
    case (None, Require(pre, Decreases(_, b))) =>
      Require(pre, b).copiedFrom(expr)
    case (None, Decreases(_, b)) =>
      b
    case (None, b) =>
      b
  }

  /** Deconstructs an expression into its [[Specification]] and body parts. */
  def deconstructSpecs(e: Expr)(implicit s: Symbols): (Seq[Specification], Option[Expr]) = {
    val measure = measureOf(e).map(Measure)
    val pre = Precondition(preconditionOf(e).getOrElse(BooleanLiteral(true).copiedFrom(e)))
    val post = Postcondition(postconditionOf(e).getOrElse(Lambda(
      Seq(ValDef(FreshIdentifier("res"), e.getType).copiedFrom(e)),
      BooleanLiteral(true).copiedFrom(e)
    ).copiedFrom(e)))

    val body = withoutSpecs(e)
    (Seq(pre, post) ++ measure, body)
  }

  /** Reconstructs an expression given a set of specifications
    * and a body, as obtained through [[deconstructSpecs]]. */
  final def reconstructSpecs(specs: Seq[Specification], body: Option[Expr], resultType: Type) = {
    val newBody = body match {
      case Some(body) => body
      case None =>
        val poss = specs.map(_.expr.getPos).filter(_ != NoPosition)
        val pos = if (poss.isEmpty) NoPosition
          else if (poss.size == 1) poss.head
          else Position.between(poss.min, poss.max)
        NoTree(resultType).setPos(pos)
    }
    specs.foldLeft(newBody)(withSpec)
  }

  override def freshenLocals(expr: Expr, freshenChooses: Boolean = false): Expr = {
    val subst: MutableMap[Variable, Variable] = MutableMap.empty
    variablesOf(expr).foreach(v => subst(v) = v)

    new SelfTreeTransformer {
      override def transform(vd: ValDef): ValDef = subst.getOrElse(vd.toVariable, {
        val res = super.transform(vd).freshen.toVariable
        subst(vd.toVariable) = res
        res
      }).toVal

      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => transform(v.toVal).toVariable
        case Choose(res, pred) if !freshenChooses =>
          val newVd = super.transform(res)
          subst(res.toVariable) = newVd.toVariable
          Choose(newVd, transform(pred)).copiedFrom(expr)
        case _ => super.transform(expr)
      }
    }.transform(expr)
  }

  def freshenTypeParams(tps: Seq[TypeParameter]): Seq[TypeParameter] = tps.map(_.freshen)

  /** Freshen the type parameters and parameters of the given [[FunDef]]. */
  def freshenSignature(fd: FunDef): FunDef = {
    val typeArgs = freshenTypeParams(fd.typeArgs)
    val tpSubst = (fd.typeArgs zip typeArgs).toMap

    val (paramSubst, params) = fd.params
      .map(vd => vd.copy(tpe = typeOps.instantiateType(vd.tpe, tpSubst)))
      .foldLeft((Map[ValDef, Expr](), Seq[ValDef]())) { case ((paramSubst, params), vd) =>
        val ntpe = typeOps.replaceFromSymbols(paramSubst, vd.tpe)
        val nvd = ValDef(vd.id.freshen, ntpe, vd.flags).copiedFrom(vd)
        (paramSubst + (vd -> nvd.toVariable), params :+ nvd)
      }

    new FunDef(fd.id, typeArgs.map(TypeParameterDef(_)), params,
      typeOps.replaceFromSymbols(paramSubst, typeOps.instantiateType(fd.returnType, tpSubst)),
      replaceFromSymbols(paramSubst, typeOps.instantiateType(fd.fullBody, tpSubst)),
      fd.flags
    ).copiedFrom(fd)
  }

  /** Applies the function to the I/O constraint and simplifies the resulting constraint */
  def applyAsMatches(p: Passes, f: Expr => Expr): Expr = {
    f(p.asConstraint) match {
      case Equals(newOut, MatchExpr(newIn, newCases)) =>
        val filtered = newCases flatMap {
          case MatchCase(p, g, `newOut`) => None
          case other => Some(other)
        }
        Passes(newIn, newOut, filtered)
      case other =>
        other
    }
  }
}
