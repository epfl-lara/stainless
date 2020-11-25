/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import scala.collection.mutable.{Map => MutableMap}

import inox.utils.{NoPosition, Position, Positioned}

trait ExprOps extends inox.ast.ExprOps {
  protected val trees: Trees
  import trees._

  /* =================
   * Body manipulation
   * ================= */

  case class SpecKind(name: String) { type Spec <: Specification }
  object PreconditionKind extends SpecKind("pre") { type Spec = Precondition }
  object PostconditionKind extends SpecKind("post") { type Spec = Postcondition }
  object MeasureKind extends SpecKind("measure") { type Spec = Measure }

  /** Abstraction over contracts and specifications. */
  abstract class Specification(val kind: SpecKind) extends Positioned {
    val expr: Expr
    def map(t: ast.Trees)(f: Expr => t.Expr): t.exprOps.Specification

    final def map(f: Expr => Expr): Specification = map(trees)(f).asInstanceOf[Specification]

    final def foreach(f: Expr => Unit): Unit = f(expr)

    // Whether the spec might as well be omitted
    def isTrivial: Boolean

    // Close the specification under let bindings shared by all specs
    def letWrapped(specced: BodyWithSpecs): Specification
  }

  /** Precondition contract that corresponds to [[Expressions.Require]]. */
  case class Precondition(expr: Expr) extends Specification(PreconditionKind) {
    def map(t: ast.Trees)(f: Expr => t.Expr): t.exprOps.Precondition =
      t.exprOps.Precondition(f(expr)).setPos(this.getPos)

    def isTrivial: Boolean = expr == BooleanLiteral(true)

    def letWrapped(specced: BodyWithSpecs): Precondition =
      Precondition(specced.wrapLets(expr)).setPos(this.getPos)
  }

  /** Postcondition contract that corresponds to [[Expressions.Ensuring]]. */
  case class Postcondition(expr: Lambda) extends Specification(PostconditionKind) {
    def map(t: ast.Trees)(f: Expr => t.Expr): t.exprOps.Postcondition =
      t.exprOps.Postcondition(f(expr).asInstanceOf[t.Lambda])
        .setPos(this.getPos)

    def isTrivial: Boolean = expr.body == BooleanLiteral(true)

    def letWrapped(specced: BodyWithSpecs): Postcondition =
      Postcondition(expr.copy(body = specced.wrapLets(expr.body)).copiedFrom(expr))
        .setPos(this.getPos)
  }

  case class Measure(expr: Expr) extends Specification(MeasureKind) {
    def map(t: ast.Trees)(f: Expr => t.Expr): t.exprOps.Specification =
      t.exprOps.Measure(f(expr)).setPos(this.getPos)

    def isTrivial: Boolean = false

    def letWrapped(specced: BodyWithSpecs): Measure =
      Measure(specced.wrapLets(expr)).setPos(this.getPos)
  }

  case class BodyWithSpecs(
    lets: Seq[(ValDef, Expr, Position)],
    specs: Seq[Specification],
    body: Expr)
  {
    def hasBody: Boolean = !body.isInstanceOf[NoTree]

    def bodyOpt: Option[Expr] = if (hasBody) Some(body) else None

    lazy val hasDuplicates: Boolean = specs.size != specs.map(_.kind).toSet.size

    def getSpec(kind: SpecKind): Option[kind.Spec] = {
      assert(!hasDuplicates, "Duplicate specs")
      specs.find(_.kind == kind).asInstanceOf[Option[kind.Spec]]
    }

    def withSpec(spec: Specification): BodyWithSpecs = {
      def adaptPos(spec: Specification, closest: Option[Specification]) = {
        if (spec.getPos == NoPosition)
          spec.setPos(closest.getOrElse(body).getPos)
        spec
      }
      assert(!hasDuplicates, "Duplicate specs")
      val newSpecs = specs.indexWhere(_.kind == spec.kind) match {
        case -1 => adaptPos(spec, specs.headOption) +: specs
        case i => specs.updated(i, adaptPos(spec, Some(specs(i))))
      }
      this.copy(specs = newSpecs)
    }

    def withoutSpec(kind: SpecKind): BodyWithSpecs =
      this.copy(specs = specs.filterNot(_.kind == kind))

    def withBody(body: Expr): BodyWithSpecs =
      this.copy(body = body)

    def withBody(bodyOpt: Option[Expr], resultType: Type): BodyWithSpecs =
      withBody(bodyOpt getOrElse {
        val poss = specs.map(_.expr.getPos).filter(_ != NoPosition)
        val pos = if (poss.isEmpty) NoPosition
          else if (poss.size == 1) poss.head
          else Position.between(poss.min, poss.max)
        NoTree(resultType).setPos(pos)
      })

    def wrapLets(expr: Expr) =
      lets.foldRight(expr) {
        case ((vd, e, pos), b) => Let(vd, e, b).setPos(pos)
      }

    def reconstructed: Expr =
      wrapLets(specs.foldRight(body)(applySpec))
  }

  object BodyWithSpecs {
    def apply(fullBody: Expr): BodyWithSpecs = {
      import scala.annotation.tailrec

      // Gather the lets and duplicate-free prefix of specs around `expr`.
      // Also handles lets interleaved with specs.
      type LetInfo = (ValDef, Expr, Position)
      @tailrec
      def gatherSpecs(
          expr: Expr,
          letsCommitted: Seq[LetInfo],
          letsUncommitted: Seq[LetInfo],
          exprUncommitted: Option[Expr],
          specs: Seq[Specification]
        ): Option[(Seq[LetInfo], Seq[Specification], Expr)] =
      {
        peelSpec(expr) match {
          case Some((spec, rest)) if !specs.exists(_.kind == spec.kind) =>
            gatherSpecs(rest, letsUncommitted ++ letsCommitted, Seq.empty, None, spec +: specs)
          case _ =>
            expr match {
              case Let(vd, e, b) =>
                // A Let potentially wrapping a spec
                val newLetsUncommitted = (vd, e, expr.getPos) +: letsUncommitted
                val newExprUncommitted = exprUncommitted.orElse(Some(expr))
                gatherSpecs(b, letsCommitted, newLetsUncommitted, newExprUncommitted, specs)
              case _ =>
                if (specs.isEmpty) {
                  // Done (no specs at all)
                  None
                } else {
                  // Done (found some specs)
                  val body = exprUncommitted.getOrElse(expr)
                  Some((letsCommitted.reverse, specs.reverse, body))
                }
            }
        }
      }

      def bodyMissing(expr: Expr): Boolean = expr match {
        case NoTree(_) => true
        case Let(_, _, rest) => bodyMissing(rest)
        case _ => false
      }

      gatherSpecs(fullBody, Seq.empty, Seq.empty, None, Seq.empty) match {
        case Some((lets, specs, body)) =>
          assert(!body.isInstanceOf[Let] || !bodyMissing(body),
            "Body is missing, but there are let bindings irrelevant to specs")
          assert(lets.isEmpty || specs.nonEmpty)
          BodyWithSpecs(lets, specs, body)
        case None =>
          BodyWithSpecs(Seq.empty, Seq.empty, fullBody)
      }
    }
  }

  /* These can be overridden to add new kinds of specifications: */

  def peelSpec(expr: Expr): Option[(Specification, Expr)] = expr match {
    case Require(pred, body) => Some((Precondition(pred).setPos(expr), body))
    case Ensuring(body, pred) => Some((Postcondition(pred).setPos(expr), body))
    case Decreases(measure, body) => Some((Measure(measure).setPos(expr), body))
    case _ => None
  }

  def applySpec(spec: Specification, body: Expr): Expr = (spec match {
    case Precondition(pred) => Require(pred, body)
    case Postcondition(pred) => Ensuring(body, pred)
    case Measure(measure) => Decreases(measure, body)
  }).setPos(spec.getPos)

  // Adds or replaces a spec, when given a left. Removes the given spec kind, when given a right.
  final def withSpec(expr: Expr, spec: Either[Specification, SpecKind]): Expr =
    spec match {
      case Left(spec) => BodyWithSpecs(expr).withSpec(spec).reconstructed
      case Right(specKind) => BodyWithSpecs(expr).withoutSpec(specKind).reconstructed
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
  final def withPrecondition(expr: Expr, pred: Option[Expr]): Expr =
    withSpec(expr, pred.filterNot(_ == BooleanLiteral(true)).map(Precondition).toLeft(PreconditionKind))

  /** Replaces the postcondition of an existing [[Expressions.Expr]] with a new one.
    *
    * If no postcondition is provided, removes any existing postcondition.
    * Else, wraps the expression with a [[Expressions.Ensuring]] clause referring to the new postcondition.
    *
    * @param expr The current expression
    * @param pred An optional postcondition. Setting it to None removes any postcondition.
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  final def withPostcondition(expr: Expr, pred: Option[Lambda]): Expr =
    withSpec(expr, pred.filterNot(_.body == BooleanLiteral(true)).map(Postcondition).toLeft(PostconditionKind))

  final def withMeasure(expr: Expr, measure: Option[Expr]): Expr =
    withSpec(expr, measure.map(Measure).toLeft(MeasureKind))

  /** Adds a body to a specification
    *
    * @param expr The specification expression [[Expressions.Ensuring]] or [[Expressions.Require]].
    * If none of these, the argument is discarded.
    * @param body An expression body
    * @return The post/pre condition with the body. If no body is provided, returns [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  final def withBody(expr: Expr, body: Expr): Expr =
    BodyWithSpecs(expr).withBody(body).reconstructed

  /** Extracts the body without its specification
    *
    * [[Expressions.Expr]] trees contain its specifications as part of certain nodes.
    * This function helps extracting only the body part of an expression
    *
    * @return An option type with the resulting expression if not [[Expressions.NoTree]]
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  final def withoutSpecs(expr: Expr): Option[Expr] = {
    val specced = BodyWithSpecs(expr)
    specced.bodyOpt.map(specced.wrapLets)
  }

  /** Returns the precondition of an expression wrapped in Option */
  final def preconditionOf(expr: Expr): Option[Expr] = {
    val specced = BodyWithSpecs(expr)
    specced.getSpec(PreconditionKind).map(_.letWrapped(specced).expr)
  }

  /** Returns the postcondition of an expression wrapped in Option */
  final def postconditionOf(expr: Expr): Option[Lambda] = {
    val specced = BodyWithSpecs(expr)
    specced.getSpec(PostconditionKind).map(_.letWrapped(specced).expr)
  }

  final def measureOf(expr: Expr): Option[Expr] = {
    val specced = BodyWithSpecs(expr)
    specced.getSpec(MeasureKind).map(_.letWrapped(specced).expr)
  }

  /** Deconstructs an expression into its [[Specification]] and body parts. */
  final def deconstructSpecs(e: Expr)(implicit s: Symbols): (Seq[Specification], Option[Expr]) = {
    val specced = BodyWithSpecs(e)

    // NOTE: This behavior is replicated from `withoutBody` as used in the old `deconstructSpecs`.
    //   Ideally we should not rewrap here to maintain the sharing of lets between specs and body.
    val wrappedBodyOpt = specced.bodyOpt.map(specced.wrapLets)
    var specs = specced.specs.map(_.letWrapped(specced))
    if (specced.getSpec(PreconditionKind).isEmpty)
      specs +:= Precondition(preconditionOf(e).getOrElse(BooleanLiteral(true).copiedFrom(e)))
    if (specced.getSpec(PostconditionKind).isEmpty)
      specs +:= Postcondition(postconditionOf(e).getOrElse(Lambda(
        Seq(ValDef(FreshIdentifier("res"), e.getType).copiedFrom(e)),
        BooleanLiteral(true).copiedFrom(e)
      ).copiedFrom(e)))

    (specs, wrappedBodyOpt)
  }

  /** Reconstructs an expression given a set of specifications
    * and a body, as obtained through [[deconstructSpecs]]. */
  final def reconstructSpecs(specs: Seq[Specification], body: Option[Expr], resultType: Type) =
    BodyWithSpecs(Seq.empty, specs.filterNot(_.isTrivial), UnitLiteral())
      .withBody(body, resultType)
      .reconstructed

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

  def replaceKeepPositions(subst: Map[Variable, Expr], expr: Expr): Expr = {
    new SelfTreeTransformer {
      override def transform(expr: Expr): Expr = expr match {
        case v: Variable => subst.getOrElse(v, v).copiedFrom(v)
        case _ => super.transform(expr)
      }
    }.transform(expr)
  }

  def stripAnnotations(tpe: Type): Type = tpe match {
    case AnnotatedType(tpe, _) => stripAnnotations(tpe)
    case _ => tpe
  }
}
