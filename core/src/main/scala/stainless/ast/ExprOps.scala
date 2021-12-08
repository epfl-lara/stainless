/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import scala.collection.mutable.{Map => MutableMap}

import inox.utils.{NoPosition, Position, Positioned}
import inox.transformers.Transformer
import stainless.transformers.TreeTransformer
import stainless.transformers.TreeTraverser

class ExprOps(override val trees: Trees) extends inox.ast.ExprOps(trees) { self =>
  import trees._

  /* =================
   * Body manipulation
   * ================= */

  case class SpecKind(name: String) { type Spec <: Specification }
  object PreconditionKind extends SpecKind("pre") { type Spec = Precondition }
  object PostconditionKind extends SpecKind("post") { type Spec = Postcondition }
  object MeasureKind extends SpecKind("measure") { type Spec = Measure }
  object LetKind extends SpecKind("let") { type Spec = LetInSpec }

  /** Abstraction over contracts and specifications. */
  abstract class Specification(val kind: SpecKind) extends Positioned {
    def transform(tr: Transformer { val s: trees.type; val t: Trees })(env: tr.Env): tr.t.exprOps.Specification
    def transform(tr: TreeTransformer { val s: trees.type; val t: Trees }): tr.t.exprOps.Specification
    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit

    final def transform(f: Expr => Expr): kind.Spec = {
      class TransformImpl(override val s: trees.type, override val t: trees.type)
        extends TreeTransformer with stainless.transformers.Transformer {
        override def transform(e: Expr): Expr = f(e)
      }
      transform(new TransformImpl(trees, trees)).asInstanceOf[kind.Spec]
    }

    final def traverse(f: Expr => Unit): Unit = {
      class TraverseImpl(override val trees: self.trees.type) extends TreeTraverser {
        override def traverse(e: Expr): Unit = f(e)
      }
      traverse(new TraverseImpl(self.trees))
    }

    // Whether the spec might as well be omitted
    def isTrivial: Boolean
  }

  /** Binding that appear before a specification with a [[Expressions.Let]]'s. */
  case class LetInSpec(vd: ValDef, expr: Expr) extends Specification(LetKind) {
    def transform(tr: Transformer { val s: trees.type; val t: Trees })(env: tr.Env): tr.t.exprOps.Specification =
      tr.t.exprOps.LetInSpec(tr.transform(vd, env), tr.transform(expr, env)).setPos(this)
    def transform(tr: TreeTransformer { val s: trees.type; val t: Trees }): tr.t.exprOps.Specification =
      tr.t.exprOps.LetInSpec(tr.transform(vd), tr.transform(expr)).setPos(this)
    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit = {
      tr.traverse(vd)
      tr.traverse(expr)
    }

    def isTrivial: Boolean = false
  }


  /** Precondition contract that corresponds to [[Expressions.Require]]'s. */
  case class Precondition(expr: Expr) extends Specification(PreconditionKind) {
    def transform(tr: Transformer { val s: trees.type; val t: Trees })(env: tr.Env): tr.t.exprOps.Specification =
      tr.t.exprOps.Precondition(tr.transform(expr, env)).setPos(this)
    def transform(tr: TreeTransformer { val s: trees.type; val t: Trees }): tr.t.exprOps.Specification =
      tr.t.exprOps.Precondition(tr.transform(expr)).setPos(this)

    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit = {
      tr.traverse(expr)
    }

    def isTrivial: Boolean = expr == BooleanLiteral(true)
  }

  /** Postcondition contract that corresponds to [[Expressions.Ensuring]]. */
  case class Postcondition(expr: Lambda) extends Specification(PostconditionKind) {
    def transform(tr: Transformer { val s: trees.type; val t: Trees })(env: tr.Env): tr.t.exprOps.Specification =
      tr.t.exprOps.Postcondition(tr.transform(expr, env).asInstanceOf[tr.t.Lambda]).setPos(this)
    def transform(tr: TreeTransformer { val s: trees.type; val t: Trees }): tr.t.exprOps.Specification =
      tr.t.exprOps.Postcondition(tr.transform(expr).asInstanceOf[tr.t.Lambda]).setPos(this)

    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit = {
      tr.traverse(expr)
    }

    def isTrivial: Boolean = expr.body == BooleanLiteral(true)
  }

  /** Measure contract that corresponds to [[Expressions.Decreases]]. */
  case class Measure(expr: Expr) extends Specification(MeasureKind) {
    def transform(tr: Transformer { val s: trees.type; val t: Trees })(env: tr.Env): tr.t.exprOps.Specification =
      tr.t.exprOps.Measure(tr.transform(expr, env)).setPos(this)
    def transform(tr: TreeTransformer { val s: trees.type; val t: Trees }): tr.t.exprOps.Specification =
      tr.t.exprOps.Measure(tr.transform(expr)).setPos(this)

    def traverse(tr: TreeTraverser { val trees: self.trees.type }): Unit = {
      tr.traverse(expr)
    }

    def isTrivial: Boolean = false
  }

  case class BodyWithSpecs(
    specs: Seq[Specification],
    body: Expr)
  {
    def hasBody: Boolean = !body.isInstanceOf[NoTree]

    def bodyOpt: Option[Expr] = if (hasBody) Some(body) else None

    def getFirstSpec(kind: SpecKind): Option[kind.Spec] = {
      specs.find(_.kind == kind).asInstanceOf[Option[kind.Spec]]
    }

    def getSpec(kind: SpecKind): Option[kind.Spec] = {
      val filtered = specs.filter(_.kind == kind)
      if (filtered.isEmpty) None
      else if (filtered.size >= 2) sys.error(s"`getSpec` must be called when there is at most one spec of kind $kind")
      else Some(filtered.head.asInstanceOf[kind.Spec])
    }

    def withSpec(specOpt: Option[Specification]): BodyWithSpecs = {
      if (specOpt.nonEmpty) withSpec(specOpt.get)
      else this
    }

    def withSpec(spec: Specification): BodyWithSpecs = {
      def adaptPos(spec: Specification, closest: Option[Specification]) = {
        if (spec.getPos == NoPosition)
          spec.setPos(closest.getOrElse(body).getPos)
        spec
      }
      assert(specs.count(_.kind == spec.kind) <= 1, s"Duplicate specs of kind `${spec.kind.name}`")
      val newSpecs = specs.indexWhere(_.kind == spec.kind) match {
        case -1 => adaptPos(spec, specs.headOption) +: specs
        case i => specs.updated(i, adaptPos(spec, Some(specs(i))))
      }
      this.copy(specs = newSpecs)
    }

    def mapOrDefaultSpec(kind: SpecKind)(
        f: kind.Spec => kind.Spec, default: => kind.Spec): BodyWithSpecs =
      withSpec(getSpec(kind).map(f).getOrElse(default))

    def withoutSpec(kind: SpecKind): BodyWithSpecs =
      this.copy(specs = specs.filterNot(_.kind == kind))

    def withBody(body: Expr): BodyWithSpecs =
      this.copy(body = body)

    def withBody(bodyOpt: Option[Expr], resultType: Type): BodyWithSpecs =
      withBody(bodyOpt getOrElse {
        val poss = specs.map(_.getPos).filter(_ != NoPosition)
        val pos = if (poss.isEmpty) NoPosition
          else if (poss.size == 1) poss.head
          else Position.between(poss.min, poss.max)
        NoTree(resultType).setPos(pos)
      })

    def wrapLets(expr: Expr) =
      specs.filter(_.kind == LetKind).foldRight(expr) {
        case (spec @ LetInSpec(vd, e), b) => Let(vd, e, b).setPos(spec)
        case _ => sys.error("shouldn't happen thanks to the filtering above")
      }

    val letsAndBody: Expr = wrapLets(body)

    def reconstructed: Expr = specs.foldRight(body)(applySpec)

    def addSpec(optSpec: Option[Specification]): BodyWithSpecs = {
      if (optSpec.nonEmpty) this.copy(specs = optSpec.get +: specs)
      else this
    }

    // add a post-condition spec if there aren't any
    def addPost(using Symbols): BodyWithSpecs = {
      if (specs.exists(_.kind == PostconditionKind)) this
      else BodyWithSpecs(Postcondition(Lambda(
        Seq(ValDef(FreshIdentifier("res"), body.getType).setPos(body)),
        BooleanLiteral(true).setPos(body)
      ).setPos(body)).setPos(body) +: specs, body)
    }

    def letsAndSpecs(kind: SpecKind): Seq[Specification] = {
      val (afterLast, untilLast) = specs.reverse.span(_.kind != kind)
      untilLast.reverse.filter(spec => spec.kind == kind || spec.kind == LetKind)
    }

  }

  object BodyWithSpecs {
    def apply(fullBody: Expr): BodyWithSpecs = {
      import scala.annotation.tailrec

      // Gather the lets and specs around `expr`.
      // Also handles lets interleaved with specs
      type LetInfo = (ValDef, Expr, Position)
      @tailrec
      def gatherSpecs(
          expr: Expr,
          letsUncommitted: Seq[LetInfo],
          exprUncommitted: Option[Expr],
          specs: Seq[Specification]
        ): (Seq[Specification], Expr) =
      {
        peelSpec(expr) match {
          case Some((let: LetInSpec, rest)) =>
            val newExprUncommitted = exprUncommitted.orElse(Some(expr))
            gatherSpecs(rest, (let.vd, let.expr, let.getPos) +: letsUncommitted, newExprUncommitted, specs)
          case Some((spec, rest)) =>
            val lets = letsUncommitted.map { case (vd, expr, pos) =>
              LetInSpec(vd, expr).setPos(pos)
            }
            gatherSpecs(rest, Seq.empty, None, spec +: (lets ++ specs))
          case None =>
            (specs.reverse, exprUncommitted.getOrElse(expr))
        }
      }

      val (specs, body) = gatherSpecs(fullBody, Seq.empty, None, Seq.empty)
      BodyWithSpecs(specs, body)
    }
  }

  /* These can be overridden to add new kinds of specifications: */

  def peelSpec(expr: Expr): Option[(Specification, Expr)] = expr match {
    case Require(pred, body) => Some((Precondition(pred).setPos(expr), body))
    case Ensuring(body, pred) => Some((Postcondition(pred).setPos(expr), body))
    case Decreases(measure, body) => Some((Measure(measure).setPos(expr), body))
    case Let(vd, e, body) => Some((LetInSpec(vd, e).setPos(expr), body))
    case _ => None
  }

  def applySpec(spec: Specification, body: Expr): Expr = (spec match {
    case Precondition(pred) => Require(pred, body)
    case Postcondition(pred) => Ensuring(body, pred)
    case Measure(measure) => Decreases(measure, body)
    case LetInSpec(vd, expr) => Let(vd, expr, body)
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
    withSpec(expr, pred.filterNot(_ == BooleanLiteral(true)).map(Precondition.apply).toLeft(PreconditionKind))

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
    withSpec(expr, pred.filterNot(_.body == BooleanLiteral(true)).map(Postcondition.apply).toLeft(PostconditionKind))

  final def withMeasure(expr: Expr, measure: Option[Expr]): Expr =
    withSpec(expr, measure.map(expr => Measure(expr).setPos(expr)).toLeft(MeasureKind))

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
    * This function helps extracting only the body part of an expression, wrapped with
    * the lets that are shared with the specification
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
    val letsAndRequires = specced.letsAndSpecs(PreconditionKind)
    if (letsAndRequires.isEmpty) None
    else Some(letsAndRequires.init.foldRight(letsAndRequires.last.asInstanceOf[Precondition].expr) {
      case (spec @ LetInSpec(vd, e), acc) => Let(vd, e, acc).setPos(spec)
      case (spec @ Precondition(pred), acc) => And(pred, acc).setPos(spec)
      case _ => sys.error("shouldn't happen thanks to the filtering above")
    })
  }

  /** Returns the postcondition of an expression wrapped in Option */
  final def postconditionOf(expr: Expr): Option[Lambda] = {
    val BodyWithSpecs(specs, _) = BodyWithSpecs(expr)
    val (beforePost, postAndAfter) = specs.span(_.kind != PostconditionKind)
    val lets = beforePost.filter(_.kind == LetKind)
    if (postAndAfter.isEmpty) None
    else {
      val lambda @ Lambda(vd, postBody) = postAndAfter.head.asInstanceOf[Postcondition].expr
      Some(Lambda(vd, lets.foldRight(postBody) {
        case (spec @ LetInSpec(vd, e), acc) => Let(vd, e, acc).setPos(spec)
        case _ => sys.error("shouldn't happen thanks to the filtering above")
      }).setPos(lambda))
    }
  }

  /** Returns the measure of an expression wrapped in Option */
  final def measureOf(expr: Expr): Option[Expr] = {
    val BodyWithSpecs(specs, _) = BodyWithSpecs(expr)
    val (beforeMeasure, measureAndAfter) = specs.span(_.kind != MeasureKind)
    val lets = beforeMeasure.filter(_.kind == LetKind)
    if (measureAndAfter.isEmpty) None
    else Some(lets.foldRight(measureAndAfter.head.asInstanceOf[Measure].expr) {
      case (spec @ LetInSpec(vd, e), acc) => Let(vd, e, acc).setPos(spec)
      case _ => sys.error("shouldn't happen thanks to the filtering above")
    })
  }

  /** Deconstructs an expression into its [[Specification]] and body parts. */
  final def deconstructSpecs(e: Expr): (Seq[Specification], Option[Expr]) = {
    val specced = BodyWithSpecs(e)
    (specced.specs, specced.bodyOpt)
  }

  /** Reconstructs an expression given a set of specifications */
  final def reconstructSpecs(specs: Seq[Specification], body: Option[Expr], resultType: Type) =
    BodyWithSpecs(specs.filterNot(_.isTrivial), UnitLiteral())
      .withBody(body, resultType)
      .reconstructed

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
    new ConcreteStainlessSelfTreeTransformer {
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

  /* =============================
   * Freshening of local variables
   * ============================= */

  protected class StainlessFreshener(override val s: self.trees.type,
                                     override val t: self.trees.type,
                                     freshenChooses: Boolean)
    extends Freshener(freshenChooses) with transformers.Transformer {

    def this(freshenChooses: Boolean) = this(self.trees, self.trees, freshenChooses)

    override def transformCase(cse: MatchCase, env: Env): MatchCase = {
      val MatchCase(pat, guard, rhs) = cse
      val (newPat, newEnv) = transformAndGetEnv(pat, env)
      val newGuard = guard.map(transform(_, newEnv))
      val newRhs = transform(rhs, newEnv)
      MatchCase(newPat, newGuard, newRhs).copiedFrom(cse)
    }

    override def transform(pat: Pattern, env: Env): Pattern = {
      transformAndGetEnv(pat, env)._1
    }

    def transformAndGetEnv(pat: Pattern, env: Env): (Pattern, Env) = pat match {
      case WildcardPattern(vdOpt) =>
        val freshVdOpt = vdOpt.map(vd => transform(vd.freshen, env))
        val newEnv = env ++ freshVdOpt.map(freshVd => vdOpt.get.id -> freshVd.id)
        (WildcardPattern(freshVdOpt), newEnv)

      case ADTPattern(vdOpt, id, tps, subPatterns) =>
        val freshVdOpt = vdOpt.map(vd => transform(vd.freshen, env))
        val newPatterns = subPatterns.map(transformAndGetEnv(_, env))
        (
          ADTPattern(
            freshVdOpt,
            transform(id, env),
            tps.map(transform(_, env)),
            newPatterns.map(_._1)
          ),
          newPatterns.map(_._2).fold
            (env ++ freshVdOpt.map(freshVd => vdOpt.get.id -> freshVd.id))
            (_ ++ _)
        )

      case TuplePattern(vdOpt, subPatterns) =>
        val freshVdOpt = vdOpt.map(vd => transform(vd.freshen, env))
        val newPatterns = subPatterns.map(transformAndGetEnv(_, env))
        (
          TuplePattern(freshVdOpt, newPatterns.map(_._1)),
          newPatterns.map(_._2).fold
            (env ++ freshVdOpt.map(freshVd => vdOpt.get.id -> freshVd.id))
            (_ ++ _)
        )

      case LiteralPattern(vdOpt, lit) =>
        val freshVdOpt = vdOpt.map(vd => transform(vd.freshen, env))
        val newEnv = env ++ freshVdOpt.map(freshVd => vdOpt.get.id -> freshVd.id)
        (LiteralPattern(freshVdOpt, lit), newEnv)

      case UnapplyPattern(vdOpt, recs, id, tps, subPatterns) =>
        val freshVdOpt = vdOpt.map(vd => transform(vd.freshen, env))
        val newRecs = recs.map(transform(_, env))
        val newPatterns = subPatterns.map(transformAndGetEnv(_, env))
        (
          UnapplyPattern(
            freshVdOpt,
            newRecs,
            transform(id, env),
            tps.map(transform(_, env)),
            newPatterns.map(_._1)
          ),
          newPatterns.map(_._2).fold
            (env ++ freshVdOpt.map(freshVd => vdOpt.get.id -> freshVd.id))
            (_ ++ _)
        )

      case _ => (super.transform(pat, env), env)
    }
  }

  override def freshenLocals(expr: Expr, freshenChooses: Boolean = false): Expr = {
    new StainlessFreshener(freshenChooses).transform(expr, Map.empty[Identifier, Identifier])
  }

}
