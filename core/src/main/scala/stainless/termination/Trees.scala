/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

trait Trees extends ast.Trees { self =>

  /* ========================================
   *             EXPRESSIONS
   * ======================================== */

  override val exprOps: ExprOps { val trees: self.type } = new {
    protected val trees: self.type = self
  } with ExprOps

  /* ========================================
   *              EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }

  /* ========================================
   *              DEFINITIONS
   * ======================================== */

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols { self0: Symbols =>

    private[this] val measureCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getMeasure(fd: FunDef): Option[Expr] = getMeasure(fd.typed)
    def getMeasure(tfd: TypedFunDef): Option[Expr] =
      measureCache.getOrElse(tfd, {
        val res = exprOps.measureOf(tfd.fullBody)
        measureCache(tfd) = res
        res
      })
  }

  implicit class TerminationFunDef(fd: FunDef) {
    def measure(implicit s: Symbols): Option[Expr] = s.getMeasure(fd)
  }

  implicit class TerminationTypedFunDef(tfd: TypedFunDef) {
    def measure(implicit s: Symbols): Option[Expr] = s.getMeasure(tfd)
  }
}

trait Printer extends ast.Printer {
  protected val trees: Trees
}

trait ExprOps extends ast.ExprOps {
  protected val trees: Trees
  import trees._

  case class Measure(expr: Expr) extends Specification {
    def map(trees: ast.Trees)(f: Expr => trees.Expr): trees.exprOps.Specification = trees match {
      case t: termination.Trees =>
        t.exprOps.Measure(f(expr).asInstanceOf[t.Expr]).asInstanceOf[trees.exprOps.Specification]
      case _ =>
        throw new java.lang.IllegalArgumentException("Can't map measure into non-termination trees")
    }
  }

  override def withSpec(expr: Expr, spec: Specification): Expr = spec match {
    case Measure(meas) => withMeasure(expr, Some(meas))
    case _ => super.withSpec(expr, spec)
  }

  override def hasSpec(e: Expr): Boolean = e match {
    case Decreases(_, _) => true
    case _ => super.hasSpec(e)
  }

  override def withBody(e: Expr, body: Expr): Expr = e match {
    case Decreases(meas, _) =>
      Decreases(meas, body).copiedFrom(e)
    case Require(pre, d @ Decreases(meas, _)) =>
      Require(pre, Decreases(meas, body).copiedFrom(d)).copiedFrom(e)
    case Ensuring(r @ Require(pre, d @ Decreases(meas, _)), post) =>
      Ensuring(Require(pre, Decreases(meas, body).copiedFrom(d)).copiedFrom(r), post).copiedFrom(e)
    case Ensuring(d @ Decreases(meas, _), post) =>
      Ensuring(Decreases(meas, body).copiedFrom(d), post).copiedFrom(e)
    case _ => super.withBody(e, body)
  }

  override def withoutSpecs(e: Expr): Option[Expr] = e match {
    case Decreases(_, b)                          => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Require(_, Decreases(_, b))              => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(_, Decreases(_, b)), _) => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Decreases(_, b), _)             => Option(b).filterNot(_.isInstanceOf[NoTree])
    case _                                        => super.withoutSpecs(e)
  }

  /** Returns the measure associated to an expression wrapped in an Option */
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

  override def deconstructSpecs(e: Expr)(implicit s: Symbols): (Seq[Specification], Option[Expr]) = {
    val measure = measureOf(e).map(Measure)
    val (specs, body) = super.deconstructSpecs(e)
    (specs ++ measure, body)
  }
}

trait TreeDeconstructor extends ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees
}
