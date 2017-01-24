/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import scala.collection.mutable.{Map => MutableMap}

trait Trees extends ast.Trees { self =>

  /* ========================================
   *             EXPRESSIONS
   * ======================================== */

  /** $encodingof `decreases(measure); body` */
  case class Decreases(measure: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = measure.getType match {
      case IntegerType | BVType(_) => body.getType
      case TupleType(tps) if tps.forall { case IntegerType | BVType(_) => true case _ => false } => body.getType
      case _ => Untyped
    }
  }

  override val exprOps: ExprOps { val trees: self.type } = new {
    protected val trees: self.type = self
  } with ExprOps


  /* ========================================
   *              EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees) = that match {
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
      measureCache.getOrElseUpdate(tfd, exprOps.measureOf(tfd.fullBody))
  }

  implicit class TerminationFunDef(fd: FunDef) {
    def measure(implicit s: Symbols): Option[Expr] = s.getMeasure(fd)
  }

  implicit class TerminationTypedFunDef(tfd: TypedFunDef) {
    def measure(implicit s: Symbols): Option[Expr] = s.getMeasure(tfd)
  }
}

trait ExprOps extends ast.ExprOps {
  protected val trees: Trees
  import trees._

  override def withBody(expr: Expr, body: Expr): Expr = expr match {
    case Require(pre, dec @ Decreases(measure, _)) =>
      Require(pre, Decreases(measure, body).copiedFrom(dec)).copiedFrom(expr)
    case Ensuring(req @ Require(pre, dec @ Decreases(measure, _)), post) =>
      Ensuring(Require(pre, Decreases(measure, body).copiedFrom(dec)).copiedFrom(req), post).copiedFrom(expr)
    case Ensuring(dec @ Decreases(measure, _), post) =>
      Ensuring(Decreases(measure, body).copiedFrom(dec), post).copiedFrom(expr)
    case _ => super.withBody(expr, body)
  }

  override def withoutSpec(expr: Expr): Option[Expr] = expr match {
    case Require(_, Decreases(_, b))              => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Require(_, Decreases(_, b)), _) => Option(b).filterNot(_.isInstanceOf[NoTree])
    case Ensuring(Decreases(_, b), _)             => Option(b).filterNot(_.isInstanceOf[NoTree])
    case _                                        => super.withoutSpec(expr)
  }

  /** Returns the measure associated to an expression wrapped in an Option */
  def measureOf(expr: Expr): Option[Expr] = expr match {
    case Let(i, e, b)                             => measureOf(b).map(Let(i, e, _).copiedFrom(expr))
    case Require(_, Decreases(m, _))              => Some(m)
    case Ensuring(Require(_, Decreases(m, _)), _) => Some(m)
    case Ensuring(Decreases(m, _), _)             => Some(m)
    case _                                        => None
  }
}

trait TreeDeconstructor extends ast.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.Decreases(measure, body) =>
      (Seq(), Seq(measure, body), Seq(), (_, es, _) => t.Decreases(es(0), es(1)))

    case _ => super.deconstruct(e)
  }
}
