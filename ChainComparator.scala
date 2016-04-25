/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Path
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps._
import purescala.Constructors._
import purescala.Common._

trait ChainComparator { self : StructuralSize =>
  val checker: TerminationChecker

  def structuralDecreasing(e1: Expr, e2s: Seq[(Path, Expr)]): Seq[Expr] = flatTypesPowerset(e1.getType).toSeq.map {
    recons => andJoin(e2s.map { case (path, e2) =>
      path implies GreaterThan(self.fullSize(recons(e1)), self.fullSize(recons(e2)))
    })
  }

  /*
  def structuralDecreasing(e1: Expr, e2s: Seq[(Seq[Expr], Expr)]) : Expr = e1.getType match {
    case ContainerType(def1, fields1) => Or(fields1.zipWithIndex map { case ((id1, type1), index) =>
      structuralDecreasing(CaseClassSelector(def1, e1, id1), e2s.map { case (path, e2) =>
        e2.getType match {
          case ContainerType(def2, fields2) => (path, CaseClassSelector(def2, e2, fields2(index)._1))
          case _ => scala.sys.error("Unexpected input combinations: " + e1 + " " + e2)
        }
      })
    })
    case TupleType(types1) => Or((0 until types1.length) map { case index =>
      structuralDecreasing(tupleSelect(e1, index + 1), e2s.map { case (path, e2) =>
        e2.getType match {
          case TupleType(_) => (path, tupleSelect(e2, index + 1))
          case _ => scala.sys.error("Unexpected input combination: " + e1 + " " + e2)
        }
      })
    })
    case c: ClassType => And(e2s map { case (path, e2) =>
      e2.getType match {
        case c2: ClassType => Implies(And(path), GreaterThan(self.size(e1), self.size(e2)))
        case _ => scala.sys.error("Unexpected input combination: " + e1 + " " + e2)
      }
    })
    case _ => BooleanLiteral(false)
  }
  */

  private sealed abstract class NumericEndpoint {
    def inverse: NumericEndpoint = this match {
      case UpperBoundEndpoint => LowerBoundEndpoint
      case LowerBoundEndpoint => UpperBoundEndpoint
      case InnerEndpoint => AnyEndpoint
      case AnyEndpoint => InnerEndpoint
      case NoEndpoint => NoEndpoint
    }
    def <(that: NumericEndpoint) : Boolean = (this, that) match {
      case (UpperBoundEndpoint, AnyEndpoint) => true
      case (LowerBoundEndpoint, AnyEndpoint) => true
      case (InnerEndpoint, AnyEndpoint) => true
      case (NoEndpoint, AnyEndpoint) => true
      case (InnerEndpoint, UpperBoundEndpoint) => true
      case (InnerEndpoint, LowerBoundEndpoint) => true
      case (NoEndpoint, UpperBoundEndpoint) => true
      case (NoEndpoint, LowerBoundEndpoint) => true
      case (NoEndpoint, InnerEndpoint) => true
      case _ => false
    }
    def <=(that: NumericEndpoint) : Boolean = (this, that) match {
      case (t1, t2) if t1 < t2 => true
      case (t1, t2) if t1 == t2 => true
      case _ => false
    }
    def min(that: NumericEndpoint) : NumericEndpoint = {
      if (this <= that) this else if (that <= this) that else InnerEndpoint
    }
    def max(that: NumericEndpoint) : NumericEndpoint = {
      if (this <= that) that else if (that <= this) this else AnyEndpoint
    }
  }

  private case object UpperBoundEndpoint extends NumericEndpoint
  private case object LowerBoundEndpoint extends NumericEndpoint
  private case object InnerEndpoint extends NumericEndpoint
  private case object AnyEndpoint extends NumericEndpoint
  private case object NoEndpoint extends NumericEndpoint

  private def numericEndpoint(value: Expr, cluster: Set[Chain]) = {

    object Value {
      val vars = variablesOf(value)
      assert(vars.size == 1)

      def simplifyBinaryArithmetic(e1: Expr, e2: Expr) : Boolean = {
        val (inE1, inE2) = (variablesOf(e1) == vars, variablesOf(e2) == vars)
        if (inE1 && inE2) false else if (inE1) unapply(e1) else if (inE2) unapply(e2) else {
          scala.sys.error("How the heck did we get here?!?")
        }
      }

      def unapply(expr: Expr): Boolean = if (variablesOf(expr) != vars) false else expr match {
        case Plus(e1, e2) => simplifyBinaryArithmetic(e1, e2)
        case Minus(e1, e2) => simplifyBinaryArithmetic(e1, e2)
        // case Times(e1, e2) => ... Need to make sure multiplier is not negative!
        case e => e == value
      }
    }

    def matches(expr: Expr) : NumericEndpoint = expr match {
      case And(es) => es.map(matches).foldLeft[NumericEndpoint](AnyEndpoint)(_ min _)
      case Or(es) => es.map(matches).foldLeft[NumericEndpoint](NoEndpoint)(_ max _)
      case Not(e) => matches(e).inverse
      case GreaterThan(Value(), e)   if variablesOf(e).isEmpty => LowerBoundEndpoint
      case GreaterThan(e, Value())   if variablesOf(e).isEmpty => UpperBoundEndpoint
      case GreaterEquals(Value(), e) if variablesOf(e).isEmpty => LowerBoundEndpoint
      case GreaterEquals(e, Value()) if variablesOf(e).isEmpty => UpperBoundEndpoint
      case Equals(Value(), e)        if variablesOf(e).isEmpty => InnerEndpoint
      case Equals(e, Value())        if variablesOf(e).isEmpty => InnerEndpoint
      case LessThan(e1, e2)   => matches(GreaterThan(e2, e1))
      case LessEquals(e1, e2) => matches(GreaterEquals(e2, e1))
      case _ => NoEndpoint
    }

    def endpoint(expr: Expr) : NumericEndpoint = expr match {
      case IfExpr(cond, thenn, elze) => matches(cond) match {
        case NoEndpoint =>
          endpoint(thenn) min endpoint(elze)
        case ep =>
          val terminatingThen = functionCallsOf(thenn).forall(fi => checker.terminates(fi.tfd.fd).isGuaranteed)
          val terminatingElze = functionCallsOf(elze).forall(fi => checker.terminates(fi.tfd.fd).isGuaranteed)
          val thenEndpoint = if (terminatingThen) ep max endpoint(thenn) else endpoint(thenn)
          val elzeEndpoint = if (terminatingElze) ep.inverse max endpoint(elze) else endpoint(elze)
          thenEndpoint max elzeEndpoint
      }
      case _ => NoEndpoint
    }

    cluster.foldLeft[NumericEndpoint](AnyEndpoint) { (acc, chain) =>
      acc min chain.inlined.foldLeft[NumericEndpoint](NoEndpoint) { (acc, expr) =>
        acc max endpoint(expr)
      }
    }
  }

  def numericConverging(e1: Expr, e2s: Seq[(Path, Expr)], cluster: Set[Chain]) : Seq[Expr] = flatType(e1.getType).toSeq.flatMap {
    recons => recons(e1) match {
      case e if e.getType == IntegerType =>
        val endpoint = numericEndpoint(e, cluster)

        val uppers = if (endpoint == UpperBoundEndpoint || endpoint == AnyEndpoint) {
          Some(andJoin(e2s map { case (path, e2) => path implies GreaterThan(e, recons(e2)) }))
        } else {
          None
        }

        val lowers = if (endpoint == LowerBoundEndpoint || endpoint == AnyEndpoint) {
          Some(andJoin(e2s map { case (path, e2) => path implies LessThan(e, recons(e2)) }))
        } else {
          None
        }

        uppers ++ lowers
      case _ => Seq.empty
    }
  }
}

// vim: set ts=4 sw=4 et:
