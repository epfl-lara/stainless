package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

object ChainComparator {
  import StructuralSize._

  def sizeDecreasing(e1: TypedExpr, e2s: Seq[(Seq[Expr], Expr)]) = _sizeDecreasing(e1, e2s map {
    case (path, e2) => (path, exprToTypedExpr(e2))
  })
  def sizeDecreasing(e1:      Expr, e2s: Seq[(Seq[Expr], Expr)]) = _sizeDecreasing(e1, e2s map {
    case (path, e2) => (path, exprToTypedExpr(e2))
  })

  private object ContainerType {
    def unapply(c: ClassType): Option[(CaseClassDef, Seq[(Identifier, TypeTree)])] = c match {
      case CaseClassType(classDef) =>
        if (classDef.fields.exists(arg => isSubtypeOf(arg.tpe, classDef.parent.map(AbstractClassType(_)).getOrElse(c)))) None
        else if (classDef.hasParent && classDef.parent.get.knownChildren.size > 1) None
        else Some((classDef, classDef.fields.map(arg => arg.id -> arg.tpe)))
      case _ => None
    }
  }

  private def _sizeDecreasing(te1: TypedExpr, te2s: Seq[(Seq[Expr], TypedExpr)]) : Expr = te1 match {
    case TypedExpr(e1, ContainerType(def1, types1)) => Or(types1.zipWithIndex map { case ((id1, type1), index) =>
      val newTe1 = TypedExpr(CaseClassSelector(def1, e1, id1), type1)
      val newTe2s = te2s.map({
        case (path, TypedExpr(e2, ContainerType(def2, types2))) =>
          val (id2, type2) = types2(index)
          (path, TypedExpr(CaseClassSelector(def2, e2, id2), type2))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      })
      _sizeDecreasing(newTe1, newTe2s)
    })
    case TypedExpr(e1, TupleType(types1)) => Or(types1.zipWithIndex map { case (type1, index) =>
      val newTe1 = TypedExpr(TupleSelect(e1, index + 1), type1)
      val newTe2s = te2s.map({
        case (path, TypedExpr(e2, TupleType(types2))) => (path, TypedExpr(TupleSelect(e2, index + 1), types2(index)))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      })
      _sizeDecreasing(newTe1, newTe2s)
    })
    case TypedExpr(_, _: ClassType) => And(te2s map {
      case (path, te2 @ TypedExpr(_, _: ClassType)) => Implies(And(path), GreaterThan(size(te1), size(te2)))
      case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
    })
    case TypedExpr(_, BooleanType) => BooleanLiteral(false)
    case TypedExpr(_, Int32Type) => BooleanLiteral(false)
    case _ => scala.sys.error("Unexpected type " + te1.tpe)
  }

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

  private def numericEndpoint(value: Expr, cluster: Set[Chain], checker: TerminationChecker) = {

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
      case And(es) => es.map(matches(_)).foldLeft[NumericEndpoint](AnyEndpoint)(_ min _)
      case Or(es) => es.map(matches(_)).foldLeft[NumericEndpoint](NoEndpoint)(_ max _)
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
      case IfExpr(cond, then, elze) => matches(cond) match {
        case NoEndpoint =>
          endpoint(then) min endpoint(elze)
        case ep =>
          val terminatingThen = functionCallsOf(then).forall(fi => checker.terminates(fi.funDef).isGuaranteed)
          val terminatingElze = functionCallsOf(elze).forall(fi => checker.terminates(fi.funDef).isGuaranteed)
          val thenEndpoint = if (terminatingThen) ep max endpoint(then) else endpoint(then)
          val elzeEndpoint = if (terminatingElze) ep.inverse max endpoint(elze) else endpoint(elze)
          thenEndpoint max elzeEndpoint
      }
      case _ => NoEndpoint
    }

    cluster.foldLeft[NumericEndpoint](AnyEndpoint)((acc, chain) => {
      acc min chain.inlined.foldLeft[NumericEndpoint](NoEndpoint)((acc, expr) => acc max endpoint(expr))
    })
  }

  def numericConverging(e1: TypedExpr, e2s: Seq[(Seq[Expr], Expr)], cluster: Set[Chain], checker: TerminationChecker) = _numericConverging(e1, e2s map {
    case (path, e2) => (path, exprToTypedExpr(e2))
  }, cluster, checker)
  def numericConverging(e1:      Expr, e2s: Seq[(Seq[Expr], Expr)], cluster: Set[Chain], checker: TerminationChecker) = _numericConverging(e1, e2s map {
    case (path, e2) => (path, exprToTypedExpr(e2))
  }, cluster, checker)

  private def _numericConverging(te1: TypedExpr, te2s: Seq[(Seq[Expr], TypedExpr)], cluster: Set[Chain], checker: TerminationChecker) : Expr = te1 match {
    case TypedExpr(e1, ContainerType(def1, types1)) => Or(types1.zipWithIndex map { case ((id1, type1), index) =>
      val newTe1 = TypedExpr(CaseClassSelector(def1, e1, id1), type1)
      val newTe2s = te2s.map({
        case (path, TypedExpr(e2, ContainerType(def2, types2))) =>
          val (id2, type2) = types2(index)
          (path, TypedExpr(CaseClassSelector(def2, e2, id2), type2))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      })
      _numericConverging(newTe1, newTe2s, cluster, checker)
    })
    case TypedExpr(e1, TupleType(types1)) => Or(types1.zipWithIndex map { case (type1, index) =>
      val newTe1 = TypedExpr(TupleSelect(e1, index + 1), type1)
      val newTe2s = te2s.map({
        case (path, TypedExpr(e2, TupleType(types2))) => (path, TypedExpr(TupleSelect(e2, index + 1), types2(index)))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      })
      _numericConverging(newTe1, newTe2s, cluster, checker)
    })
    case TypedExpr(e1, Int32Type) => numericEndpoint(e1, cluster, checker) match {
      case UpperBoundEndpoint => And(te2s map {
        case (path, TypedExpr(e2, Int32Type)) => Implies(And(path), GreaterThan(e1, e2))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      })
      case LowerBoundEndpoint => And(te2s map {
        case (path, TypedExpr(e2, Int32Type)) => Implies(And(path), LessThan(e1, e2))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      })
      case AnyEndpoint => Or(And(te2s map {
        case (path, TypedExpr(e2, Int32Type)) => Implies(And(path), GreaterThan(e1, e2))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      }), And(te2s map {
        case (path, TypedExpr(e2, Int32Type)) => Implies(And(path), LessThan(e1, e2))
        case (_, te2) => scala.sys.error("Unexpected input combinations: " + te1 + " " + te2)
      }))
      case InnerEndpoint => BooleanLiteral(false)
      case NoEndpoint => BooleanLiteral(false)
    }
    case TypedExpr(_, _: ClassType) => BooleanLiteral(false)
    case TypedExpr(_, BooleanType) => BooleanLiteral(false)
    case _ => scala.sys.error("Unexpected type " + te1.tpe)
  }
}

// vim: set ts=4 sw=4 et:
