/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

trait Expressions extends ast.Expressions { self: Trees =>

  /* XLang functional trees to desugar */

  /** $encodingof `receiver.id[tps](args)` */
  case class MethodInvocation(receiver: Expr, id: Identifier, tps: Seq[Type], args: Seq[Expr]) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = receiver.getType match {
      case ct: ClassType => (s.lookupFunction(id, tps), s.lookupClass(id)) match {
        case (Some(tfd), Some(cd)) =>
          s.instantiateType(tfd.returnType, (cd.typeArgs zip ct.tps).toMap)
        case _ => Untyped
      }
      case _ => Untyped
    }
  }

  /** $encodingof `new id(args)` */
  case class ClassConstructor(ct: ClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = ct.lookupClass match {
      case Some(tcd) => checkParamTypes(args.map(_.getType), tcd.fields.map(_.tpe), ct)
      case _ => Untyped
    }
  }

  /** $encodingof `expr.selector` */
  case class ClassSelector(expr: Expr, selector: Identifier) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = expr.getType match {
      case ct: ClassType => ct.getField(selector).map(_.tpe).getOrElse(Untyped)
      case _ => Untyped
    }
  }

  /** $encodingof `this` */
  case class This(ct: ClassType) extends Expr {
    def getType(implicit s: Symbols): Type = ct
  }


  /* XLang imperative trees to desugar */

  /** $encodingof `{ expr1; expr2; ...; exprn; last }` */
  case class Block(exprs: Seq[Expr], last: Expr) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = if (exprs.forall(_.isTyped)) last.getType else Untyped
  }

  /** $encodingof `vd = value` */
  case class Assignment(v: Variable, value: Expr) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = if (s.isSubtypeOf(value.getType, v.tpe)) {
      UnitType
    } else {
      Untyped
    }
  }

  /** $encodingof `obj.selector = value` */
  case class FieldAssignment(obj: Expr, selector: Identifier, value: Expr) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = obj.getType match {
      case ct: ClassType => ct.getField(selector)
        .filter(vd => s.isSubtypeOf(value.getType, vd.tpe))
        .map(_ => UnitType)
        .getOrElse(Untyped)
      case _ => Untyped
    }
  }

  /** $encodingof `(while(cond) { ... }) invariant (pred)` */
  case class While(cond: Expr, body: Expr, pred: Option[Expr]) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type =
      if (cond.getType == BooleanType && body.isTyped && pred.forall(_.getType == BooleanType)) UnitType
      else Untyped
  }

  /** $encodingof `array(index) = value` */
  case class ArrayUpdate(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    def computeType(implicit s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type) if s.isSubtypeOf(value.getType, base) => UnitType
      case _ => Untyped
    }
  }
}

trait ExprOps extends ast.ExprOps {
  protected val trees: Trees
  import trees._

  def flattenBlocks(expr: Expr): Expr = postMap {
    case Block(exprs, last) =>
      val newExprs = (exprs.filter(_ != UnitLiteral()) :+ last).flatMap {
        case Block(es, l) => es :+ l
        case e => Seq(e)
      }

      Some(newExprs match {
        case Seq() => UnitLiteral()
        case Seq(e) => e
        case es => Block(es.init, es.last)
      })
    case _ => None
  } (expr)
}
