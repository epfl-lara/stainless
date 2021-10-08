/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

trait Expressions extends inox.ast.Expressions with Types { self: Trees =>

  /** Stands for an undefined Expr, similar to `???` or `null`
    *
    * During code generation, it gets compiled to `null`, or the 0 of the
    * respective type for value types.
    */
  sealed case class NoTree(tpe: Type) extends Expr with Terminal {
    override def getType(using Symbols): Type = tpe.getType
  }


  /* Specifications */

  /** Computational errors (unmatched case, taking min of an empty set,
    * division by zero, etc.). Corresponds to the ``error[T](description)``
    * Stainless library function.
    * It should always be typed according to the expected type.
    *
    * @param tpe The type of this expression
    * @param description The description of the error
    */
  sealed case class Error(tpe: Type, description: String) extends Expr with Terminal {
    override def getType(using Symbols): Type = tpe.getType
  }


  /** Precondition of an [[Expressions.Expr]]. Corresponds to the Stainless keyword *require*
    *
    * @param pred The precondition formula inside ``require(...)``
    * @param body The body following the ``require(...)``
    */
  sealed case class Require(pred: Expr, body: Expr) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = {
      if (s.isSubtypeOf(pred.getType, BooleanType())) body.getType
      else Untyped
    }
  }

  /** Unchecked conditions *
    *
    * @param body
    */
  sealed case class Annotated(body: Expr, flags: Seq[Flag]) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = body.getType
  }

  /** Postcondition of an [[Expressions.Expr]]. Corresponds to the Stainless keyword *ensuring*
    *
    * @param body The body of the expression. It can contain at most one [[Expressions.Require]] sub-expression.
    * @param pred The predicate to satisfy. It should be a function whose argument's type can handle the type of the body
    */
  sealed case class Ensuring(body: Expr, pred: Lambda) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = pred.getType match {
      case FunctionType(Seq(bodyType), BooleanType()) if s.isSubtypeOf(body.getType, bodyType) =>
        body.getType
      case _ =>
        Untyped
    }

    /** Converts this ensuring clause to the body followed by an assert statement */
    def toAssert(using s: Symbols): Expr = {
      val res = ValDef(FreshIdentifier("res", true), getType)
      Let(res, body, Assert(
        s.application(pred, Seq(res.toVariable)),
        Some("Postcondition @" + this.getPos),
        res.toVariable
      ))
    }
  }

  /** Local assertions with customizable error message
    *
    * @param pred The predicate, first argument of `assert(..., ...)`
    * @param error An optional error string to display if the assert fails. Second argument of `assert(..., ...)`
    * @param body The expression following `assert(..., ...)`
    */
  sealed case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = {
      if (s.isSubtypeOf(pred.getType, BooleanType())) body.getType
      else Untyped
    }
  }


  /* Pattern-match expression */

  /** $encodingof `... match { ... }`
    *
    * '''cases''' should be nonempty.
    *
    * @param scrutinee Expression to the left of the '''match''' keyword
    * @param cases A sequence of cases to match `scrutinee` against
    */
  sealed case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr with CachingTyped {
    require(cases.nonEmpty)

    override protected def computeType(using s: Symbols): Type =
      if (cases forall { case MatchCase(pat, guard, rhs) =>
        s.patternIsTyped(scrutinee.getType, pat) &&
        guard.forall(_.getType == BooleanType())
      }) {
        s.leastUpperBound(cases.map(_.rhs.getType))
      } else {
        Untyped
      }
  }

  /** $encodingof `case pattern [if optGuard] => rhs`
    *
    * @param pattern The pattern just to the right of the '''case''' keyword
    * @param optGuard An optional if-condition just to the left of the `=>`
    * @param rhs The expression to the right of `=>`
    * @see [[Expressions.MatchExpr]]
    */
  sealed case class MatchCase(pattern: Pattern, optGuard: Option[Expr], rhs: Expr) extends Tree

  /** $encodingof a pattern after a '''case''' keyword.
    *
    * @see [[Expressions.MatchCase]]
    */
  abstract class Pattern extends Tree {
    val subPatterns: Seq[Pattern]
    val binder: Option[ValDef]

    private def subBinders = subPatterns.flatMap(_.binders).toSet
    def binders: Set[ValDef] = subBinders ++ binder.toSet
  }

  /** Pattern encoding `case _ => `, or `case binder => ` if [[binder]] is present */
  sealed case class WildcardPattern(binder: Option[ValDef]) extends Pattern { // c @ _
    val subPatterns = Seq()
  }

  /** Pattern encoding `case binder @ id(subPatterns...) =>`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  sealed case class ADTPattern(binder: Option[ValDef], id: Identifier, tps: Seq[Type], subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding tuple pattern `case binder @ (subPatterns...) =>`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  sealed case class TuplePattern(binder: Option[ValDef], subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding like `case binder @ 0 => ...` or `case binder @ "Foo" => ...`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  sealed case class LiteralPattern[+T](binder: Option[ValDef], lit: Literal[T]) extends Pattern {
    val subPatterns = Seq()
  }

  protected def unapplyScrut(scrut: Expr, up: UnapplyPattern)(using s: Symbols): Expr = {
    FunctionInvocation(up.id, up.tps, up.recs :+ scrut)
  }

  protected def unapplyAccessor(unapplied: Expr, id: Identifier, up: UnapplyPattern)(using s: Symbols): Expr = {
    val fd = s.lookupFunction(id)
      .filter(_.params.size == 1)
      .getOrElse(throw extraction.MalformedStainlessCode(up, "Invalid unapply accessor"))
    val unapp = up.getFunction
    val tpMap = s.instantiation(fd.params.head.tpe, unapp.returnType)
      .getOrElse(throw extraction.MalformedStainlessCode(up, "Unapply pattern failed type instantiation"))
    fd.typed(fd.typeArgs map tpMap).applied(Seq(unapplied))
  }

  /** A custom pattern defined through an object's `unapply` function */
  sealed case class UnapplyPattern(binder: Option[ValDef], recs: Seq[Expr], id: Identifier, tps: Seq[Type], subPatterns: Seq[Pattern]) extends Pattern {
    def getFunction(using s: Symbols): TypedFunDef = s.getFunction(id, tps)

    private def getIsEmpty(using s: Symbols): Identifier =
      getFunction.flags.collectFirst { case IsUnapply(isEmpty, _) => isEmpty }
        .getOrElse(throw extraction.MalformedStainlessCode(this, "Unapply pattern on non-unapply method (isEmpty)"))

    private def getGet(using s: Symbols): Identifier =
      getFunction.flags.collectFirst { case IsUnapply(_, get) => get }
        .getOrElse(throw extraction.MalformedStainlessCode(this, "Unapply pattern on non-unapply method (get)"))

    def isEmptyUnapplied(unapp: Expr)(using s: Symbols): Expr = unapplyAccessor(unapp, getIsEmpty, this).copiedFrom(this)
    def getUnapplied(unapp: Expr)(using s: Symbols): Expr = unapplyAccessor(unapp, getGet, this).copiedFrom(this)

    def isEmpty(scrut: Expr)(using s: Symbols): Expr =
      isEmptyUnapplied(unapplyScrut(scrut, this).copiedFrom(this))

    def get(scrut: Expr)(using s: Symbols): Expr =
      getUnapplied(unapplyScrut(scrut, this).copiedFrom(this))

    def subTypes(in: Type)(using s: Symbols): Seq[Type] =
      unwrapTupleType(s.unapplyAccessorResultType(getGet, getFunction.returnType).get, subPatterns.size)
  }

  /** Symbolic I/O examples as a match/case.
    * $encodingof `out == (in match { cases; case _ => out })`
    *
    * [[cases]] should be nonempty. If you are not sure about this, you should use [[ast.Constructors#passes]] instead.
    *
    * @param in The input expression
    * @param out The output expression
    * @param cases The cases to compare against
    */
  case class Passes(in: Expr, out: Expr, cases: Seq[MatchCase]) extends Expr with CachingTyped {
    require(cases.nonEmpty)

    override protected def computeType(using s: Symbols) = {
      if (in.getType == Untyped || out.getType == Untyped) Untyped
      else if (s.leastUpperBound(cases.map(_.rhs.getType)) == Untyped) Untyped
      else BooleanType()
    }

    /** Transforms the set of I/O examples to a constraint equality. */
    def asConstraint: Expr = {
      val defaultCase = MatchCase(WildcardPattern(None), None, out).copiedFrom(this)
      Equals(out, MatchExpr(in, cases :+ defaultCase).copiedFrom(this)).copiedFrom(this)
    }
  }

  /* Array Operations */

  /** $encodingof `Array(elems...)` */
  sealed case class FiniteArray(elems: Seq[Expr], base: Type) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = {
      checkParamTypes(elems.map(_.getType), List.fill(elems.size)(base), unveilUntyped(ArrayType(base)))
    }
  }

  /** $encodingof `Array(elems...)` for huge arrays
    * @param elems   Map from an index to the corresponding element
    * @param default Default value for indexes not in the [[elems]] map
    * @param size    Array length
    */
  sealed case class LargeArray(elems: Map[Int, Expr], default: Expr, size: Expr, base: Type) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = {
      if (s.isSubtypeOf(size.getType, Int32Type())) {
        unveilUntyped(ArrayType(checkParamTypes(
          (default +: elems.values.toSeq).map(_.getType),
          List.fill(elems.size + 1)(base),
          base
        )))
      } else {
        Untyped
      }
    }
  }

  /** $encodingof `array(index)` */
  sealed case class ArraySelect(array: Expr, index: Expr) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type()) => base
      case _ => Untyped
    }
  }

  /** $encodingof `array.updated(index, value)` */
  sealed case class ArrayUpdated(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type()) => unveilUntyped(ArrayType(s.leastUpperBound(base, value.getType)))
      case _ => Untyped
    }
  }

  /** $encodingof `array.length` */
  sealed case class ArrayLength(array: Expr) extends Expr with CachingTyped {
    override protected def computeType(using s: Symbols): Type = array.getType match {
      case ArrayType(_) => Int32Type()
      case _ => Untyped
    }
  }

  /** $encodingof `decreases(measure); body` */
  case class Decreases(measure: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(using s: Symbols): Type = measure.getType match {
      case Untyped => Untyped
      case _ => body.getType
    }
  }

  /** $encodingof `max(e1, e2, e3)` */
  case class Max(exprs: Seq[Expr]) extends Expr with CachingTyped {
    require(exprs.nonEmpty)

    protected def computeType(using s: Symbols): Type = {
      checkAllTypes(exprs.map(_.getType), IntegerType(), IntegerType())
    }
  }

  object SplitAnd {
    def apply(lhs: Expr, rhs: Expr): Expr = Annotated(And(lhs, rhs), Seq(SplitVC))

    def many(exprs: Expr*): Expr = {
      val conjuncts = exprs.filter(_ != BooleanLiteral(true))
      if (conjuncts.isEmpty) {
        if (exprs.isEmpty) BooleanLiteral(true) else exprs.head // exprs.head is `true` and might have a position
      }
      else if (conjuncts.size == 1) conjuncts.head
      else conjuncts.tail.foldLeft(conjuncts.head) {
        case (acc, expr) => SplitAnd(acc, expr).setPos(acc)
      }
    }

    def manyJoin(exprs: Seq[Expr]): Expr = many(exprs: _*)

    def unapply(expr: Expr): Option[Seq[Expr]] = expr match {
      case Annotated(And(exprs), flags) if flags.contains(SplitVC) => Some(exprs.toSeq)
      case _ => None
    }

  }

  /* Recursive Types */

  /** $encodingof of `ADTType(id,tps)<n>` */
  sealed case class RecursiveType(id: Identifier, tps: Seq[Type], index: Expr) extends Type {
    override protected def computeType(using s: Symbols): Type = ADTType(id, tps).getType
  }


  /** $encodingof of `Constructor<size>[tps](args)` */
  sealed case class SizedADT(id: Identifier, tps: Seq[Type], args: Seq[Expr], size: Expr) extends Expr with CachingTyped {
    def getConstructor(using s: Symbols) = s.getConstructor(id, tps)
    override protected def computeType(using s: Symbols): Type = ADT(id, tps, args).getType
  }

  /* Top type */

  /** $encodingof of Top (with underlying Inox type `tpe`) */
  sealed case class ValueType(tpe: Type) extends Type {
    override protected def computeType(using s: Symbols): Type = tpe.getType
  }

  /* Annotation on types */
  sealed case class AnnotatedType(tpe: Type, flags: Seq[Flag]) extends Type {
    override protected def computeType(using s: Symbols): Type = tpe.getType
  }

}
