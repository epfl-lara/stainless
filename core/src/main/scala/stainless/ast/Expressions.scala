/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

trait Expressions extends inox.ast.Expressions with inox.ast.Types { self: Trees =>

  /** Stands for an undefined Expr, similar to `???` or `null`
    *
    * During code generation, it gets compiled to `null`, or the 0 of the
    * respective type for value types.
    */
  case class NoTree(tpe: Type) extends Expr with Terminal {
    def getType(implicit s: Symbols): Type = tpe
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
  case class Error(tpe: Type, description: String) extends Expr with Terminal {
    def getType(implicit s: Symbols): Type = tpe
  }

  /** Precondition of an [[Expressions.Expr]]. Corresponds to the Stainless keyword *require*
    *
    * @param pred The precondition formula inside ``require(...)``
    * @param body The body following the ``require(...)``
    */
  case class Require(pred: Expr, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (pred.getType == BooleanType) body.getType
      else Untyped
    }
  }

  /** Postcondition of an [[Expressions.Expr]]. Corresponds to the Stainless keyword *ensuring*
    *
    * @param body The body of the expression. It can contain at most one [[Expressions.Require]] sub-expression.
    * @param pred The predicate to satisfy. It should be a function whose argument's type can handle the type of the body
    */
  case class Ensuring(body: Expr, pred: Lambda) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = pred.getType match {
      case FunctionType(Seq(bodyType), BooleanType) if s.isSubtypeOf(body.getType, bodyType) =>
        body.getType
      case _ =>
        Untyped
    }

    /** Converts this ensuring clause to the body followed by an assert statement */
    def toAssert(implicit s: Symbols): Expr = {
      val res = ValDef(FreshIdentifier("res", true), getType)
      Let(res, body, Assert(
        s.application(pred, Seq(res.toVariable)),
        Some("Postcondition failed @" + this.getPos),
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
  case class Assert(pred: Expr, error: Option[String], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (pred.getType == BooleanType) body.getType
      else Untyped
    }
  }


  /* First-class function specs */

  /** First class function precondition accessor
    * 
    * $encodingof `f.pre` */
  case class Pre(f: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = f.getType match {
      case FunctionType(from, to) => FunctionType(from, BooleanType).unveilUntyped
      case _ => Untyped
    }
  }


  /* Pattern-match expression */

  /** $encodingof `... match { ... }`
    *
    * '''cases''' should be nonempty. If you are not sure about this, you should use
    * FIXME
    *
    * @param scrutinee Expression to the left of the '''match''' keyword
    * @param cases A sequence of cases to match `scrutinee` against
    */
  case class MatchExpr(scrutinee: Expr, cases: Seq[MatchCase]) extends Expr with CachingTyped {
    require(cases.nonEmpty)

    protected def computeType(implicit s: Symbols): Type =
      s.leastUpperBound(cases.map(_.rhs.getType))
  }

  /** $encodingof `case pattern [if optGuard] => rhs`
    *
    * @param pattern The pattern just to the right of the '''case''' keyword
    * @param optGuard An optional if-condition just to the left of the `=>`
    * @param rhs The expression to the right of `=>`
    * @see [[Expressions.MatchExpr]]
    */
  case class MatchCase(pattern: Pattern, optGuard: Option[Expr], rhs: Expr) extends Tree {
    def expressions: Seq[Expr] = optGuard.toList :+ rhs
  }

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

  /** Pattern encoding `case binder: ct`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class InstanceOfPattern(binder: Option[ValDef], tpe: ADTType) extends Pattern {
    val subPatterns = Seq()
  }

  /** Pattern encoding `case _ => `, or `case binder => ` if [[binder]] is present */
  case class WildcardPattern(binder: Option[ValDef]) extends Pattern { // c @ _
    val subPatterns = Seq()
  }

  /** Pattern encoding `case binder @ ct(subPatterns...) =>`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class ADTPattern(binder: Option[ValDef], tpe: ADTType, subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding tuple pattern `case binder @ (subPatterns...) =>`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class TuplePattern(binder: Option[ValDef], subPatterns: Seq[Pattern]) extends Pattern

  /** Pattern encoding like `case binder @ 0 => ...` or `case binder @ "Foo" => ...`
    *
    * If [[binder]] is empty, consider a wildcard `_` in its place.
    */
  case class LiteralPattern[+T](binder: Option[ValDef], lit: Literal[T]) extends Pattern {
    val subPatterns = Seq()
  }

  /** A custom pattern defined through an object's `unapply` function */
  case class UnapplyPattern(binder: Option[ValDef], id: Identifier, tps: Seq[Type], subPatterns: Seq[Pattern]) extends Pattern {
    def tfd(implicit s: Symbols): TypedFunDef = s.getFunction(id, tps)

    // Hacky, but ok
    def optionType(implicit s: Symbols): ADTType = tfd.returnType.asInstanceOf[ADTType].getADT.root.toType
    
    private def optionChildren(implicit s: Symbols): Seq[TypedADTConstructor] =
      optionType.getADT.toSort.constructors.sortBy(_.fields.size)
    def noneType(implicit s: Symbols): ADTType = optionChildren.apply(0).toType
    def someType(implicit s: Symbols): ADTType = optionChildren.apply(1).toType

    def someSelector(implicit s: Symbols): Identifier = someType.getADT.toConstructor.fields.head.id

    /** Construct a pattern matching against unapply(scrut) (as an if-expression)
      *
      * @param scrut The scrutinee of the pattern matching
      * @param noneCase The expression that will happen if unapply(scrut) is None
      * @param someCase How unapply(scrut).get will be handled in case it exists
      */
    def patternMatch(scrut: Expr, noneCase: Expr, someCase: Expr => Expr)(implicit s: Symbols): Expr = {
      // We use this hand-coded if-then-else because we don't want to generate
      // match exhaustiveness checks in the program
      val binder = ValDef(FreshIdentifier("unap", true), optionType)
      Let(
        binder,
        FunctionInvocation(id, tps, Seq(scrut)),
        IfExpr(
          IsInstanceOf(binder.toVariable, someType),
          someCase(ADTSelector(AsInstanceOf(binder.toVariable, someType), someSelector)),
          noneCase
        )
      )
    }

    /** Inlined .get method */
    def get(scrut: Expr)(implicit s: Symbols): Expr = patternMatch(
      scrut,
      Error(optionType.tps.head, "None.get"),
      e => e
    )

    /** Selects Some.v field without type-checking.
      * Use ONLY in a context where scrut.isDefined returns true! */
    def getUnsafe(scrut: Expr)(implicit s: Symbols): Expr = ADTSelector(
      AsInstanceOf(FunctionInvocation(id, tps, Seq(scrut)), someType),
      someSelector
    )

    def isSome(scrut: Expr)(implicit s: Symbols): Expr =
      IsInstanceOf(FunctionInvocation(id, tps, Seq(scrut)), someType)
  }


  /* Array Operations */

  case class ArrayType(base: Type) extends Type

  /** $encodingof `Array(elems...)` */
  case class FiniteArray(elems: Seq[Expr], base: Type) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      checkParamTypes(elems.map(_.getType), List.fill(elems.size)(base), ArrayType(base).unveilUntyped)
    }
  }

  /** $encodingof `Array(elems...)` for huge arrays
    * @param elems   Map from an index to the corresponding element
    * @param default Default value for indexes not in the [[elems]] map
    * @param size    Array length
    */
  case class LargeArray(elems: Map[Int, Expr], default: Expr, size: Expr, base: Type) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (size.getType == Int32Type) {
        ArrayType(checkParamTypes(
          (default +: elems.values.toSeq).map(_.getType),
          List.fill(elems.size + 1)(base),
          base
        )).unveilUntyped
      } else {
        Untyped
      }
    }
  }

  /** $encodingof `array(index)` */
  case class ArraySelect(array: Expr, index: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type) => base
      case _ => Untyped
    }
  }

  /** $encodingof `array.updated(index, value)` */
  case class ArrayUpdated(array: Expr, index: Expr, value: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = (array.getType, index.getType) match {
      case (ArrayType(base), Int32Type) => ArrayType(s.leastUpperBound(base, value.getType)).unveilUntyped
      case _ => Untyped
    }
  }

  /** $encodingof `array.length` */
  case class ArrayLength(array: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = array.getType match {
      case ArrayType(_) => Int32Type
      case _ => Untyped
    }
  }
}
