import stainless.annotation.*
import stainless.lang.*
import stainless.lang.StaticChecks.*

/* Arithmetic expression typing */

object ArithLangSound:
  // Arithmetic expressions working on integers and booleans
  sealed trait Expr
  case class IntConst(c: BigInt) extends Expr
  case class BoolConst(b: Boolean) extends Expr
  case class ApplyOperator(e1: Expr, op: Operator, e2: Expr) extends Expr
  case class If(condition: Expr, thenBranch: Expr, elseBranch: Expr) extends Expr

  // Several example operators
  sealed trait Operator
  case class PlusOp() extends Operator
  case class MinusOp() extends Operator
  case class EqOp() extends Operator
  case class StrictAndOp() extends Operator // evaluates both arguments

  // Values are integer or boolean constants
  sealed trait Value
  case class IntVal(c: BigInt) extends Value
  case class BoolVal(b: Boolean) extends Value

  // Apply a given operator to a given value or give None if wrong types
  def evalVal(v1: Value, op: Operator, v2: Value): Option[Value] =
    (v1, op, v2) match
      case (IntVal(c1), PlusOp(), IntVal(c2)) => Some(IntVal(c1 + c2))
      case (IntVal(c1), MinusOp(), IntVal(c2)) => Some(IntVal(c1 - c2))
      case (BoolVal(b1), StrictAndOp(), BoolVal(b2)) => Some(BoolVal(b1 && b2))
      case (IntVal(c1), EqOp(), IntVal(c2)) => Some(BoolVal(c1 == c2))
      case (BoolVal(b1), EqOp(), BoolVal(b2)) => Some(BoolVal(b1 == b2))
      case _ => None[Value]() // Evaluation went wrong
      
  def eval(e: Expr): Option[Value] = // e need not type check, so we can get none
    decreases(e)
    e match
      case IntConst(c) => Some(IntVal(c))
      case BoolConst(b) => Some(BoolVal(b))
      case ApplyOperator(e1, op, e2) =>
        (eval(e1), eval(e2)) match
          case (Some(v1), Some(v2)) => evalVal(v1, op, v2)
          case _ => None[Value]()
      case If(c, e1, e2) =>
        eval(c) match
          case Some(BoolVal(b)) =>
            if b then eval(e1) else eval(e2)
          case _ => None[Value]()

  // Type expressions are Bool or Int
  sealed trait TypeExpr
  case class BoolType() extends TypeExpr
  case class IntType() extends TypeExpr
  
  // Infer the type of an expression. None means it does not type check
  def typeOf(e: Expr): Option[TypeExpr] =
    decreases(e)
    e match
      case IntConst(c) => Some(IntType())
      case BoolConst(b) => Some(BoolType())
      case ApplyOperator(e1, op, e2) =>
        (typeOf(e1), op, typeOf(e2)) match
          case (Some(IntType()), PlusOp(), Some(IntType())) => Some(IntType())
          case (Some(IntType()), MinusOp(), Some(IntType())) => Some(IntType())
          case (Some(IntType()), EqOp(), Some(IntType())) => Some(BoolType())
          case (Some(BoolType()), EqOp(), Some(BoolType())) => Some(BoolType())
          case (Some(BoolType()), StrictAndOp(), Some(BoolType())) => Some(BoolType())
          case _ => None[TypeExpr]()
      case If(c, e1, e2) =>
        (typeOf(c), typeOf(e1), typeOf(e2)) match
          case (Some(BoolType()), Some(t1), Some(t2)) => 
            if t1 == t2 then Some(t1) else None[TypeExpr]()
          case _ => None[TypeExpr]()

  // We can also assign types to values 
  def valTypeOf(v: Value): TypeExpr =
    v match
      case IntVal(c) => IntType()
      case BoolVal(b) => BoolType()
          
  // If we require an expression to have a type, then it always returns value.
  // This means that well-typed expressions do not get stuck.
  def evalTyped(e: Expr, @ghost t: TypeExpr): Value = {
    require(typeOf(e) == t)
    decreases(e)
    e match {
      case IntConst(c) => IntVal(c)
      case BoolConst(b) => BoolVal(b)
      case ApplyOperator(e1, op, e2) =>
        @ghost val t1 = typeOf(e1).get
        @ghost val t2 = typeOf(e2).get
        evalVal(evalTyped(e1, t1), op, evalTyped(e2, t2)).get
      case If(c, e1, e2) =>
        @ghost val t1 = typeOf(e1).get
        @ghost val t2 = typeOf(e2).get
        assert(t1 == t2)
        evalTyped(c, BoolType()) match
          case BoolVal(b) =>
            if b then evalTyped(e1, t1) else evalTyped(e2, t2)
    }
  }.ensuring(res => valTypeOf(res) == t) // the resulting value has the same type
  
  // Examples
  def e1: Expr = If(ApplyOperator(IntConst(2), EqOp(), IntConst(3)), IntConst(42), IntConst(7))
  def v1: Option[Value] = eval(e1)
  def e2: Expr = If(ApplyOperator(IntConst(2), EqOp(), BoolConst(true)), IntConst(42), IntConst(7))
  def v2: Option[Value] = eval(e2)     
  val t1: Option[TypeExpr] = typeOf(e1)
  val t2: Option[TypeExpr] = typeOf(e2)
  val tv1: Value = evalTyped(e1, t1.get)
  
end ArithLangSound

