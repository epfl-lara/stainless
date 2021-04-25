/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import ir.Operators._
import ir.PrimitiveTypes._
import ir.Literals._

/*
 * Here are defined classes used to represent AST of C programs.
 *
 * NOTE on char and string:
 *      because the C character and string literals encoding sets are
 *      highly dependent on platforms and compilers, only basic single-byte
 *      characters from the ASCII set are supported at the moment.
 *
 *      Details on such literals can be found in the C99 standard in §3.7,
 *      §6.4.4.4 and §6.4.5, and more.
 *
 * NOTE Because types in union shall not be partially defined we need to
 *      keep track of the dependencies between Struct's and Union's in a
 *      Prog's types. We do this lazily by requiring the `types` field to
 *      be sorted appropriately. Also, it shall only contains Struct's
 *      and Union's, no other kind of Type's.
 */
object CAST { // C Abstract Syntax Tree

  sealed abstract class Tree


  /* ----------------------------------------------------- Definitions  ----- */
  abstract class Def extends Tree

  case class Include(file: String) extends Def {
    require(file.nonEmpty && isASCII(file))
  }

  case class Prog(
    includes: Set[Include],
    typeDefs: Set[TypeDef],
    enums: Set[Enum],
    types: Seq[DataType], // Both structs and unions, order IS important! See NOTE above.
    functions: Set[Fun]
  ) extends Def {
    require(types.length == types.distinct.length) // no duplicates in `types`
  }

  // Manually defined function through the cCode.function annotation have a string
  // for signature+body instead of the usual Stmt AST exclusively for the body
  case class Fun(id: Id, returnType: Type, params: Seq[Var], body: Either[Block, String], export: Boolean) extends Def

  case class Id(name: String) extends Def {
    // TODO add check on name's domain for conformance

    // `|` is used as the margin delimiter and can cause trouble in some situations,
    // for example when name start with a `|`.
    def fixMargin =
      if (name.size > 0 && name(0) == '|') "| " + name
      else name
  }

  case class Var(id: Id, typ: Type) extends Def


  /* ------------------------------------------------------------ Types ----- */
  abstract class Type extends Tree

  abstract class DataType extends Type {
    val id: Id
    val fields: Seq[Var]
  }

  case class TypeDef(orig: Id, alias: Id) extends Type
  case class Primitive(pt: PrimitiveType) extends Type
  case class Pointer(base: Type) extends Type

  case class FunType(ret: Type, params: Seq[Type]) extends Type

  case class Struct(id: Id, fields: Seq[Var]) extends DataType {
    require(fields.nonEmpty)
  }

  case class Union(id: Id, fields: Seq[Var]) extends DataType {
    require(fields.nonEmpty)
  }

  case class Enum(id: Id, literals: Seq[EnumLiteral]) extends Type {
    require(literals.nonEmpty)
  }


  /* ------------------------------------------------------ Expressions ----- */
  abstract class Expr extends Tree

  case class Block(exprs: Seq[Expr]) extends Expr // Can be empty

  case class Lit(lit: Literal) extends Expr

  case class EnumLiteral(id: Id) extends Expr

  case class Decl(id: Id, typ: Type) extends Expr

  case class DeclInit(id: Id, typ: Type, value: Expr) extends Expr {
    require(value.isValue)
  }

  case class DeclArrayStatic(id: Id, base: Type, length: Int, values: Seq[Expr]) extends Expr {
    require(values forall { _.isValue })
  }

  case class DeclArrayVLA(id: Id, base: Type, length: Expr, defaultExpr: Expr) extends Expr {
    require(
      length.isValue &&
      // length.getType == Primitive(Int32Type) &&
      defaultExpr.isValue
    )
  }

  // Initialise all the fields of a struct, in the same order as they are declared.
  case class StructInit(struct: Struct, values: Seq[Expr]) extends Expr {
    require(
      values.length == struct.fields.length && // Allow only explicit initialisation.
      (values forall { _.isValue })
    )
  }

  // Initialise one of the fields of the union
  case class UnionInit(union: Union, fieldId: Id, value: Expr) extends Expr {
    require(
      (union.fields exists { _.id == fieldId }) && // The requested field must exists.
      value.isValue // &&
      // (union.fields forall { f => f.id != fieldId || f.getType == value.getType })
    )
  }

  case class Call(callable: Expr, args: Seq[Expr]) extends Expr {
    require(args forall { _.isValue })
  }

  case class Binding(id: Id) extends Expr

  case class FieldAccess(objekt: Expr, fieldId: Id) extends Expr {
    require(
      objekt.isValue //&&
      /*
       * (objekt.getType match {
       *   case dt: DataType => dt.fields exists { _.id == fieldId }
       *   case _ => false
       * })
       */
    )
  }

  case class ArrayAccess(array: Expr, index: Expr) extends Expr {
    require(
      array.isValue // &&
      // array.getType.isInstanceOf[ArrayType]
    )
  }

  case class Ref(e: Expr) extends Expr {
    require(e.isValue)
  }

  case class Deref(e: Expr) extends Expr {
    require(e.isValue)
  }

  case class Assign(lhs: Expr, rhs: Expr) extends Expr {
    require(
      // lhs.getType == rhs.getType &&
      lhs.isValue && rhs.isValue
    )
  }

  case class BinOp(op: BinaryOperator, lhs: Expr, rhs: Expr) extends Expr {
    require(lhs.isValue && rhs.isValue)
  }

  case class UnOp(op: UnaryOperator, expr: Expr) extends Expr {
    require(expr.isValue)
  }

  case class If(cond: Expr, thenn: Block) extends Expr {
    require(
      cond.isValue // &&
      // cond.getType == Primitive(BoolType)
    )
  }

  case class IfElse(cond: Expr, thenn: Block, elze: Block) extends Expr {
    require(
      cond.isValue // &&
      // cond.getType == Primitive(BoolType)
    )
  }

  case class While(cond: Expr, body: Block) extends Expr {
    require(
      cond.isValue // &&
      // cond.getType == Primitive(BoolType)
    )
  }

  case object Break extends Expr

  case class Return(value: Expr) extends Expr {
    require(value.isValue)
  }

  // This can represent any C cast, however unsafe it can be.
  case class Cast(expr: Expr, typ: Type) extends Expr


  /* ---------------------------------------------------------- Helpers ----- */
  // Flatten blocks together and remove `()` literals
  def buildBlock(exprs: Seq[Expr]): Block = {
    val block = (exprs filterNot isUnitLit).foldLeft(Seq.empty[Expr]) {
      case (acc, e) => e match {
        case Block(exprs) => acc ++ exprs
        case expr => acc :+ expr
      }
    }

    Block(block)
  }

  def buildBlock(expr: Expr): Block = buildBlock(Seq(expr))

  object FreshId {
    private val counter = new utils.UniqueCounter[String]()

    def apply(prefix: String): Id = {
      val idx = counter.next(prefix)
      Id("stainless_" + prefix + "_" + idx)
    }
  }

  val True = Lit(BoolLit(true))


  /* ---------------------------------------------------------- Details ----- */
  // String & char limitations, see NOTE above
  private def isASCII(c: Char): Boolean = { c >= 0 && c <= 127 }
  private def isASCII(s: String): Boolean = s forall isASCII

  private def isUnitLit(e: Expr): Boolean = e match {
    case Lit(UnitLit) => true
    case _ => false
  }


  /* ---------------------------------------------- Sanitisation Helper ----- */
  private implicit class ExprValidation(e: Expr) {
    def isValue = e match {
      case _: Binding | _: Lit | _: EnumLiteral | _: StructInit |
           _: UnionInit | _: Call | _: FieldAccess | _: ArrayAccess |
           _: Ref | _: Deref | _: BinOp | _: UnOp | _: Cast => true
      case _ => false
    }

    def isReference = e match {
      case _: Ref => true
      case _ => false
    }
  }

}
