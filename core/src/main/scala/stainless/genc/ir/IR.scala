/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import scala.collection.mutable.{ Set => MutableSet }

/*
 * A relatively immutable Intermediary Representation for the Scala to C conversion.
 *
 * NOTE ClassDef is mutable: subclasses get registered automatically to their parent (and mutate it).
 *      this means, when processing a class, you have to process the whole hierarchy if you don't
 *      want to lose a class definition. See for example how it's done in Class.refine.
 *
 * NOTE FunDef is mutable: in order to support recursive (mutually) functions, we need to be able
 *      to build a partial version of a FunDef, without a body, for App constructions. This
 *      partial FunDef has a null body.
 */
private[genc] sealed trait IR { ir =>

  // Add ability to pretty print the tree
  val printer = new IRPrinter[ir.type](ir)

  type Id = String
  type ClassHierarchy = Set[ClassDef]

  import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
  import Literals._
  import Operators._

  sealed abstract class Tree {
    override def toString: String = prettyString(0)

    def prettyString(indent: Int): String = printer(this)(using printer.Context(indent))
  }


  /****************************************************************************************************
   *                                                       Definition Tree                            *
   ****************************************************************************************************/
  sealed abstract class Def extends Tree

  case class Prog(
    decls: Seq[(Decl, Seq[DeclarationMode])],
    functions: Seq[FunDef],
    classes: Seq[ClassDef]
  ) {
    override def toString: String = printer(this)

    def size(using inox.Context): Int = {
      var result = 0
      new Visitor[ir.type](ir) {
        private val classCache = MutableSet[ClassDef]()
        override def visit(prog: Prog): Unit = { result += 1; super.visit(prog) }
        override def visit(fd: FunDef): Unit = { result += 1; super.visit(fd) }
        override def visit(cd: ClassDef): Unit = { result += 1; super.visit(cd) }
        override def visit(vd: ValDef): Unit = { result += 1; super.visit(vd) }
        override def visit(fb: FunBody): Unit = { result += 1; super.visit(fb) }
        override def visit(alloc: ArrayAlloc): Unit = { result += 1; super.visit(alloc) }
        override def visit(e: Expr): Unit = { result += 1; super.visit(e) }
        override def visit(typ: Type): Unit = { result += 1; super.visit(typ) }
      }.apply(this)
      result
    }
  }

  // Define a function body as either a regular AST or a manually defined
  // function using @cCode.function
  sealed abstract class FunBody
  case class FunDropped(isAccessor: Boolean) extends FunBody // for @cCode.drop; `isAccessor` is true for `val`'s to avoid parentheses
  case class FunBodyAST(body: Expr) extends FunBody
  case class FunBodyManual(headerIncludes: Seq[String], cIncludes: Seq[String], body: String) extends FunBody // NOTE `body` is actually the whole function!

  case class FunDef(id: Id, returnType: Type, ctx: Seq[ValDef], params: Seq[ValDef], var body: FunBody, isExported: Boolean, isPure: Boolean) extends Def {
    // Ignore body in equality/hash code; actually, use only the identifier. This is to prevent infinite recursion...
    override def equals(that: Any): Boolean = that match {
      case fd: FunDef => fd.id == id
      case _ => false
    }

    override def hashCode: Int = id.hashCode

    def toVal = FunVal(this)
  }

  case class ClassDef(id: Id, parent: Option[ClassDef], fields: Seq[ValDef], isAbstract: Boolean, isExported: Boolean, isPacked: Boolean) extends Def {
    require(
      // Parent must be abstract if any
      (parent forall { _.isAbstract }) &&
      // No fields on abstract classes (isAbstract --> fields.isEmpty)
      (!isAbstract || fields.isEmpty)
    )

    // Find the "toppest" parent
    val hierarchyTop: ClassDef = (parent map { _.hierarchyTop }) getOrElse this

    // To make the list of children correct by construction, subclasses
    // get automatically registered to their parent
    parent foreach { _ addChild this }

    // The list of children is kept directly here, in a mutable manner,
    // so that we can easily refine all the classes from a class hierarchy
    // at once, plus actually keep track of all of them.
    private var _children = Set[ClassDef]()

    private def addChild(child: ClassDef): Unit = {
      require(isAbstract)

      _children = _children + child
    }

    private def getAllChildren: Set[ClassDef] = _children flatMap { c => c.getAllChildren + c }

    def getDirectChildren: Set[ClassDef] = _children

    def getFullHierarchy: ClassHierarchy = hierarchyTop.getAllChildren + hierarchyTop

    def getHierarchyLeaves: Set[ClassDef] = getFullHierarchy filter { !_.isAbstract }

    def isHierarchyMutable: Boolean = getHierarchyLeaves exists { c => c.fields exists { _.isMutable } }

    // Get the type of a given field
    def getFieldType(fieldId: Id): Type = fields collectFirst { case ValDef(id, typ, _) if id == fieldId => typ } match {
      case Some(typ) => typ
      case None => sys.error(s"no such field $fieldId in class $id")
    }

    // Check whether `this` is the same as `other` or one of its subclasses.
    def <=(other: ClassDef): Boolean =  (this == other) || (other.getDirectChildren exists { this <= _ })
  }

  case class ValDef(id: Id, typ: Type, isVar: Boolean) extends Def {
    def getType: Type = typ
    def isArray: Boolean = typ.isArray
    def isMutable: Boolean = isVar || typ.isMutable
    def isReference: Boolean = typ.isReference
  }

  /****************************************************************************************************
   *                                                       Array Allocation                           *
   ****************************************************************************************************/
  // Represent an allocation point for arrays
  //
  // NOTE This ain't an Expr.
  sealed abstract class ArrayAlloc extends Tree {
    val typ: ArrayType
  }

  // For optimisation of ArrayAllocStatic: avoid processing useless bits in GenC to speed up things for big arrays.
  case object Zero

  // Allocate an array with a compile-time size
  case class ArrayAllocStatic(typ: ArrayType, length: Int, values: Either[Zero.type, Seq[Expr]]) extends ArrayAlloc {
    require(
      values match {
        case Left(z) =>
          // No empty array
          (length > 0) &&
          typ.base.isIntegral

        case Right(values) =>
          // The type of the values should match the type of the array elements
          (values forall { _.getType <= typ.base }) &&
          // The number of values should match the array size
          (length == values.length) &&
          // And empty arrays are forbidden
          (length > 0)
      }
    )
  }

  // Allocate a variable length array (VLA)
  //
  // NOTE Using "call by name" on `valueInit` means it will be fully evaluated at runtime as
  //      many times as the runtime value of `length`.
  case class ArrayAllocVLA(typ: ArrayType, length: Expr, valueInit: Expr) extends ArrayAlloc {
    require(
      // The length must evaluate to an integer (and should be positif but this not tested)
      (length.getType == PrimitiveType(Int32Type)) &&
      // The type of the array elements should match the type of the initialiation expression
      (valueInit.getType == typ.base)
    )
  }

  /****************************************************************************************************
   *                                                       Expression Tree                            *
   ****************************************************************************************************/
  sealed abstract class Expr extends Tree {
    // Get the type of the expressions
    final def getType: Type = this match {
      case Binding(vd) => vd.getType
      case c: Callable => c.typ
      case Block(exprs) => exprs.last.getType
      case MemSet(_, _, _) => NoType
      case SizeOf(_) => PrimitiveType(UInt32Type)
      case Decl(_, _) => NoType
      case App(fun, _, _) => fun.typ.ret
      case Construct(cd, _) => ClassType(cd)
      case ArrayInit(alloc) => alloc.typ
      case FieldAccess(objekt, fieldId) =>
        val ct = objekt.getType match {
          case ct: ClassType => ct
          case ReferenceType(ct: ClassType) => ct
          case _ => ???
        }
        ct.clazz getFieldType fieldId
      case ArrayAccess(array, _) => array.getType.asInstanceOf[ArrayType].base
      case ArrayLength(_) => PrimitiveType(Int32Type)
      case Assign(_, _) => NoType
      case BinOp(op, lhs, rhs) => op match {
        case _: ToIntegral => lhs.getType // same type as input
        case _: ToLogical => PrimitiveType(BoolType)
        case _ => ???
      }
      case UnOp(op, expr) => op match {
        case _: ToIntegral => expr.getType
        case _: ToLogical => PrimitiveType(BoolType)
        case _ => ???
      }
      case If(_, _) => NoType
      case IfElse(_, thenn, _) => thenn.getType // same as elze
      case While(_, _) => NoType
      case IsA(_, _) => PrimitiveType(BoolType)
      case AsA(_, ct) => ct
      case IntegralCast(_, newIntegralType) => PrimitiveType(newIntegralType)
      case Lit(lit) => PrimitiveType(lit.getPrimitiveType)
      case Ref(e) => ReferenceType(e.getType)
      case Deref(e) => e.getType.asInstanceOf[ReferenceType].t
      case Return(e) => e.getType
      case Assert(_) => NoType
      case Break => NoType
    }
  }

  // Access a variable
  case class Binding(vd: ValDef) extends Expr

  // Represents either a function definition or a function reference
  sealed abstract class Callable extends Expr {
    val typ: FunType
  }

  // References a FunDef directly
  case class FunVal(fd: FunDef) extends Callable {
    val typ = FunType(fd.ctx map { _.getType }, fd.params map { _.getType }, fd.returnType)
  }

  // Reference any function through an expression of function type
  case class FunRef(e: Expr) extends Callable {
    require(e.getType.isInstanceOf[FunType])
    val typ = e.getType.asInstanceOf[FunType]
  }

  // A non-empty sequence of expressions
  //
  // NOTE Nested Decl expressions have their ValDef available to following expressions in the block.
  //
  // NOTE Use factory helper `buildBlock` below to flatten blocks together.
  case class Block(exprs: Seq[Expr]) extends Expr {
    require(exprs.nonEmpty, "GenC IR blocks must be non-empty")
  }

  case class MemSet(pointer: Expr, value: Expr, size: Expr) extends Expr
  case class SizeOf(tpe: Type) extends Expr

  // A variable declaration with optional initialisation
  case class Decl(vd: ValDef, optInit: Option[Expr]) extends Expr

  // Invoke a function with context & regular arguments
  case class App(fun: Callable, extra: Seq[Expr], args: Seq[Expr]) extends Expr

  // Construct an object with the given field values
  case class Construct(cd: ClassDef, args: Seq[Expr]) extends Expr

  // Create an array on the stack
  case class ArrayInit(alloc: ArrayAlloc) extends Expr

  // Access a field of an object
  case class FieldAccess(objekt: Expr, fieldId: Id) extends Expr

  // Access an array element
  case class ArrayAccess(array: Expr, index: Expr) extends Expr

  // Probe the length of an array
  case class ArrayLength(array: Expr) extends Expr

  // Assign a value to a variable/field/array element
  case class Assign(lhs: Expr, rhs: Expr) extends Expr

  // Binary & Unary operators
  case class BinOp(op: BinaryOperator, lhs: Expr, rhs: Expr) extends Expr
  case class UnOp(op: UnaryOperator, expr: Expr) extends Expr

  // Control flow: If, If+Else & While
  case class If(cond: Expr, thenn: Expr) extends Expr
  case class IfElse(cond: Expr, thenn: Expr, elze: Expr) extends Expr
  case class While(cond: Expr, body: Expr) extends Expr

  // Type probindg + casting
  case class IsA(expr: Expr, ct: ClassType) extends Expr
  case class AsA(expr: Expr, ct: ClassType) extends Expr

  // Integer narrowing + widening casts
  case class IntegralCast(expr: Expr, newType: IntegralPrimitiveType) extends Expr {
    require(expr.getType.isIntegral)
  }

  // Literals
  case class Lit(lit: Literal) extends Expr

  // Referencing/Dereferencing, i.e. take address of expression or deference pointer
  case class Ref(e: Expr) extends Expr {
    require(!e.getType.isInstanceOf[ReferenceType])
  }
  case class Deref(e: Expr) extends Expr {
    require(e.getType.isInstanceOf[ReferenceType])
  }

  case class Assert(e: Expr) extends Expr

  case class Return(e: Expr) extends Expr

  case object Break extends Expr


  /****************************************************************************************************
   *                                                       Expression Helpers                         *
   ****************************************************************************************************/

  // Flatten blocks together
  def buildBlock(exprs: Seq[Expr]): Block = {
    require(exprs.nonEmpty)

    val block = exprs.foldLeft(Seq[Expr]()) {
      case (acc, e) => e match {
        case Block(exprs) => acc ++ exprs
        case expr => acc :+ expr
      }
    }

    Block(block)
  }

  val False = Lit(BoolLit(false))
  val True = Lit(BoolLit(true))


  /****************************************************************************************************
   *                                                       Type Tree                                  *
   ****************************************************************************************************/
  sealed abstract class Type extends Tree {
    def isUnitType: Boolean = this match {
      case PrimitiveType(UnitType) => true
      case _ => false
    }

    def isArray: Boolean = this match {
      case ArrayType(_, _) => true
      case _ => false
    }

    def isFixedArray: Boolean = this match {
      case ArrayType(_, Some(_)) => true
      case _ => false
    }

    def containsArray: Boolean = this match {
      case PrimitiveType(_) => false

      // Functions currently do not capture anything
      case FunType(_, _, _) => false

      // We do *NOT* answer this question for the whole class hierarchy!
      case ClassType(clazz) => clazz.fields exists { _.getType.containsArray }

      case ArrayType(_, _) => true
      case ReferenceType(t) => t.containsArray

      // We assume typeDefs don't contain arrays
      case TypeDefType(_, _, _, _) => false

      case DroppedType => false

      case NoType => false
    }

    def isMutable: Boolean = this match {
      case PrimitiveType(_) => false

      case FunType(_, _, _) => false

      // We do answer this question for the whole class hierarchy!
      case ClassType(clazz) => clazz.isHierarchyMutable

      case ArrayType(_, _) => true
      case ReferenceType(_) => true
      case TypeDefType(_, _, _, _) => false // This is our assumption
      case DroppedType => false
      case NoType => false
    }

    def isReference: Boolean = this match {
      case ReferenceType(_) => true
      case _ => false
    }

    // Check that `other` is equivalent to `this` or is a super class of `this`
    def <=(other: Type): Boolean = (this == other) || ((this, other) match {
      case (ClassType(cd1), ClassType(cd2)) => cd1 <= cd2
      case _ => false
    })

    // Category test
    def isLogical: Boolean = this match {
      case PrimitiveType(pt) => pt.isLogical
      case _ => false
    }

    def isIntegral: Boolean = this match {
      case PrimitiveType(pt) => pt.isIntegral
      case _ => false
    }
  }

  // Type representing Int32, Boolean, ...
  case class PrimitiveType(primitive: PT) extends Type

  // Type representing a function
  case class FunType(ctx: Seq[Type], params: Seq[Type], ret: Type) extends Type

  // Type representing an abstract or case class, as well as tuples
  case class ClassType(clazz: ClassDef) extends Type

  // Represents the type of an array of `base`, optionally with a fixed length
  case class ArrayType(base: Type, length: Option[Int]) extends Type

  // A ReferenceType is just a marker for references, it acts like the underlying type
  case class ReferenceType(t: Type) extends Type

  // For @cCode.typedef
  case class TypeDefType(original: Id, alias: Id, include: Option[String], exprt: Boolean) extends Type

  // For @cCode.drop
  // TODO Drop them completely, and reject input program if one dropped type is actually used!
  case object DroppedType extends Type

  // For when an expressions has no specific type
  case object NoType extends Type


  /****************************************************************************************************
   *                                                       Type Helpers                               *
   ****************************************************************************************************/

  def repId(typ: Type): Id = typ match {
    case PrimitiveType(pt) => pt match {
      case CharType => "char"
      case Int8Type => "int8"
      case Int16Type => "int16"
      case Int32Type => "int32"
      case Int64Type => "int64"
      case UInt8Type => "uint8"
      case UInt16Type => "uint16"
      case UInt32Type => "uint32"
      case UInt64Type => "uint64"
      case BoolType => "bool"
      case UnitType => "unit"
      case StringType => "string"
    }
    case FunType(ctx, params, ret) =>
      val ctxRep = ctx map repId mkString "_"
      val paramsRep = params map repId mkString "_"
      "function_" + ctx + "_" + params + "_" + repId(ret)
    case ClassType(clazz) => clazz.id
    case ArrayType(base, None) => "array_" + repId(base)
    case ArrayType(base, Some(length)) => s"${repId(base)}[$length]"
    case ReferenceType(t) => "ref_" + repId(t)
    case TypeDefType(original, _, _, _) => original
    case DroppedType => ??? // Building an id on dropped type is illegal!
    case NoType => ??? // Idem for NoType
  }

}

object IRs {
  object SIR extends IR
  object CIR extends IR
  object RIR extends IR
  object NIR extends IR
  object LIR extends IR
}

