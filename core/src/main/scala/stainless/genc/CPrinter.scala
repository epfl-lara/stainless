/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import CAST._
import CPrinterHelpers._
import ir.PrimitiveTypes._
import ir.Literals._

class CPrinter(val sb: StringBuffer = new StringBuffer) {
  override def toString = sb.toString

  def print(tree: Tree) = pp(tree)(PrinterContext(indent = 0, printer = this, previous = None, current = tree))

  private[genc] def pp(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Prog(includes, typedefs0, enums0, types, functions0) =>
      // We need to convert Set to Seq in order to use nary.
      val typedefs = typedefs0.toSeq
      val enums = enums0.toSeq.sortBy(_.id.name)
      val functions = functions0.toSeq.sortBy(_.id.name)

      c"""|/* ------------------------------------ includes ----- */
          |
          |${nary(buildIncludes(includes), sep = "\n")}
          |
          |/* -------------------------------- type aliases ----- */
          |
          |${nary(typedefs map TypedefDecl, sep = "\n")}
          |
          |/* --------------------------------------- enums ----- */
          |
          |${nary(enums map EnumDef, sep = "\n\n")}
          |
          |/* ----------------------- data type definitions ----- */
          |
          |${nary(types map TypeDef, sep = "\n\n")}
          |
          |/* ----------------------- function declarations ----- */
          |
          |${nary(functions map FunDecl, sep = "\n")}
          |
          |/* ------------------------ function definitions ----- */
          |
          |${nary(functions, sep = "\n\n")}
          |"""

    // Manually defined function
    case Fun(id, _, _, Right(function)) =>
      val fun = function.replaceAllLiterally("__FUNCTION__", id.name)
      c"$fun"

    // Auto-generated function
    case fun @ Fun(_, _, _, Left(body)) =>
      c"""|${FunSign(fun)} {
          |    $body
          |}"""

    case Id(name) => c"$name"

    case Var(id, typ) => c"${TypeId(typ, id)}"

    case Typedef(orig, _) => c"$orig"

    case Primitive(pt) => pt match {
      case CharType => c"char"

      case Int8Type => c"int8_t"
      case Int16Type => c"int16_t"
      case Int32Type => c"int32_t"
      case Int64Type => c"int64_t"

      case UInt8Type => c"uint8_t"
      case UInt16Type => c"uint16_t"
      case UInt32Type => c"uint32_t"
      case UInt64Type => c"uint64_t"

      case BoolType => c"bool"
      case UnitType => c"void"
      case StringType => c"char*"
    }

    case FunType(ret, params) => ??? /* This is probably not what you want! */
    // The issue is that c"$ret (*)($params)" would be wrong in most contexts.
    // Instead, one has to add a variable name right after the `*`.

    case Pointer(base) => c"$base*"

    case Struct(id, _) => c"$id"

    case Union(id, _) => c"$id"

    case Enum(id, _) => c"$id"

    case Block(exprs) =>
      for { (e, i) <- exprs.zipWithIndex } {
        c"$e"
        e match {
          case _: If | _: IfElse | _: While => ()
          case _ => c";"
        }
        if (i < exprs.length - 1) // new line, except for the last expression
          c"""|
              |"""
      }

    case Lit(lit) => c"$lit"

    case EnumLiteral(lit) => c"$lit"

    case Decl(id, typ) => c"${TypeId(typ, id)}"

    case DeclInit(id, typ, value) => c"${TypeId(typ, id)} = $value"

    // TODO Visual "optimisation" can be made here if all values are zeros
    case DeclArrayStatic(id, base, length, values) =>
      c"$base $id[$length] = { ${nary(values, sep = ", ")} }"

    case DeclArrayVLA(id, base, length, defaultExpr) =>
      val i = FreshId("i")
      c"""|$base $id[$length];
          |${Decl(i, Primitive(Int32Type))};
          |for ($i = 0; $i < $length; ++$i) {
          |    $id[$i] = $defaultExpr;
          |}"""

    case StructInit(struct, values) =>
      val args = struct.fields zip values
      c"(${struct.id}) { ${nary(args map { case (Var(id, _), arg) => FieldInit(id, arg) }, sep = ", ")} }"

    case UnionInit(union, fieldId, value) =>
      c"(${union.id}) { ${FieldInit(fieldId, value)} }"

    case Call(id, args) => c"$id(${nary(args)})"

    case Binding(id) => c"$id"

    case FieldAccess(Deref(objekt), fieldId) => c"$objekt->$fieldId"

    case FieldAccess(objekt, fieldId) => c"$objekt.$fieldId"

    case ArrayAccess(array, index) => c"$array[$index]"

    case Ref(e) => c"&$e"

    case Deref(e) => optP { c"*$e" }

    case Assign(lhs, rhs) => c"$lhs = $rhs"

    case BinOp(op, lhs, rhs) => optP { c"$lhs $op $rhs" }

    case UnOp(op, expr) => optP { c"$op$expr" }

    case If(cond, thenn) =>
      c"""|if ($cond) {
          |    $thenn
          |}"""

    case IfElse(cond, thenn, Block(Seq(secondIf @ If(_, _)))) =>
      c"""|if ($cond) {
          |    $thenn
          |} else $secondIf"""

    case IfElse(cond, thenn, Block(Seq(secondIf @ IfElse(_, _, _)))) =>
      c"""|if ($cond) {
          |    $thenn
          |} else $secondIf"""

    case IfElse(cond, thenn, elze) =>
      c"""|if ($cond) {
          |    $thenn
          |} else {
          |    $elze
          |}"""

    case While(cond, body) =>
      c"""|while ($cond) {
          |    $body
          |}"""

    case Break => c"break"

    case Return(value) => c"return $value"

    case Cast(expr, typ) => optP { c"($typ)$expr" }
  }

  private[genc] def pp(wt: WrapperTree)(implicit ctx: PrinterContext): Unit = wt match {
    case StaticStorage(id) if id.name == "main" => /* Nothing */
    case StaticStorage(_) => c"static"

    case TypeId(FunType(ret, params), id) => c"$ret (*$id)($params)"
    case TypeId(typ, id) => c"$typ $id"

    case FunSign(Fun(id, FunType(retret, retparamTypes), params, _)) =>
      c"${StaticStorage(id)} $retret (*$id(${FunSignParams(params)}))(${FunSignParams(retparamTypes)})"

    case FunSign(Fun(id, returnType, params, _)) =>
      c"${StaticStorage(id)} $returnType $id(${FunSignParams(params)})"

    case FunSignParams(Seq()) => c"void"
    case FunSignParams(params) => c"${nary(params)}"

    case FunDecl(f) => c"${FunSign(f)};"

    case TypedefDecl(Typedef(original, alias)) => c"typedef $alias $original;"

    case EnumDef(Enum(id, literals)) =>
      c"""|typedef enum {
          |  ${nary(literals, sep = ",\n")}
          |} $id;"""

    case TypeDef(t: DataType) =>
      val kind = t match {
        case _: Struct => "struct"
        case _: Union => "union"
      }
      c"""|typedef $kind {
          |  ${nary(t.fields, sep = ";\n", closing = ";")}
          |} ${t.id};"""

    case FieldInit(id, value) => c".$id = $value"
  }


  /** Hardcoded list of required include files from C standard library **/
  private lazy val includes_ = Set("assert.h", "stdbool.h", "stdint.h", "stddef.h") map Include

  private def buildIncludes(includes: Set[Include]): Seq[String] =
    (includes_ ++ includes).toSeq sortBy { _.file } map { i => s"#include <${i.file}>" }


  /** Wrappers to distinguish how the data should be printed **/
  private[genc] sealed abstract class WrapperTree
  private case class StaticStorage(id: Id) extends WrapperTree
  private case class TypeId(typ: Type, id: Id) extends WrapperTree
  private case class FunSign(f: Fun) extends WrapperTree

  // Here, params is expected to be of Type or Var.
  private case class FunSignParams(params: Seq[Tree]) extends WrapperTree

  private case class FunDecl(f: Fun) extends WrapperTree
  private case class TypedefDecl(td: Typedef) extends WrapperTree
  private case class EnumDef(u: Enum) extends WrapperTree
  private case class TypeDef(t: DataType) extends WrapperTree // This is not Typedef!!!
  private case class FieldInit(id: Id, value: Expr) extends WrapperTree


  /** Special helpers for pretty parentheses **/
  private def optP(body: => Any)(implicit ctx: PrinterContext) = {
    if (requiresParentheses(ctx.current, ctx.previous)) {
      sb.append("(")
      body
      sb.append(")")
    } else {
      body
    }
  }

  private def requiresParentheses(current: Tree, previous: Option[Tree]): Boolean = (current, previous) match {
    case (_, None) => false
    case (_, Some(_: DeclInit | _: Call | _: ArrayAccess | _: If | _: IfElse | _: While | _: Return | _: Assign)) => false
    case (Operator(precedence1), Some(Operator(precedence2))) if precedence1 < precedence2 => false
    case (_, _) => true
  }

  private object Operator {
    def unapply(tree: Tree): Option[Int] = tree match {
      case BinOp(op, _, _) => Some(op.precedence)
      case UnOp(op, _) => Some(op.precedence)
      case _ => None
    }
  }
}
