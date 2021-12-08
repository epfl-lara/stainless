/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import CAST._
import CPrinterHelpers._
import ir.PrimitiveTypes._
import ir.Literals._

class CPrinter(
  hFileName: String,
  // `printC` is true when we print the *.c file, false when we print the *.h file
  printC: Boolean,
  headerDependencies: Set[Type],
  gencIncludes: Seq[String],
  val sb: StringBuffer = new StringBuffer,
) {
  def print(tree: Tree) = pp(tree)(using PrinterContext(indent = 0, printer = this, previous = None, current = tree))

  private def purity(isPure: Boolean): String = if (isPure) "STAINLESS_FUNC_PURE " else ""

  private[genc] def pp(tree: Tree)(using PrinterContext): Unit = tree match {
    case Prog(headerIncludes, cIncludes, decls, typeDefs0, enums0, types, functions0) =>
      // We need to convert Set to Seq in order to use nary.
      val typeDefs = typeDefs0.toSeq
      val enums = enums0.toSeq.sortBy(_.id.name)
      val functions = functions0.toSeq.sortBy(_.id.name).filter(_.body != Right(""))

      def separator(s: String) = {
        "/* " + "-" * (43 - s.length) + " " + s + " " + "----- */\n\n"
      }

      if (printC) {
        c"""|/* --------------------------- GenC requirements ----- */
            |
            |#include <limits.h>
            |#if (__STDC_VERSION__ < 199901L) || (CHAR_BIT != 8)
            |#error "Your compiler does not meet the minimum requirements of GenC. Please see"
            |#error "https://epfl-lara.github.io/stainless/genc.html#requirements for more details."
            |#endif
            |
            |/* ---------------------------- include header ------- */
            |
            |#include "${hFileName}"
            |
            |${nary(
              buildIncludes(cIncludes),
              opening = separator("includes"),
              closing = "\n\n",
              sep = "\n")
            }
            |${nary(
              typeDefs.filter(!headerDependencies.contains(_)) map TypeDefDecl.apply,
              opening = separator("type aliases"),
              closing = "\n\n",
              sep = "\n")
             }
            |${nary(
              enums.filter(!headerDependencies.contains(_)) map EnumDef.apply,
              closing = "\n\n",
              opening = separator("enums"),
              sep = "\n\n")
             }
            |${nary(
              types.filter(!headerDependencies.contains(_)) map DataTypeDecl.apply,
              opening = separator("data type definitions"),
              closing = "\n\n",
              sep = "\n\n")
             }
            |${nary(
              decls.filter(decl => !decl._2.contains(External) && !decl._2.contains(Define)).map { case (decl, modes) =>
                modes.foldLeft(TTree(decl) : WrapperTree) {
                  case (acc, Static) => StaticStorage(acc)
                  case (acc, Volatile) => VolatileStorage(acc)
                  case (acc, _) => acc
                }
              },
              opening = separator("global variables"),
              closing = ";\n\n",
              sep = ";\n")
             }
            |${nary(
              functions.filter(!_.isExported) map FunDecl.apply,
              opening = separator("function declarations"),
              closing = "\n\n",
              sep = "\n")
             }
            |${nary(
              functions,
              opening = separator("function definitions"),
              sep = "\n\n")
             }
            |"""
      } else {
        val capitalized = hFileName.toUpperCase.map { c =>
          if (c.isLetterOrDigit) c
          else "_"
        }.mkString

        c"""|#ifndef __${capitalized}__
            |#define __${capitalized}__
            |
            |/* --------------------------- preprocessor macros ----- */
            |
            |#define STAINLESS_FUNC_PURE
            |#if defined(__cplusplus)
            |#undef STAINLESS_FUNC_PURE
            |#define STAINLESS_FUNC_PURE _Pragma("FUNC_IS_PURE;")
            |#elif __GNUC__>=3
            |#undef STAINLESS_FUNC_PURE
            |#define STAINLESS_FUNC_PURE __attribute__((__pure__))
            |#elif defined(__has_attribute)
            |#if __has_attribute(pure)
            |#undef STAINLESS_FUNC_PURE
            |#define STAINLESS_FUNC_PURE __attribute__((__pure__))
            |#endif
            |#endif
            |
            |${nary(
              decls.filter(decl => decl._2.contains(Define)).map { case (decl, _) =>
                DefineMacro(TTree(decl))
              },
              opening = separator("macros"),
              closing = "\n\n",
              sep = "\n")
             }
            |${nary(
              buildIncludes(headerIncludes),
              opening = separator("includes"),
              closing = "\n\n",
              sep = "\n")
            }
            |${nary(
              typeDefs.filter(headerDependencies.contains) map TypeDefDecl.apply,
              opening = separator("type aliases"),
              closing = "\n\n",
              sep = "\n")
             }
            |${nary(
              enums.filter(headerDependencies.contains) map EnumDef.apply,
              closing = "\n\n",
              opening = separator("enums"),
              sep = "\n\n")
             }
            |${nary(
              types.filter(headerDependencies.contains) map DataTypeDecl.apply,
              opening = separator("data type definitions"),
              closing = "\n\n",
              sep = "\n\n")
             }
            |${nary(
              decls.filter(decl => decl._2.contains(Export) && !decl._2.contains(Define)).map { case (decl, modes) =>
                ExternDecl(modes.foldLeft(TTree(decl.copy(optValue = None)) : WrapperTree) {
                  case (acc, Static) => StaticStorage(acc)
                  case (acc, Volatile) => VolatileStorage(acc)
                  case (acc, _) => acc
                }) : WrapperTree
              },
              opening = separator("global variables"),
              closing = ";\n\n",
              sep = ";\n")
             }
            |${nary(
              functions.filter(_.isExported) map FunDecl.apply,
              opening = separator("function declarations"),
              sep = "\n")
             }
            |
            |#endif
            |"""
      }

    // Manually defined function
    case Fun(id, _, _, Right(function), _, _) =>
      val fun = function.replace("__FUNCTION__", id.name)
      c"$fun"

    case fun @ Fun(_, _, _, Left(body), _, isPure) =>
      c"""|${FunSign(fun)} {
          |    $body
          |}"""

    case Id(name) => c"$name"

    case Var(id, typ) => c"${TypeId(typ, id)}"

    case TypeDef(orig, _, _) => c"$orig"

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


    case MemSet(pointer, value, size) => c"memset($pointer, $value, $size)"
    case SizeOf(tpe) => c"sizeof($tpe)"

    case Pointer(base) => c"$base*"

    case Struct(id, _, _, _) => c"$id"

    case Union(id, _, _) => c"$id"

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

    case Decl(id, typ, None) => c"${TypeId(typ, id)}"

    case Decl(id, typ, Some(value)) => c"${TypeId(typ, id)} = $value"

    // TODO Visual "optimisation" can be made here if all values are zeros
    case DeclArrayStatic(id, base, length, values) =>
      c"$base $id[$length] = { ${nary(values, sep = ", ")} }"

    case ArrayStatic(_, values) =>
      c"{ ${nary(values, sep = ", ")} }"

    case DeclArrayVLA(id, base, length, defaultExpr) =>
      val i = FreshId("i")
      c"""|$base $id[$length];
          |${Decl(i, Primitive(Int32Type), None)};
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

    case Return(Lit(UnitLit)) => c"return"
    case Return(value) => c"return $value"
    case Assert(expr) => c"assert($expr)"

    case Cast(expr, typ) => optP { c"($typ)$expr" }

    case _ => throw new Exception(s"GenC cannot print tree (of class ${tree.getClass})")
  }

  private[genc] def pp(wt: WrapperTree)(using PrinterContext): Unit = wt match {
    case TTree(t) => pp(t)

    case StaticStorage(decl) => c"static $decl"
    case ExternDecl(decl) => c"extern $decl"
    case VolatileStorage(decl) => c"volatile $decl"
    case DefineMacro(TTree(Decl(id, _, Some(value)))) => c"#define $id $value"

    case TypeId(FunType(ret, params), id) => c"$ret (*$id)($params)"
    case TypeId(FixedArrayType(base, length), id) => c"$base $id[$length]"
    case TypeId(typ, id) => c"$typ $id"

    case FunSign(Fun(id, _, _, Right(s), _, isPure)) =>
      val header = s.takeWhile(_ != ')').replace("__FUNCTION__", id.name)
      c"${purity(isPure)}$header)"

    case FunSign(Fun(id, FunType(retret, retparamTypes), params, _, _, isPure)) =>
      c"${purity(isPure)}$retret (*$id(${FunSignParams(params)}))(${FunSignParams(retparamTypes)})"

    case FunSign(Fun(id, returnType, params, _, _, isPure)) =>
      c"${purity(isPure)}$returnType $id(${FunSignParams(params)})"

    case FunSignParams(Seq()) => c"void"
    case FunSignParams(params) => c"${nary(params)}"

    case FunDecl(f) => c"${FunSign(f)};"

    case TypeDefDecl(TypeDef(original, alias, _)) => c"typedef $alias $original;"

    case EnumDef(Enum(id, literals)) =>
      c"""|typedef enum {
          |  ${nary(literals, sep = ",\n")}
          |} $id;"""

    case DataTypeDecl(u: Union) =>
      c"""|typedef union {
          |  ${nary(u.fields, sep = ";\n", closing = ";")}
          |} ${u.id};"""

    case DataTypeDecl(s: Struct) if s.isPacked =>
      c"""|#pragma pack(1)
          |typedef struct {
          |  ${nary(s.fields, sep = ";\n", closing = ";")}
          |} ${s.id};
          |#pragma pack()"""

    case DataTypeDecl(s: Struct) =>
      c"""|typedef struct {
          |  ${nary(s.fields, sep = ";\n", closing = ";")}
          |} ${s.id};"""

    case FieldInit(id, value) => c".$id = $value"

    case _ => throw new Exception(s"GenC cannot print wrapped tree $wt (of class ${wt.getClass})")
  }


  /** Hardcoded list of required include files from C standard library **/
  private lazy val includes_ = Set("assert.h", "stdbool.h", "stdint.h", "stddef.h", "string.h") map Include.apply

  private def buildIncludes(includes: Set[Include]): Seq[String] =
    (includes_ ++ includes).toSeq.sortBy(_.file).map(i => s"#include <${i.file}>") ++
    gencIncludes.map(f => s"""#include "$f"""")

  /** Wrappers to distinguish how the data should be printed **/
  private[genc] sealed abstract class WrapperTree
  private case class TTree(t: Tree) extends WrapperTree
  private case class ExternDecl(wt: WrapperTree) extends WrapperTree
  private case class DefineMacro(wt: WrapperTree) extends WrapperTree
  private case class StaticStorage(wt: WrapperTree) extends WrapperTree
  private case class VolatileStorage(wt: WrapperTree) extends WrapperTree
  private case class TypeId(typ: Type, id: Id) extends WrapperTree
  private case class FunSign(f: Fun) extends WrapperTree

  // Here, params is expected to be of Type or Var.
  private case class FunSignParams(params: Seq[Tree]) extends WrapperTree

  private case class FunDecl(f: Fun) extends WrapperTree
  private case class TypeDefDecl(td: TypeDef) extends WrapperTree
  private case class EnumDef(u: Enum) extends WrapperTree
  private case class DataTypeDecl(t: DataType) extends WrapperTree
  private case class FieldInit(id: Id, value: Expr) extends WrapperTree


  /** Special helpers for pretty parentheses **/
  private def optP(body: => Any)(using pctx: PrinterContext) = {
    if (requiresParentheses(pctx.current, pctx.previous)) {
      sb.append("(")
      body
      sb.append(")")
    } else {
      body
    }
  }

  private def requiresParentheses(current: Tree, previous: Option[Tree]): Boolean = (current, previous) match {
    case (_, None) => false
    case (_, Some(_: Decl | _: Call | _: ArrayAccess | _: If | _: IfElse | _: While | _: Return | _: Assign)) => false
    // Add parentheses even when not necessary to avoid warnings in C
    // case (Operator(precedence1), Some(Operator(precedence2))) if precedence1 < precedence2 => false
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
