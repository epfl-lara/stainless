/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

/*
 * Print an IR tree
 */
final class IRPrinter[S <: IR](val ir: S) {
  import ir._

  case class Context(indent: Int) {
    val pad = "  " * indent
    val newLine = s"\n$pad"

    def +(i: Int) = copy(indent = indent + i)
  }

  // Entry point for pretty printing
  final def apply(prog: Prog): String = rec(prog)(Context(0))

  final def apply(tree: Tree)(implicit ptx: Context): String = tree match {
    case t: FunDef => rec(t)
    case t: ClassDef => rec(t)
    case t: ValDef => rec(t)
    case t: Expr => rec(t)
    case t: Type => rec(t)
    case t: ArrayAlloc => rec(t)
    case _ => ???
  }

  private def rec(prog: Prog)(implicit ptx: Context): String = {
    val funs = prog.functions.map(rec)
    val classes = prog.classes.map(rec)

    (funs mkString ptx.newLine) + ptx.newLine + (classes mkString ptx.newLine)
  }

  private def rec(fd: FunDef)(implicit ptx: Context): String = {
    val ctx = fd.ctx map rec mkString ", "
    val params = (fd.params map rec).mkString(start = ", ", sep = ", ", end = "")
    val pre = fd.id + "(<" + ctx + ">" + params + "): " + rec(fd.returnType) + " = {" + ptx.newLine + "  "
    val body = rec(fd.body)(ptx + 1)
    val post = ptx.newLine + "}"

    (if (fd.isPure) "@pure\n" else "") +
    (if (fd.isExported) "@export\n" else "") +
    pre + body + post
  }

  private def rec(fb: FunBody)(implicit ptx: Context): String = {
    fb match {
      case FunBodyAST(body) => rec(body)
      case _ => "@cCode.function"
    }
  }

  private def rec(cd: ClassDef)(implicit ptx: Context): String = {
    val pre = if (cd.isAbstract) "abstract " else ""
    val fields = cd.fields map rec mkString ", "
    val parent = if (cd.parent.isDefined) " extends " + cd.parent.get.id else ""

    pre + "class " + cd.id + "(" + fields + ")" + parent
  }

  private def rec(vd: ValDef)(implicit ptx: Context): String = {
    vd.id + ": " + rec(vd.typ)
  }

  private def rec(alloc: ArrayAlloc)(implicit ptx: Context): String = {
    (alloc: @unchecked) match {
      case ArrayAllocStatic(arrayType, length, Right(values)) =>
        "Array[" + rec(arrayType.base) + "](" + (values map rec mkString ", ") + ")"

      case ArrayAllocStatic(arrayType, length, Left(z)) =>
        "Array[" + rec(arrayType.base) + "]( 0's " + length + " times )"

      case ArrayAllocVLA(arrayType, length, valueInit) =>
        "Array[" + rec(arrayType.base) + "].fill(" + rec(length) + ")(" + rec(valueInit) + ")"
    }
  }

  private def rec(e: Expr)(implicit ptx: Context): String = (e: @unchecked) match {
    case Binding(vd) => "[[ " + vd.id + ": " + rec(vd.getType) + " ]]"
    case FunVal(fd) => "@" + fd.id
    case FunRef(e) => "@{" + rec(e) + "}"
    case Block(exprs) => "{{ " + (exprs map rec mkString ptx.newLine) + " }}"
    case Decl(vd) => (if (vd.isVar) "var" else "val") + " " + rec(vd) + " // no value"
    case DeclInit(vd, value) => (if (vd.isVar) "var" else "val") + " " + rec(vd) + " = " + rec(value)
    case App(callable, extra, args) =>
      rec(callable) + "(<" + (extra map rec mkString ", ") + ">" + (args map rec).mkString(start = ", ", sep = ", ", end = "") + ")"
    case Construct(cd, args) => cd.id + "(" + (args map rec mkString ", ") + ")"
    case ArrayInit(alloc) => rec(alloc)
    case FieldAccess(objekt, fieldId) => rec(objekt) + "." + fieldId
    case ArrayAccess(array, index) => rec(array) + "[" + rec(index) + "]"
    case ArrayLength(array) => rec(array) + ".length"
    case Assign(lhs, rhs) => rec(lhs) + " = " + rec(rhs)
    case BinOp(op, lhs, rhs) => rec(lhs) + " " + op.symbol + " " + rec(rhs)
    case UnOp(op, expr) => op.symbol + rec(expr)
    case If(cond, thenn) =>
      "if (" + rec(cond) + ") {" + ptx.newLine + "  " + rec(thenn)(ptx + 1) + ptx.newLine + "}"
    case IfElse(cond, thenn, elze) =>
      "if (" + rec(cond) + ") {" + ptx.newLine + "  " + rec(thenn)(ptx + 1) + ptx.newLine + "} " +
      "else {" + ptx.newLine + "  " + rec(elze)(ptx + 1) + ptx.newLine + "}"
    case While(cond, body) =>
      "while (" + rec(cond) + ") {" + ptx.newLine + "  " + rec(body)(ptx + 1) + ptx.newLine + "}"
    case IsA(expr, ct) => "¿" + ct.clazz.id + "?" + rec(expr)
    case AsA(expr, ct) => "(" + ct.clazz.id + ")" + rec(expr)
    case IntegralCast(expr, newType) => "(" + newType + ")" + rec(expr)
    case Lit(lit) => lit.toString
    case Ref(e) => "&" + rec(e)
    case Deref(e) => "*" + rec(e)
    case Return(e) => "return " + rec(e)
    case Break => "break"
  }

  private def rec(typ: Type)(implicit ptx: Context): String = (typ: @unchecked) match {
    case PrimitiveType(pt) => pt.toString
    case FunType(ctx, params, ret) =>
      "Function[" + (ctx map rec mkString ", ") + "][" + (params map rec mkString ", ") + "]: " + rec(ret)
    case ClassType(clazz) => clazz.id
    case ArrayType(base, None) => "Array[" + rec(base) + "]"
    case ArrayType(base, Some(length)) => s"Array_$length[" + rec(base) + "]"
    case ReferenceType(t) => "Ref[" + rec(t) + "]"
    case TypeDefType(original, alias, _, _) => "typedef " + original + " -> " + alias
    case DroppedType => "DROPPED"
    case NoType => "NO-TYPE"
  }

}
