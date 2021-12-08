/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import collection.mutable.{ Set => MutableSet }

/*
 * Visite an IR in a post-order manner.
 *
 * NOTE Subclasses can selectively override the visite methods that aren't final on a need to basis.
 *
 * NOTE No caching is done, hence subclasses should be aware that a definition/expression/type can
 *      be visited several times with the same env.
 * EXCEPT for functions. See Transformer for reason.
 */
abstract class Visitor[S <: IR](val ir: S) {
  import ir._

  // Entry point for the visit
  final def apply(prog: Prog): Unit = rec(prog)
  final def apply(e: Expr): Unit = rec(e)

  protected def visit(prog: Prog): Unit = ()
  protected def visit(fd: FunDef): Unit = ()
  protected def visit(cd: ClassDef): Unit = ()
  protected def visit(vd: ValDef): Unit = ()
  protected def visit(fb: FunBody): Unit = ()
  protected def visit(alloc: ArrayAlloc): Unit = ()
  protected def visit(e: Expr): Unit = ()
  protected def visit(typ: Type): Unit = ()

  private val funCache = MutableSet[FunDef]()

  private def rec(prog: Prog): Unit = {
    prog.functions.foreach(rec)
    visit(prog)
  }

  private def rec(fd: FunDef): Unit = if (!funCache(fd)) {
    funCache += fd // Traverse it once

    rec(fd.returnType)
    fd.ctx foreach rec
    fd.params foreach rec
    rec(fd.body)
    visit(fd)
  }

  private def rec(fb: FunBody): Unit = {
    fb match {
      case FunBodyAST(body) => rec(body)
      case _ => ()
    }
    visit(fb)
  }

  private def rec(cd: ClassDef): Unit = {
    def impl(cd: ClassDef): Unit = {
      cd.fields foreach rec
      visit(cd)
    }

    cd.getFullHierarchy foreach impl
  }

  private def rec(vd: ValDef): Unit = {
    rec(vd.typ)
    visit(vd)
  }

  private def rec(alloc: ArrayAlloc): Unit = {
    (alloc: @unchecked) match {
      case ArrayAllocStatic(arrayType, length, values) =>
        rec(arrayType)
        values match {
          case Right(values) => values foreach rec
          case _ =>
        }

      case ArrayAllocVLA(arrayType, length, valueInit) =>
        rec(arrayType)
        rec(length)
        rec(valueInit)
    }

    visit(alloc)
  }

  private def rec(e: Expr): Unit = {
    (e: @unchecked) match {
      case Binding(vd) => rec(vd)
      case FunVal(fd) => rec(fd)
      case FunRef(e) => rec(e)
      case Assert(e) => rec(e)
      case Block(exprs) => exprs foreach rec
      case Decl(vd, None) => rec(vd)
      case Decl(vd, Some(value)) => rec(vd); rec(value)
      case App(fun, extra, args) => rec(fun); extra foreach rec; args foreach rec
      case Construct(cd, args) => rec(cd); args foreach rec
      case ArrayInit(alloc) => rec(alloc)
      case FieldAccess(objekt, fieldId) => rec(objekt)
      case ArrayAccess(array, index) => rec(array); rec(index)
      case ArrayLength(array) => rec(array)
      case Assign(lhs, rhs) => rec(lhs); rec(rhs)
      case BinOp(op, lhs, rhs) => rec(lhs); rec(rhs)
      case UnOp(op, expr) => rec(expr)
      case If(cond, thenn) => rec(cond); rec(thenn)
      case IfElse(cond, thenn, elze) => rec(cond); rec(thenn); rec(elze)
      case While(cond, body) => rec(cond); rec(body)
      case IsA(expr, ct) => rec(expr); rec(ct.clazz)
      case AsA(expr, ct) => rec(expr); rec(ct.clazz)
      case IntegralCast(expr, _) => rec(expr)
      case Lit(lit) => ()
      case Ref(e) => rec(e)
      case Deref(e) => rec(e)
      case Return(e) => rec(e)
      case Break => ()
    }
    visit(e)
  }

  private def rec(typ: Type): Unit = {
    (typ: @unchecked) match {
      case PrimitiveType(pt) => ()
      case FunType(ctx, params, ret) => ((ret +: ctx) ++ params) map rec
      case ClassType(clazz) => rec(clazz)
      case ArrayType(base, _) => rec(base)
      case ReferenceType(t) => rec(t)
      case TypeDefType(original, alias, include, _) => ()
      case DroppedType => ()
      case NoType => ()
    }
    visit(typ)
  }

}
