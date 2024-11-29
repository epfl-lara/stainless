/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._

import collection.mutable.{ Map => MutableMap }

trait NoEnv {
  type Env = Unit
  final val Ø = ()
}

/*
 * Transform an IR into another version of the IR.
 *
 * NOTE Subclasses can selectively override the rec/recImpl methods that aren't final on a need to basis.
 *
 * NOTE Subclasses have to define an `Env` type and an empty enviornment Ø. They can be Unit and (),
 *      respectively. In that case, inherit from NoEnv.
 *
 * NOTE No caching is done, hence subclasses should be aware that a definition/expression/type can
 *      be transformed several times with the same env.
 * EXCEPT for FunDef. In order to support recursive functions, function definitions are cached.
 *      When building partial function definitions (i.e. with body = null), subclasses are required
 *      to call `registerFunction` before proceeding with the conversion of their bodies.
 */
abstract class Transformer[From <: IR, To <: IR](final val from: From, final val to: To) {
  import from._

  type Env
  val Ø: Env // empty env

  // Entry point of the transformation
  final def apply(prog: Prog): to.Prog = rec(prog)(using Ø)
  final def apply(vd: ValDef): to.ValDef = rec(vd)(using Ø)
  final def apply(e: Expr): to.Expr = rec(e)(using Ø)
  final def apply(typ: Type): to.Type = rec(typ)(using Ø)


  // See note above about caching & partial function definition
  private val funCache = MutableMap[FunDef, to.FunDef]()

  protected final def registerFunction(older: FunDef, newer: to.FunDef): Unit = {
    funCache.update(older, newer)
  }

  protected def rec(prog: Prog)(using Env): to.Prog = {
    if (prog.decls.nonEmpty) {
      val modes = prog.decls.map(_._2)
      val (to.Block(newDecls), newEnv) = recImpl(Block(prog.decls.map(_._1))): @unchecked
      to.Prog(
        newDecls.map(_.asInstanceOf[to.Decl]).zip(modes),
        prog.functions.map(rec(_)(using newEnv)),
        prog.classes.map(rec(_)(using newEnv)),
      )
    } else {
      to.Prog(
        Seq(),
        prog.functions.map(rec),
        prog.classes.map(rec),
      )
    }
  }

  protected final def rec(fd: FunDef)(using Env): to.FunDef = funCache.getOrElse(fd, recImpl(fd))

  protected def recImpl(fd: FunDef)(using Env): to.FunDef = {
    val newer = to.FunDef(fd.id, rec(fd.returnType), fd.ctx map rec, fd.params map rec, null, fd.isExported, fd.isPure)
    registerFunction(fd, newer)
    newer.body = rec(fd.body)
    newer
  }

  protected def rec(fb: FunBody)(using Env): to.FunBody = (fb: @unchecked) match {
    case FunDropped(isAccessor) => to.FunDropped(isAccessor)
    case FunBodyAST(body) => to.FunBodyAST(rec(body))
    case FunBodyManual(headerIncludes, cIncludes, body) => to.FunBodyManual(headerIncludes, cIncludes, body)
  }

  // NOTE Due to the mutability nature of ClassDef and its children registration process,
  //      we need to traverse class hierarchies in a top down fashion. See recImpl.
  protected final def rec(cd: ClassDef)(using Env): to.ClassDef = {
    type ClassTranslation = Map[from.ClassDef, to.ClassDef]

    def topDown(transformedParent: Option[to.ClassDef], current: from.ClassDef, acc: ClassTranslation): ClassTranslation = {
      val transformed = recImpl(current, transformedParent)

      val acc2 = acc + (current -> transformed)
      val subs = current.getDirectChildren

      subs.foldLeft(acc2) { case (acc3, sub) => topDown(Some(transformed), sub, acc3) }
    }

    val top = cd.hierarchyTop
    val translation = topDown(None, top, Map.empty)
    val transformed = translation(cd)
    transformed
  }

  protected def recImpl(cd: ClassDef, parent: Option[to.ClassDef])(using env: Env): to.ClassDef =
    to.ClassDef(cd.id, parent,
      cd.fields.map { case (vd,modes) => (rec(vd), modes) },
      cd.isAbstract, cd.isExported, cd.isPacked
    )

  protected def rec(vd: ValDef)(using Env): to.ValDef = to.ValDef(vd.id, rec(vd.typ), vd.isVar)

  protected def rec(alloc: ArrayAlloc)(using Env): to.ArrayAlloc = (alloc: @unchecked) match {
    case ArrayAllocStatic(ArrayType(base, optLength), length, Right(values)) =>
      to.ArrayAllocStatic(to.ArrayType(rec(base), optLength), length, Right(values map rec))

    case ArrayAllocStatic(ArrayType(base, optLength), length, Left(_)) =>
      to.ArrayAllocStatic(to.ArrayType(rec(base), optLength), length, Left(to.Zero))

    case ArrayAllocVLA(ArrayType(base, optLength), length, valueInit) =>
      to.ArrayAllocVLA(to.ArrayType(rec(base), optLength), rec(length), rec(valueInit))
  }

  protected def rec(e: Expr)(using Env): to.Expr = recImpl(e)._1

  protected final def recCallable(fun: Callable)(using Env): to.Callable = rec(fun).asInstanceOf[to.Callable]

  // We need to propagate the enviornement accross the whole blocks, not simply by recursing
  protected def recImpl(e: Expr)(using env: Env): (to.Expr, Env) = (e: @unchecked) match {
    case Binding(vd) => to.Binding(rec(vd)) -> env

    case FunVal(fd) => to.FunVal(rec(fd)) -> env
    case FunRef(e) => to.FunRef(rec(e)) -> env

    // Consider blocks as a sequence of let statements
    case Block(exprs0) =>
      var newEnv = env
      val exprs = for { e0 <- exprs0 } yield {
        val (e, nextEnv) = recImpl(e0)(using newEnv)
        newEnv = nextEnv
        e
      }
      to.buildBlock(exprs) -> newEnv
    case Labeled(name, expr) =>
      to.Labeled(name, rec(expr)) -> env

    case MemSet(pointer, value, size) => to.MemSet(rec(pointer), rec(value), rec(size)) -> env
    case SizeOf(tpe) => to.SizeOf(rec(tpe)) -> env

    case Decl(vd, None) => to.Decl(rec(vd), None) -> env
    case Decl(vd, Some(value)) => to.Decl(rec(vd), Some(rec(value))) -> env
    case App(fun, extra, args) => to.App(recCallable(fun), extra map rec, args map rec) -> env
    case Construct(cd, args) => to.Construct(rec(cd), args map rec) -> env
    case ArrayInit(alloc) => to.ArrayInit(rec(alloc)) -> env
    case FieldAccess(objekt, fieldId) => to.FieldAccess(rec(objekt), fieldId) -> env
    case ArrayAccess(array, index) => to.ArrayAccess(rec(array), rec(index)) -> env
    case ArrayLength(array) => to.ArrayLength(rec(array)) -> env
    case Assign(lhs, rhs) => to.Assign(rec(lhs), rec(rhs)) -> env
    case BinOp(op, lhs, rhs) => to.BinOp(op, rec(lhs), rec(rhs)) -> env
    case UnOp(op, expr) => to.UnOp(op, rec(expr)) -> env
    case If(cond, thenn) => to.If(rec(cond), rec(thenn)) -> env
    case IfElse(cond, thenn, elze) => to.IfElse(rec(cond), rec(thenn), rec(elze)) -> env
    case While(cond, body) => to.While(rec(cond), rec(body)) -> env
    case Goto(label) => to.Goto(label) -> env
    case IsA(expr, ct) => to.IsA(rec(expr), to.ClassType(rec(ct.clazz))) -> env
    case AsA(expr, ct) => to.AsA(rec(expr), to.ClassType(rec(ct.clazz))) -> env
    case IntegralCast(expr, t) => to.IntegralCast(rec(expr), t) -> env
    case Lit(lit) => to.Lit(lit) -> env
    case Ref(e) => to.Ref(rec(e)) -> env
    case Deref(e) => to.Deref(rec(e)) -> env
    case Return(e) => to.Return(rec(e)) -> env
    case Assert(e) => to.Assert(rec(e)) -> env
    case Break => to.Break -> env
    case Continue => to.Continue -> env
  }

  protected def rec(typ: Type)(using Env): to.Type = (typ: @unchecked) match {
    case PrimitiveType(pt) => to.PrimitiveType(pt)
    case FunType(ctx, params, ret) => to.FunType(ctx map rec, params map rec, rec(ret))
    case ClassType(clazz) => to.ClassType(rec(clazz))
    case ArrayType(base, optLength) => to.ArrayType(rec(base), optLength)
    case ReferenceType(t) => to.ReferenceType(rec(t))
    case TypeDefType(original, alias, include, exprt) => to.TypeDefType(original, alias, include, exprt)
    case DroppedType => to.DroppedType
    case NoType => to.NoType
  }

}

