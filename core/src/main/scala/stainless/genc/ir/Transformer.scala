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
  final def apply(prog: Prog): to.Prog = rec(prog)(Ø)
  final def apply(vd: ValDef): to.ValDef = rec(vd)(Ø)
  final def apply(e: Expr): to.Expr = rec(e)(Ø)
  final def apply(typ: Type): to.Type = rec(typ)(Ø)


  // See note above about caching & partial function definition
  private val funCache = MutableMap[FunDef, to.FunDef]()

  protected final def registerFunction(older: FunDef, newer: to.FunDef) {
    funCache.update(older, newer)
  }

  protected def rec(prog: Prog)(implicit env: Env): to.Prog =
    to.Prog(
      prog.functions.map(rec),
      prog.classes.map(rec)
    )

  protected final def rec(fd: FunDef)(implicit env: Env): to.FunDef = funCache.getOrElse(fd, recImpl(fd))

  protected def recImpl(fd: FunDef)(implicit env: Env): to.FunDef = {
    val newer = to.FunDef(fd.id, rec(fd.returnType), fd.ctx map rec, fd.params map rec, null, fd.export)
    registerFunction(fd, newer)
    newer.body = rec(fd.body)
    newer
  }

  protected def rec(fb: FunBody)(implicit env: Env): to.FunBody = (fb: @unchecked) match {
    case FunBodyAST(body) => to.FunBodyAST(rec(body))
    case FunBodyManual(includes, body) => to.FunBodyManual(includes, body)
  }

  // NOTE Due to the mutability nature of ClassDef and its children registration process,
  //      we need to traverse class hierarchies in a top down fashion. See recImpl.
  protected final def rec(cd: ClassDef)(implicit env: Env): to.ClassDef = {
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

  protected def recImpl(cd: ClassDef, parent: Option[to.ClassDef])(implicit env: Env): to.ClassDef =
    to.ClassDef(cd.id, parent, cd.fields map rec, cd.isAbstract)

  protected def rec(vd: ValDef)(implicit env: Env): to.ValDef = to.ValDef(vd.id, rec(vd.typ), vd.isVar)

  protected def rec(alloc: ArrayAlloc)(implicit env: Env): to.ArrayAlloc = (alloc: @unchecked) match {
    case ArrayAllocStatic(ArrayType(base), length, Right(values)) =>
      to.ArrayAllocStatic(to.ArrayType(rec(base)), length, Right(values map rec))

    case ArrayAllocStatic(ArrayType(base), length, Left(_)) =>
      to.ArrayAllocStatic(to.ArrayType(rec(base)), length, Left(to.Zero))

    case ArrayAllocVLA(ArrayType(base), length, valueInit) =>
      to.ArrayAllocVLA(to.ArrayType(rec(base)), rec(length), rec(valueInit))
  }

  protected final def rec(e: Expr)(implicit env: Env): to.Expr = recImpl(e)._1

  protected final def recCallable(fun: Callable)(implicit env: Env): to.Callable = rec(fun).asInstanceOf[to.Callable]

  // We need to propagate the enviornement accross the whole blocks, not simply by recusring
  protected def recImpl(e: Expr)(implicit env: Env): (to.Expr, Env) = (e: @unchecked) match {
    case Binding(vd) => to.Binding(rec(vd)) -> env

    case FunVal(fd) => to.FunVal(rec(fd)) -> env
    case FunRef(e) => to.FunRef(rec(e)) -> env

    // Consider blocks as a sequence of let statements
    case Block(exprs0) =>
      var newEnv = env
      val exprs = for { e0 <- exprs0 } yield {
        val (e, nextEnv) = recImpl(e0)(newEnv)
        newEnv = nextEnv
        e
      }
      to.buildBlock(exprs) -> newEnv

    case Decl(vd) => to.Decl(rec(vd)) -> env
    case DeclInit(vd, value) => to.DeclInit(rec(vd), rec(value)) -> env
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
    case IsA(expr, ct) => to.IsA(rec(expr), to.ClassType(rec(ct.clazz))) -> env
    case AsA(expr, ct) => to.AsA(rec(expr), to.ClassType(rec(ct.clazz))) -> env
    case IntegralCast(expr, t) => to.IntegralCast(rec(expr), t) -> env
    case Lit(lit) => to.Lit(lit) -> env
    case Ref(e) => to.Ref(rec(e)) -> env
    case Deref(e) => to.Deref(rec(e)) -> env
    case Return(e) => to.Return(rec(e)) -> env
    case Break => to.Break -> env
  }

  protected def rec(typ: Type)(implicit env: Env): to.Type = (typ: @unchecked) match {
    case PrimitiveType(pt) => to.PrimitiveType(pt)
    case FunType(ctx, params, ret) => to.FunType(ctx map rec, params map rec, rec(ret))
    case ClassType(clazz) => to.ClassType(rec(clazz))
    case ArrayType(base) => to.ArrayType(rec(base))
    case ReferenceType(t) => to.ReferenceType(rec(t))
    case TypeDefType(original, alias, include) => to.TypeDefType(original, alias, include)
    case DroppedType => to.DroppedType
    case NoType => to.NoType
  }

}

