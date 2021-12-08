/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import PrimitiveTypes.{ PrimitiveType => PT, _ } // For desambiguation
import Literals._
import Operators._
import IRs._

import collection.mutable.{ Stack => MutableStack, Set => MutableSet }

/*
 * The main idea is to add ReferenceType on functions' parameters when either:
 *  - the parameter is not an array (C array are always passed by reference using a different mechanism)
 *  - the parameter is part of the context of the function
 *  - the parameter is of mutable type
 *
 * This also means that when using a binding in an expression we have to make sure that we
 * take a reference or dereference it before using it.
 *
 * Array are mutables, but once converted into C they are wrapped into an immutable struct;
 * we therefore do not take array by reference because this would only add an indirection.
 *
 * When normalisation kicks in, we might face the following pattern:
 *   var norm // no value
 *   if (cond) norm = v1 else norm = v2
 * If v1 & v2 are:
 *  - both of reference type, then norm also is a reference;
 *  - both of non-reference type, then norm is not a reference either;
 *  - a mix of reference/non-reference types, then we stop due to a C type conflict.
 *
 * NOTE The last case could be hanlded with something like what follows, but this is too complex for now.
 *      Also, this can be solved on the user side trivially.
 *   var norm: T*;
 *   var normHelper: T;
 *   if (cond) norm = ptr; else { normHelper = value; norm = &normHelper }
 *
 * NOTE It is also possible to have more than two assignment points. This is handled below.
 */
final class Referentiator(val ctx: inox.Context) extends Transformer(LIR, RIR) {
  import from._

  case class Env(vds: Map[ValDef, to.ValDef], mutableParams: Set[to.ValDef], inGlobalDeclarations: Boolean) {
    def apply(vd: ValDef) = vds(vd)

    def +(mapping: (ValDef, to.ValDef)) = copy(vds = vds + mapping)

    def withParams(mapping: Map[ValDef, to.ValDef]): Env = {
      val refs = mapping.values.toSet filter { _.isReference }
      copy(vds = vds ++ mapping, mutableParams = refs)
    }
  }

  val Ø = Env(Map.empty, Set.empty, false)

  // Registry of ValDef declared using Decl and which are references.
  private val knownDeclRef = MutableSet[to.ValDef]()

  private def isKnownDeclRef(vd: ValDef)(using env: Env) = {
    val to = env.vds(vd)
    knownDeclRef(to) || env.mutableParams(to)
  }

  private def addRef(t: Type)(using env: Env): Boolean = !t.isArray && t.isMutable && !env.inGlobalDeclarations
  private def addRef2(t: RIR.Type)(using env: Env): Boolean = !t.isArray && t.isMutable && !env.inGlobalDeclarations

  override def rec(prog: Prog)(using env: Env): to.Prog = {
    if (prog.decls.nonEmpty) {
      val modes = prog.decls.map(_._2)
      val (to.Block(newDecls), newEnv0) = recImpl(Block(prog.decls.map(_._1)))(using env.copy(inGlobalDeclarations = true))
      val newEnv = newEnv0.copy(inGlobalDeclarations = false)
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

  override def recImpl(fd: FunDef)(using env: Env): to.FunDef = {
    val id = fd.id

    val returnType = rec(fd.returnType) // nothing special thanks to the no-aliasing rule

    val ctx = fd.ctx map { c0 =>
      // except for arrays, add ReferenceType
      val c = rec(c0)
      if (c.isArray) c
      else toReference(c)
    }

    val params = fd.params map { p0 =>
      // except for arrays, add ReferenceType to mutable types
      val p = rec(p0)
      if (addRef2(p.typ)) toReference(p)
      else p
    }

    // Build the new environment: from CIR to RIR
    val newEnv = env.withParams(((fd.ctx ++ fd.params) zip (ctx ++ params)).toMap)

    // Handle recursive functions
    val newer = to.FunDef(id, returnType, ctx, params, null, fd.isExported, fd.isPure)
    registerFunction(fd, newer)
    newer.body = rec(fd.body)(using newEnv)
    newer
  }

  // When converting a binding we add Deref if the variable is known to be
  // a reference. When converting, say, a function call we add Ref if the
  // expected parameter is of ReferenceType, or Deref in the opposite
  // situation.
  //
  // These operations can introduce pattern such as Deref(Ref(_))
  // or Ref(Deref(_)). This is of course not what we want so we fix it
  // right away using the ref & deref factory functions.
  final override def recImpl(e: Expr)(using env: Env): (to.Expr, Env) = e match {
    case Binding(vd0) =>
      // Check the environment for id; if it's a ref we have to reference it.
      val vd = env(vd0)
      val b = to.Binding(vd)
      if (vd.isReference) deref(b) -> env
      else b -> env

    case MemSet(obj, value, size) =>
      to.MemSet(ref(rec(obj)), rec(value), rec(size)) -> env

    case Decl(vd0, None) =>
      val vd = rec(vd0)
      val newEnv = env + (vd0 -> vd)
      to.Decl(vd, None) -> newEnv

    case Decl(vd0, Some(Binding(rhs0))) if addRef(rhs0.getType) =>
      // Here we patch aliases on references generated by normalisation.
      val vd = toReference(rec(vd0))
      val newEnv = env + (vd0 -> vd)
      val value1 = to.Binding(env(rhs0))
      val value = if (value1.getType.isReference) value1 else ref(value1)
      to.Decl(vd, Some(value)) -> newEnv

    case Decl(vd0, Some(Binding(rhs0))) if isKnownDeclRef(rhs0) =>
      // Here we patch aliases on references generated by normalisation.
      val vd = toReference(rec(vd0))
      val newEnv = env + (vd0 -> vd)
      to.Decl(vd, Some(to.Binding(env(rhs0)))) -> newEnv

    case Decl(vd0, Some(fa @ FieldAccess(_, _))) if addRef(fa.getType) =>
      val vd = toReference(rec(vd0))
      val newEnv = env + (vd0 -> vd)
      to.Decl(vd, Some(ref(rec(fa)))) -> newEnv

    case Decl(vd0, Some(value0)) =>
      val vd = rec(vd0)
      val value = rec(value0)
      val newEnv = env + (vd0 -> vd)
      to.Decl(vd, Some(value)) -> newEnv

    case Ref(_) | Deref(_) => ctx.reporter.fatalError("Ref & Deref expression should not yet be present")

    case App(fun0, extra0, args0) =>
      // Add Ref/Deref to extra/args when appropriate
      val fun = recCallable(fun0)
      val extra = refMatch(fun.typ.ctx)(extra0 map rec)
      val args = refMatch(fun.typ.params)(args0 map rec)

      to.App(fun, extra, args) -> env

    case Construct(cd0, args0) =>
      val cd = rec(cd0)
      val args = refMatch(cd.fields)(args0 map rec)

      to.Construct(cd, args) -> env

    case Assign(lhs0, rhs0) =>
      val lhs1 = rec(lhs0)
      val rhs1 = rec(rhs0)

      // Prevent normalisation variable to copy a mutable variable; keep pointers!
      //
      // Example of what we don't want:
      // void foo(bool flag, int* ptr1, int* ptr2) {
      //   int* norm;
      //   if (flag) *norm = *ptr1; else *norm = *ptr2;
      // }
      //
      // Instead, what we want is:
      //   if (flag) norm = ptr1; else norm = ptr2;
      //
      val (lhs, rhs) = (lhs1, rhs1) match {
        case (to.Deref(lhs), to.Deref(rhs)) => (lhs, rhs)
        case (to.Deref(lhs), rhs) if rhs.getType.isReference =>
          ctx.reporter.fatalError(s"$lhs0 = $rhs0 was translated into $lhs1 = $rhs1")
        case _ => (lhs1, rhs1)
      }

      to.Assign(lhs, rhs) -> env


    case e => super.recImpl(e)
  }

  // Add references to mutable type in argument position in function types only:
  // the other types are handles according to the context around the usage of types.
  override def rec(typ: Type)(using Env): to.Type = typ match {
    case FunType(Seq(), params0, ret0) =>
      // This is very similar to how function parameter (ValDef) are processed above.
      val params = params0 map { rec(_) match {
        case t if addRef2(t) => to.ReferenceType(t)
        case t => t
      }}

      to.FunType(Seq(), params, rec(ret0))

    case FunType(ctx0, _, _) =>
      ctx.reporter.fatalError(s"Don't known yet how to handle ctx ($ctx0) in FunType!")

    case _ => super.rec(typ)
  }

  // Adapt the expressions to match w.r.t. references the given parameter types, for argument-like expressions.
  private def refMatch(params: Seq[to.ValDef])(args: Seq[to.Expr])(using DummyImplicit): Seq[to.Expr] =
    refMatch(params map { _.getType })(args)

  private def refMatch(params: Seq[to.Type])(args: Seq[to.Expr]): Seq[to.Expr] = {
    (params zip args) map { case (param, arg) =>
      val pr = param.isReference
      val ar = arg.getType.isReference

      (pr, ar) match {
        case (false, false) | (true, true) => arg
        case (false, true) => deref(arg)
        case (true, false) => ref(arg, shortLived = true)
      }
    }
  }

  // Build Ref & Deref expression without patterns such as Ref(Deref(_))
  private def ref(e: to.Expr, shortLived: Boolean = false): to.Expr = e match {
    case _: to.Binding | _: to.FieldAccess | _: to.ArrayAccess | _: to.AsA => to.Ref(e)
    case to.Deref(e) => e

    // NOTE Reference can be built on Constructor, but we have to make sure we
    //      don't take the reference of a temporary result for a too long period.
    case ctor @ to.Construct(_, _) if shortLived => to.Ref(ctor)

    case _ => ctx.reporter.fatalError(s"Making reference on an unsupported expression: $e")
  }

  private def deref(e: to.Expr): to.Expr = e match {
    case b @ to.Binding(vd) if vd.isReference => to.Deref(b)
    case to.Ref(e) => e
    case _ => ctx.reporter.fatalError(s"Dereferencing an unsupported expression: $e")
  }

  private def toReference(vd: to.ValDef) = vd.copy(typ = to.ReferenceType(vd.typ))
}
