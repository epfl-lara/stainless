/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

import scala.collection.mutable.{Map => MutableMap}

trait Definitions extends inox.ast.Definitions { self: Trees =>

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
       with TypeOps
       with SymbolOps { self0: Symbols =>

    private[this] val bodyCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getBody(fd: FunDef): Option[Expr] = getBody(fd.typed)
    def getBody(tfd: TypedFunDef): Option[Expr] =
      bodyCache.getOrElseUpdate(tfd, exprOps.withoutSpec(tfd.fullBody))

    private[this] val preCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getPrecondition(fd: FunDef): Option[Expr] = getPrecondition(fd.typed)
    def getPrecondition(tfd: TypedFunDef): Option[Expr] =
      preCache.getOrElseUpdate(tfd, exprOps.preconditionOf(tfd.fullBody))

    private[this] val postCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getPostcondition(fd: FunDef): Option[Expr] = getPostcondition(fd.typed)
    def getPostcondition(tfd: TypedFunDef): Option[Expr] =
      postCache.getOrElseUpdate(tfd, exprOps.postconditionOf(tfd.fullBody))
  }

  implicit class StainlessFunDef(fd: FunDef) {
    @inline def precondition(implicit s: Symbols): Option[Expr] = s.getPrecondition(fd)
    @inline def precOrTrue(implicit s: Symbols): Expr = precondition.getOrElse(BooleanLiteral(true))
    @inline def hasPrecondition(implicit s: Symbols): Boolean = precondition.isDefined

    @inline def body(implicit s: Symbols): Option[Expr] = s.getBody(fd)

    @inline def postcondition(implicit s: Symbols): Option[Expr] = s.getPostcondition(fd)
    @inline def hasPostcondition(implicit s: Symbols): Boolean = postcondition.isDefined
  }

  implicit class StainlessTypedFunDef(tfd: TypedFunDef) {
    @inline def precondition(implicit s: Symbols): Option[Expr] = s.getPrecondition(tfd)
    @inline def precOrTrue(implicit s: Symbols): Expr = precondition.getOrElse(BooleanLiteral(true))
    @inline def hasPrecondition(implicit s: Symbols): Boolean = precondition.isDefined

    @inline def body(implicit s: Symbols): Option[Expr] = s.getBody(tfd)

    @inline def postcondition(implicit s: Symbols): Option[Expr] = s.getPostcondition(tfd)
    @inline def hasPostcondition(implicit s: Symbols): Boolean = postcondition.isDefined
  }
}
