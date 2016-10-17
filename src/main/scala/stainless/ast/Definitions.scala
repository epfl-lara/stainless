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
    @inline def getBody(id: Identifier): Option[Expr] = getBody(getFunction(id))
    @inline def getBody(id: Identifier, tps: Seq[Type]): Option[Expr] = getBody(getFunction(id, tps))
    @inline def getBody(fd: FunDef): Option[Expr] = getBody(fd.typed)
    def getBody(tfd: TypedFunDef): Option[Expr] = bodyCache.getOrElseUpdate(tfd, exprOps.withoutSpec(tfd.fullBody))
  }

  implicit class StainlessFunDef(fd: FunDef) {
    def body(implicit s: Symbols): Option[Expr] = s.getBody(fd)
  }

  implicit class StainlessTypedFunDef(tfd: TypedFunDef) {
    def body(implicit s: Symbols): Option[Expr] = s.getBody(tfd)
  }
}
