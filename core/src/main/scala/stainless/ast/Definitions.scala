/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

import scala.reflect._
import scala.collection.mutable.{Map => MutableMap}

import scala.language.dynamics

trait Definitions extends inox.ast.Definitions { self: Trees =>

  case object Extern extends Flag("extern", Seq.empty)
  case class Derived(id: Identifier) extends Flag("derived", Seq(id))

  override def extractFlag(name: String, args: Seq[Any]): Flag = (name, args) match {
    case ("extern", Seq()) => Extern
    case _ => super.extractFlag(name, args)
  }

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

    object lookup {
      private def find[T](name: String, map: Map[Identifier, T]): Option[T] = map.find(_._1 match {
        case SymbolIdentifier(`name`) => true
        case _ => false
      }).map(_._2)

      def apply[T <: Definition : ClassTag](name: String): T =
        if (classTag[ADTDefinition].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) {
          find(name, adts).getOrElse(throw ADTLookupException(FreshIdentifier(name))).asInstanceOf[T]
        } else if (classTag[FunDef].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) {
          find(name, functions).getOrElse(throw FunctionLookupException(FreshIdentifier(name))).asInstanceOf[T]
        } else sys.error("Unexpected lookup of type " + classTag[T])
    }
  }

  implicit class StainlessFunDef(fd: FunDef) {
    @inline def precondition(implicit s: Symbols): Option[Expr] = s.getPrecondition(fd)
    @inline def hasPrecondition(implicit s: Symbols): Boolean = precondition.isDefined
    @inline def precOrTrue(implicit s: Symbols): Expr = precondition.getOrElse(BooleanLiteral(true))

    @inline def body(implicit s: Symbols): Option[Expr] = s.getBody(fd)

    @inline def postcondition(implicit s: Symbols): Option[Expr] = s.getPostcondition(fd)
    @inline def hasPostcondition(implicit s: Symbols): Boolean = postcondition.isDefined
    @inline def postOrTrue(implicit s: Symbols): Expr = postcondition.getOrElse {
      Lambda(Seq(ValDef(FreshIdentifier("res", true), fd.returnType)), BooleanLiteral(true))
    }
  }

  implicit class StainlessTypedFunDef(tfd: TypedFunDef) {
    @inline def precondition(implicit s: Symbols): Option[Expr] = s.getPrecondition(tfd)
    @inline def hasPrecondition(implicit s: Symbols): Boolean = precondition.isDefined
    @inline def precOrTrue(implicit s: Symbols): Expr = precondition.getOrElse(BooleanLiteral(true))

    @inline def body(implicit s: Symbols): Option[Expr] = s.getBody(tfd)

    @inline def postcondition(implicit s: Symbols): Option[Expr] = s.getPostcondition(tfd)
    @inline def hasPostcondition(implicit s: Symbols): Boolean = postcondition.isDefined
    @inline def postOrTrue(implicit s: Symbols): Expr = postcondition.getOrElse {
      Lambda(Seq(ValDef(FreshIdentifier("res", true), tfd.returnType)), BooleanLiteral(true))
    }
  }

  implicit class StainlessLookup(val p: Program { val trees: self.type }) {
    def lookup[T <: Definition : ClassTag](name: String): T = p.symbols.lookup[T](name)
  }
}
