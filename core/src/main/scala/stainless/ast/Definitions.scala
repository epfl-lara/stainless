/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import scala.reflect._
import scala.collection.mutable.{Map => MutableMap}

trait Definitions extends inox.ast.Definitions { self: Trees =>

  case object Ghost extends Flag("ghost", Seq.empty)
  case object Extern extends Flag("extern", Seq.empty)
  case object Opaque extends Flag("opaque", Seq.empty)
  case object Private extends Flag("private", Seq.empty)
  case object Final extends Flag("final", Seq.empty)
  case object Unchecked extends Flag("unchecked", Seq.empty)
  case object Synthetic extends Flag("synthetic", Seq())
  case object PartialEval extends Flag("partialEval", Seq())
  case class Derived(id: Identifier) extends Flag("derived", Seq(id))
  case class IsField(isLazy: Boolean) extends Flag("field", Seq.empty)
  case class IsUnapply(isEmpty: Identifier, get: Identifier) extends Flag("unapply", Seq(isEmpty, get))

  def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("ghost", Seq()) => Ghost
    case ("extern", Seq()) => Extern
    case ("opaque", Seq()) => Opaque
    case ("unchecked", Seq()) => Unchecked
    case ("partialEval", Seq()) => PartialEval
    case _ => Annotation(name, args)
  }

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
       with TypeOps
       with SymbolOps
       with CallGraph
       with DependencyGraph { self0: Symbols =>

    private[this] val bodyCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getBody(fd: FunDef): Option[Expr] = getBody(fd.typed)
    def getBody(tfd: TypedFunDef): Option[Expr] =
      bodyCache.getOrElse(tfd, {
        val res = exprOps.withoutSpecs(tfd.fullBody)
        bodyCache(tfd) = res
        res
      })

    private[this] val preCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getPrecondition(fd: FunDef): Option[Expr] = getPrecondition(fd.typed)
    def getPrecondition(tfd: TypedFunDef): Option[Expr] =
      preCache.getOrElse(tfd, {
        val res = exprOps.preconditionOf(tfd.fullBody)
        preCache(tfd) = res
        res
      })

    private[this] val postCache: MutableMap[TypedFunDef, Option[Lambda]] = MutableMap.empty
    @inline def getPostcondition(fd: FunDef): Option[Lambda] = getPostcondition(fd.typed)
    def getPostcondition(tfd: TypedFunDef): Option[Lambda] =
      postCache.getOrElse(tfd, {
        val res = exprOps.postconditionOf(tfd.fullBody)
        postCache(tfd) = res
        res
      })

    protected class Lookup {
      protected def find[T](name: String, map: Map[Identifier, T]): Option[T] = map.find(_._1 match {
        case SymbolIdentifier(`name`) => true
        case _ => false
      }).map(_._2)

      def get[T <: Definition : ClassTag](name: String): Option[T] = {
        if (classTag[ADTSort].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) find(name, sorts)
        else if (classTag[FunDef].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) find(name, functions)
        else None
      }.asInstanceOf[Option[T]]

      def apply[T <: Definition : ClassTag](name: String): T = get[T](name).getOrElse {
        if (classTag[ADTSort].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) {
          throw ADTLookupException(FreshIdentifier(name))
        } else if (classTag[FunDef].runtimeClass.isAssignableFrom(classTag[T].runtimeClass)) {
          throw FunctionLookupException(FreshIdentifier(name))
        } else sys.error("Unexpected lookup of type " + classTag[T])
      }
    }

    val lookup = new Lookup
  }

  implicit class StainlessFunDef(fd: FunDef) {
    @inline def precondition(implicit s: Symbols): Option[Expr] = s.getPrecondition(fd)
    @inline def hasPrecondition(implicit s: Symbols): Boolean = precondition.isDefined
    @inline def precOrTrue(implicit s: Symbols): Expr = precondition.getOrElse(BooleanLiteral(true))

    @inline def body(implicit s: Symbols): Option[Expr] = s.getBody(fd)

    @inline def postcondition(implicit s: Symbols): Option[Lambda] = s.getPostcondition(fd)
    @inline def hasPostcondition(implicit s: Symbols): Boolean = postcondition.isDefined
    @inline def postOrTrue(implicit s: Symbols): Expr = postcondition.getOrElse {
      Lambda(Seq(ValDef(FreshIdentifier("res", true), fd.returnType)), BooleanLiteral(true))
    }

    /** Check whether the function has no (generic) parameter. */
    final def isParameterless = fd.params.isEmpty && fd.tparams.isEmpty

    /**
     * Get the source of this function
     *
     * i.e. either its identifier or the identifier of its (recursively) outer function.
     *
     * NOTE no need to actually recurse here as [[Derived]] already
     *      holds the requested data.
     */
    final def source: Identifier =
      fd.flags collectFirst { case Derived(id) => id } getOrElse fd.id
  }

  implicit class StainlessTypedFunDef(tfd: TypedFunDef) {
    @inline def precondition: Option[Expr] = tfd.symbols.getPrecondition(tfd)
    @inline def hasPrecondition: Boolean = precondition.isDefined
    @inline def precOrTrue: Expr = precondition.getOrElse(BooleanLiteral(true))

    @inline def body: Option[Expr] = tfd.symbols.getBody(tfd)

    @inline def postcondition: Option[Lambda] = tfd.symbols.getPostcondition(tfd)
    @inline def hasPostcondition: Boolean = postcondition.isDefined
    @inline def postOrTrue: Expr = postcondition.getOrElse {
      Lambda(Seq(ValDef(FreshIdentifier("res", true), tfd.returnType)), BooleanLiteral(true))
    }
  }

  implicit class StainlessLookup(val p: Program { val trees: self.type }) {
    def lookup[T <: Definition : ClassTag](name: String): T = p.symbols.lookup[T](name)
  }
}
