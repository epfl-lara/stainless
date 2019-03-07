/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import scala.reflect._
import scala.collection.mutable.{Map => MutableMap}

trait Definitions extends inox.ast.Definitions { self: Trees =>

  case object Law extends Flag("law", Seq.empty)
  // TODO: Move Erasable to Inox?
  case object Erasable extends Flag("erasable", Seq.empty)
  case class IndexedAt(e: Expr) extends Flag("indexedAt", Seq(e))
  case object Ghost extends Flag("ghost", Seq.empty)
  case object Extern extends Flag("extern", Seq.empty)
  case object Opaque extends Flag("opaque", Seq.empty)
  case object Private extends Flag("private", Seq.empty)
  case object Final extends Flag("final", Seq.empty)
  case object Unchecked extends Flag("unchecked", Seq.empty)
  case object Library extends Flag("library", Seq.empty)
  case object Synthetic extends Flag("synthetic", Seq())
  case object PartialEval extends Flag("partialEval", Seq())
  case class Derived(id: Identifier) extends Flag("derived", Seq(id))
  case class IsField(isLazy: Boolean) extends Flag("field", Seq.empty)
  case class IsUnapply(isEmpty: Identifier, get: Identifier) extends Flag("unapply", Seq(isEmpty, get))

  def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("law", Seq()) => Law
    case ("erasable", Seq()) => Erasable
    case ("indexedAt", Seq(e)) => IndexedAt(e)
    case ("ghost", Seq()) => Ghost
    case ("extern", Seq()) => Extern
    case ("opaque", Seq()) => Opaque
    case ("unchecked", Seq()) => Unchecked
    case ("library", Seq()) => Library
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

    import exprOps.{Precondition, Postcondition}

    private[this] val measureCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getMeasure(fd: FunDef): Option[Expr] = getMeasure(fd.typed)
    def getMeasure(tfd: TypedFunDef): Option[Expr] =
      measureCache.getOrElseUpdate(tfd, exprOps.measureOf(tfd.fullBody))

    private[this] val bodyCache: MutableMap[TypedFunDef, Option[Expr]] = MutableMap.empty
    @inline def getBody(fd: FunDef): Option[Expr] = getBody(fd.typed)
    def getBody(tfd: TypedFunDef): Option[Expr] =
      bodyCache.getOrElse(tfd, {
        val res = exprOps.withoutSpecs(tfd.fullBody)
        bodyCache(tfd) = res
        res
      })

    private[this] val preCache: MutableMap[TypedFunDef, Option[Precondition]] = MutableMap.empty
    @inline def getPrecondition(fd: FunDef): Option[Precondition] = getPrecondition(fd.typed)
    def getPrecondition(tfd: TypedFunDef): Option[Precondition] =
      preCache.getOrElse(tfd, {
        val res = exprOps.preconditionOf(tfd.fullBody)
        preCache(tfd) = res
        res
      })

    private[this] val postCache: MutableMap[TypedFunDef, Option[Postcondition]] = MutableMap.empty
    @inline def getPostcondition(fd: FunDef): Option[Postcondition] = getPostcondition(fd.typed)
    def getPostcondition(tfd: TypedFunDef): Option[Postcondition] =
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

  import exprOps.{Precondition, Postcondition}

  implicit class StainlessFunDef(fd: FunDef) {
    @inline def precondition(implicit s: Symbols): Option[Precondition] = s.getPrecondition(fd)
    @inline def hasPrecondition(implicit s: Symbols): Boolean = precondition.isDefined
    @inline def precOrTrue(implicit s: Symbols): Precondition = precondition.getOrElse {
      Precondition(BooleanLiteral(true), true)
    }

    @inline def body(implicit s: Symbols): Option[Expr] = s.getBody(fd)
    @inline def measure(implicit s: Symbols): Option[Expr] = s.getMeasure(fd)

    @inline def postcondition(implicit s: Symbols): Option[Postcondition] = s.getPostcondition(fd)
    @inline def hasPostcondition(implicit s: Symbols): Boolean = postcondition.isDefined
    @inline def postOrTrue(implicit s: Symbols): Postcondition = postcondition.getOrElse {
      Postcondition(
        Lambda(Seq(ValDef(FreshIdentifier("res", true), fd.returnType)), BooleanLiteral(true)),
        true
      )
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
    @inline def precondition: Option[Precondition] = tfd.symbols.getPrecondition(tfd)
    @inline def hasPrecondition: Boolean = precondition.isDefined
    @inline def precOrTrue: Precondition = precondition.getOrElse {
      Precondition(BooleanLiteral(true), true)
    }

    @inline def body: Option[Expr] = tfd.symbols.getBody(tfd)
    @inline def measure(implicit s: Symbols): Option[Expr] = s.getMeasure(tfd)

    @inline def postcondition: Option[Postcondition] = tfd.symbols.getPostcondition(tfd)
    @inline def hasPostcondition: Boolean = postcondition.isDefined
    @inline def postOrTrue: Postcondition = postcondition.getOrElse {
      Postcondition(
        Lambda(Seq(ValDef(FreshIdentifier("res", true), tfd.returnType)), BooleanLiteral(true)),
        true
      )
    }
  }

  implicit class StainlessLookup(val p: Program { val trees: self.type }) {
    def lookup[T <: Definition : ClassTag](name: String): T = p.symbols.lookup[T](name)
  }
}
