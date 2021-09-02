/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import stainless.termination.TerminationReport

import scala.reflect._
import scala.collection.mutable.{Map => MutableMap}

trait Definitions extends inox.ast.Definitions { self: Trees =>

  case object Law extends Flag("law", Seq.empty)
  // TODO: Move Erasable to Inox?
  case object Erasable extends Flag("erasable", Seq.empty)
  case object Lazy extends Flag("lazy", Seq.empty)
  case class IndexedAt(e: Expr) extends Flag("indexedAt", Seq(e))
  case object InlineInvariant extends Flag("inlineInvariant", Seq())

  case object Ghost extends Flag("ghost", Seq.empty)
  case object Extern extends Flag("extern", Seq.empty)
  case object Opaque extends Flag("opaque", Seq.empty)
  case object Private extends Flag("private", Seq.empty)
  case object Final extends Flag("final", Seq.empty)
  case object DropVCs extends Flag("DropVCs", Seq.empty)
  case object DropConjunct extends Flag("dropConjunct", Seq.empty)
  case object SplitVC extends Flag("splitVC", Seq.empty)
  case object Library extends Flag("library", Seq.empty)
  case object Synthetic extends Flag("synthetic", Seq())
  case object PartialEval extends Flag("partialEval", Seq())
  case object Wrapping extends Flag("wrapping", Seq.empty)
  case object Template extends Flag("template", Seq.empty)

  case class Derived(idOpt: Option[Identifier]) extends Flag("derived", idOpt.toSeq)
  case class IsField(isLazy: Boolean) extends Flag("field", Seq.empty)
  case class IsUnapply(isEmpty: Identifier, get: Identifier) extends Flag("unapply", Seq(isEmpty, get))
  case class ClassParamInit(cid: Identifier) extends Flag("paramInit", Seq(cid))

  case class TerminationStatus(status: TerminationReport.Status) extends Flag("termination", Seq(status))

  def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("law", Seq()) => Law
    case ("erasable", Seq()) => Erasable
    case ("lazy", Seq()) => Lazy
    case ("indexedAt", Seq(e)) => IndexedAt(e)
    case ("ghost", Seq()) => Ghost
    case ("extern", Seq()) => Extern
    case ("opaque", Seq()) => Opaque
    case ("dropVCs", Seq()) => DropVCs
    case ("dropConjunct", Seq()) => DropConjunct
    case ("library", Seq()) => Library
    case ("partialEval", Seq()) => PartialEval
    case ("wrapping", Seq()) => Wrapping
    case ("template", Seq()) => Template
    case ("inlineInvariant", Seq()) => InlineInvariant
    case _ => Annotation(name, args)
  }

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
       with TypeOps
       with SymbolOps
       with CallGraph
       with DependencyGraph { self0: Symbols =>

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

    override protected def simplestValue(tpe: Type, seen: Set[Type], allowSolver: Boolean, inLambda: Boolean)
                                        (implicit sem: symbols.Semantics, ctx: inox.Context): Expr = tpe match {
      case ArrayType(base) => FiniteArray(Seq(), base)
      case _ => super.simplestValue(tpe, seen, allowSolver, inLambda)
    }
  }

  implicit class StainlessFunDef(fd: FunDef) {
    @inline def precondition: Option[Expr] = exprOps.preconditionOf(fd.fullBody)
    @inline def hasPrecondition: Boolean =
      exprOps.BodyWithSpecs(fd.fullBody).specs.exists(_.kind == exprOps.PreconditionKind)
    @inline def precOrTrue: Expr = precondition.getOrElse(BooleanLiteral(true))

    @inline def body: Option[Expr] = exprOps.withoutSpecs(fd.fullBody)
    @inline def measure: Option[Expr] = exprOps.measureOf(fd.fullBody)

    @inline def postcondition: Option[Lambda] = exprOps.postconditionOf(fd.fullBody)
    @inline def hasPostcondition: Boolean =
      exprOps.BodyWithSpecs(fd.fullBody).specs.exists(_.kind == exprOps.PostconditionKind)
    @inline def postOrTrue: Expr = postcondition.getOrElse {
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
      fd.flags collectFirst { case Derived(Some(id)) => id } getOrElse fd.id
  }

  implicit class StainlessTypedFunDef(tfd: TypedFunDef) {
    @inline def precondition: Option[Expr] = exprOps.preconditionOf(tfd.fullBody)
    @inline def hasPrecondition: Boolean =
      exprOps.BodyWithSpecs(tfd.fullBody).specs.exists(_.kind == exprOps.PreconditionKind)
    @inline def precOrTrue: Expr = precondition.getOrElse(BooleanLiteral(true))

    @inline def body: Option[Expr] = exprOps.withoutSpecs(tfd.fullBody)
    @inline def measure: Option[Expr] = exprOps.measureOf(tfd.fullBody)

    @inline def postcondition: Option[Lambda] = exprOps.postconditionOf(tfd.fullBody)
    @inline def hasPostcondition: Boolean = postcondition.isDefined
    @inline def postOrTrue: Expr = postcondition.getOrElse {
      Lambda(Seq(ValDef(FreshIdentifier("res", true), tfd.returnType)), BooleanLiteral(true))
    }
  }

  implicit class StainlessLookup(val p: Program { val trees: self.type }) {
    def lookup[T <: Definition : ClassTag](name: String): T = p.symbols.lookup[T](name)
  }
}
