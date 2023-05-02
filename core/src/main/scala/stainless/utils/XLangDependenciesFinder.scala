/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.trees as xt
import inox.utils.{NoPosition, Position}

import scala.collection.mutable.Map as MutableMap

/**
 * [[XLangDependenciesFinder]] find the set of dependencies for a function/class,
 * it is not thread safe and is designed for one and only one run!
 *
 * It returns only the *direct* dependencies, without the argument itself
 * although it could be a recursive function. Moreover, it doesn't capture
 * the notion of class hierarchy as it doesn't know about other classes.
 *
 * It also does **not** handle dependencies toward class invariant/methods
 * because this requires the knowledge of existing functions in addition to
 * the class itself.
 */
class XLangDependenciesFinder {
  import XLangDependenciesFinder.*

  private val deps: MutableMap[Identifier, DependencyInfo] = MutableMap.empty

  private abstract class TreeTraverser extends xt.ConcreteOOSelfTreeTraverser {
    def traverse(lcd: xt.LocalClassDef): Unit
    def traverse(lmd: xt.LocalMethodDef): Unit
    def traverse(ltd: xt.LocalTypeDef): Unit
  }

  private def add(id: Identifier, kind: IdentifierKind, pos: Position): Unit = {
    val curr = deps.getOrElseUpdate(id, DependencyInfo(kind, Seq.empty))
    deps += id -> curr.copy(positions = (curr.positions :+ pos).distinct)
  }

  private val finder = new TreeTraverser {
    override def traverse(e: xt.Expr): Unit = e match {
      case xt.FunctionInvocation(id, _, _) =>
        add(id, IdentifierKind.MethodOrFunction, e.getPos)
        super.traverse(e)

      case xt.MethodInvocation(_, id, _, _) =>
        add(id, IdentifierKind.MethodOrFunction, e.getPos)
        super.traverse(e)

      case xt.LetClass(lcds, body) =>
        lcds foreach { lcd =>
          traverse(lcd)
          lcd.methods foreach traverse
          traverse(body)

          deps --= lcds.map(_.id).toSet
          deps --= lcds.flatMap(_.methods).map(_.id).toSet
          deps --= lcds.flatMap(_.typeMembers).map(_.id).toSet
        }

      case xt.ClassConstructor(ct, _) =>
        add(ct.id, IdentifierKind.Class, e.getPos)
        super.traverse(e)

      case xt.LocalClassConstructor(ct, _) =>
        add(ct.id, IdentifierKind.Class, e.getPos)
        super.traverse(e)

      case _ => super.traverse(e)
    }

    override def traverse(pat: xt.Pattern): Unit = pat match {
      case xt.UnapplyPattern(_, _, id, _, _) =>
        add(id, IdentifierKind.MethodOrFunction, pat.getPos)
        super.traverse(pat)

      case _ => super.traverse(pat)
    }

    override def traverse(tpe: xt.Type): Unit = tpe match {
      case xt.ClassType(id, _) =>
        add(id, IdentifierKind.Class, tpe.getPos)
        super.traverse(tpe)

      case xt.RefinementType(vd, pred) =>
        traverse(pred)
        deps -= vd.id

      case xt.TypeSelect(expr, id) =>
        expr foreach traverse
        add(id, IdentifierKind.TypeSelection, tpe.getPos)
        super.traverse(tpe)

      case _ => super.traverse(tpe)
    }

    override def traverse(flag: xt.Flag): Unit = flag match {
      case xt.IsMethodOf(id) =>
        add(id, IdentifierKind.Class, NoPosition)
        super.traverse(flag)

      case _ => super.traverse(flag)
    }

    override def traverse(cd: xt.ClassDef): Unit = {
      cd.tparams foreach traverse
      cd.parents foreach traverse
      cd.fields foreach traverse
      cd.flags foreach traverse
    }

    override def traverse(lcd: xt.LocalClassDef): Unit = {
      lcd.tparams foreach traverse
      lcd.parents foreach traverse
      lcd.fields foreach traverse
      lcd.typeMembers foreach traverse
      lcd.flags foreach traverse
    }

    override def traverse(lmd: xt.LocalMethodDef): Unit =
      traverse(lmd.toFunDef)

    override def traverse(ltd: xt.LocalTypeDef): Unit =
      traverse(ltd.toTypeDef)
  }

  def apply(defn: xt.Definition): Map[Identifier, DependencyInfo] = defn match {
    case fd: xt.FunDef   => apply(fd)
    case cd: xt.ClassDef => apply(cd)
    case td: xt.TypeDef  => apply(td)
    case _: xt.ADTSort   => sys.error("There should be not sorts at this stage")
  }

  def apply(fd: xt.FunDef): Map[Identifier, DependencyInfo] = {
    finder.traverse(fd)
    deps -= fd.id
    deps --= fd.params.map(_.id)

    deps.toMap
  }

  def apply(cd: xt.ClassDef): Map[Identifier, DependencyInfo] = {
    finder.traverse(cd)
    deps -= cd.id
    deps --= cd.fields.map(_.id)

    deps.toMap
  }

  def apply(td: xt.TypeDef): Map[Identifier, DependencyInfo] = {
    td.tparams foreach finder.traverse
    finder.traverse(td.rhs)
    td.flags foreach finder.traverse
    deps -= td.id

    deps.toMap
  }
}
object XLangDependenciesFinder {
  case class DependencyInfo(kind: IdentifierKind, positions: Seq[Position])

  enum IdentifierKind {
    case Class
    case TypeDef
    case MethodOrFunction
    case TypeSelection
  }
}