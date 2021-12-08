/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.{ trees => xt }

import scala.collection.mutable.{ HashSet => MutableSet }

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

  private val deps: MutableSet[Identifier] = MutableSet.empty

  private abstract class TreeTraverser extends xt.ConcreteOOSelfTreeTraverser {
    def traverse(lcd: xt.LocalClassDef): Unit
    def traverse(lmd: xt.LocalMethodDef): Unit
    def traverse(ltd: xt.LocalTypeDef): Unit
  }

  private val finder = new TreeTraverser {
    override def traverse(e: xt.Expr): Unit = e match {
      case xt.FunctionInvocation(id, _, _) =>
        deps += id
        super.traverse(e)

      case xt.MethodInvocation(_, id, _, _) =>
        deps += id
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

      case _ => super.traverse(e)
    }

    override def traverse(pat: xt.Pattern): Unit = pat match {
      case xt.UnapplyPattern(_, _, id, _, _) =>
        deps += id
        super.traverse(pat)

      case _ => super.traverse(pat)
    }

    override def traverse(tpe: xt.Type): Unit = tpe match {
      case xt.ClassType(id, _) =>
        deps += id
        super.traverse(tpe)

      case xt.RefinementType(vd, pred) =>
        traverse(pred)
        deps -= vd.id

      case xt.TypeSelect(expr, id) =>
        expr foreach traverse
        deps += id
        super.traverse(tpe)

      case _ => super.traverse(tpe)
    }

    override def traverse(flag: xt.Flag): Unit = flag match {
      case xt.IsMethodOf(id) =>
        deps += id
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

  def apply(defn: xt.Definition): Set[Identifier] = defn match {
    case fd: xt.FunDef   => apply(fd)
    case cd: xt.ClassDef => apply(cd)
    case td: xt.TypeDef  => apply(td)
    case _: xt.ADTSort   => sys.error("There should be not sorts at this stage")
  }

  def apply(fd: xt.FunDef): Set[Identifier] = {
    finder.traverse(fd)
    deps -= fd.id
    deps --= fd.params.map(_.id)

    deps.toSet
  }

  def apply(cd: xt.ClassDef): Set[Identifier] = {
    finder.traverse(cd)
    deps -= cd.id
    deps --= cd.fields.map(_.id)

    deps.toSet
  }

  def apply(td: xt.TypeDef): Set[Identifier] = {
    td.tparams foreach finder.traverse
    finder.traverse(td.rhs)
    td.flags foreach finder.traverse
    deps -= td.id

    deps.toSet
  }
}
