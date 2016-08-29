/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

import trees._

case class Import(path: Seq[String], isWildcard: Boolean) extends Tree

sealed trait DefSet extends Tree {
  val classes: Seq[ClassDef] 
  val functions: Seq[FunDef]
  val imports: Seq[Import]
  val subs: Seq[DefSet]

  def allClasses: Seq[ClassDef] = classes ++ subs.flatMap(_.allClasses)
  def allFunctions: Seq[FunDef] = functions ++ subs.flatMap(_.allFunctions)
}

case class ModuleDef(classes: Seq[ClassDef], functions: Seq[FunDef], imports: Seq[Import], subs: Seq[DefSet]) extends DefSet
case class PackageDef(classes: Seq[ClassDef], functions: Seq[FunDef], imports: Seq[Import], subs: Seq[DefSet]) extends DefSet

class Program(pkg: PackageDef)(implicit val ctx: inox.InoxContext) extends inox.Program {
  val trees: xlang.trees.type = xlang.trees
  import trees._

  val symbols = NoSymbols.withClasses(pkg.allClasses).withFunctions(pkg.allFunctions)
}
