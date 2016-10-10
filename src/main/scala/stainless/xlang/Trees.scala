/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package xlang

import stainless.intermediate.oo

trait Trees extends oo.Trees {

  case class IsField(isLazy: Boolean) extends Flag("field", Seq(isLazy))
  case object IsInvariant extends Flag("invariant", Seq.empty)
  case object IsAbstract extends Flag("abstract", Seq.empty)

  case object Ignore extends Flag("ignore", Seq.empty)
  case object Inline extends Flag("inline", Seq.empty)

  override def extractFlag(name: String, args: Seq[Any]): Flag = (name, args) match {
    case ("stainless.annotation.package$.ignore", Seq()) => Ignore
    case ("stainless.annotation.package$.inline", Seq()) => Inline
    case _ => super.extractFlag(
      if (name.startsWith("stainless.annotation.package$.")) name drop 30 else name,
      args
    )
  }

  /** $encodingof `import some.package.Path` or `import some.package.path._` */
  case class Import(path: Seq[String], isWildcard: Boolean) extends Tree

  /** Represents a static collection of definitions.
    *
    * @see [[PackageDef]] - corresponds to scala packages
    * @see [[ModuleDef]]  - corresponds to scala objects
    */
  sealed trait DefSet extends Tree

  /** $encodingof `package name; ...` */
  case class PackageDef(id: Identifier, imports: Seq[Import], classes: Seq[Identifier], subs: Seq[DefSet]) extends DefSet

  /** $encodingof `object name { ... }` */
  case class ModuleDef(id: Identifier, imports: Seq[Import], classes: Seq[Identifier], functions: Seq[Identifier], subs: Seq[DefSet]) extends DefSet

  protected def classes(cls: Seq[Identifier]): PrintWrapper = {
    implicit pctx: PrinterContext =>
      withSymbols(cls.map(id => pctx.opts.symbols.flatMap(_.lookupClass(id)) match {
        case Some(cd) => Left(cd)
        case None => Right(id)
      }), "class")
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case Import(path, isWildcard) =>
      p"import ${path.mkString(".")}"
      if (isWildcard) p"._"

    case PackageDef(id, imports, cls, subs) =>
      p"""|package $id
          |"""

      if (imports.nonEmpty) p"""|${nary(imports, "\n")}
                                |"""
      if (cls.nonEmpty)     p"""|
                                |${classes(cls)}
                                |"""
      if (subs.nonEmpty)    p"""|
                                |${nary(subs, "\n\n")}
                                |"""

    case ModuleDef(id, imports, cls, funs, subs) =>
      p"""|object $id {
          |"""
      if (imports.nonEmpty) p"""|
                                |  ${nary(imports, "\n")}
                                |"""
      if (cls.nonEmpty)     p"""|
                                |  ${classes(cls)}
                                |"""
      if (funs.nonEmpty)    p"""|
                                |  ${functions(funs)}
                                |"""
      if (subs.nonEmpty)    p"""|
                                |  ${nary(subs, "\n\n")}
                                |"""
      p"|}"

    case cd: ClassDef =>
      p"class ${cd.id}"
      p"${nary(cd.tparams, ", ", "[", "]")}"
      if (cd.fields.nonEmpty) p"(${cd.fields})"

      cd.parent.foreach { id =>
        p" extends $id${nary(cd.tparams, ", ", "[", "]")}"
      }

      if (cd.methods.nonEmpty) {
        p""" {
            |  ${functions(cd.methods)}
            |}"""
      }

    case _ => super.ppBody(tree)
  }

}

trait TreeDeconstructor extends oo.TreeDeconstructor {

  protected val s: Trees
  protected val t: Trees

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.IsField(b) => (Seq(), Seq(), (_, _) => t.IsField(b))
    case s.IsInvariant => (Seq(), Seq(), (_, _) => t.IsInvariant)
    case s.IsAbstract => (Seq(), Seq(), (_, _) => t.IsAbstract)
    case s.Ignore => (Seq(), Seq(), (_, _) => t.Ignore)
    case s.Inline => (Seq(), Seq(), (_, _) => t.Inline)
    case _ => super.deconstruct(f)
  }
}