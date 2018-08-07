/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package xlang

trait Trees extends methods.Trees { self =>

  case object Ignore extends Flag("ignore", Seq.empty)

  override def extractFlag(name: String, args: Seq[Expr]): Flag = (name, args) match {
    case ("ignore", Seq()) => Ignore
    case ("extern", Seq()) => Extern
    case _ => super.extractFlag(name, args)
  }

  /** $encodingof `import some.package.Path` or `import some.package.path._` */
  case class Import(path: Seq[String], isWildcard: Boolean) extends Tree

  /** $encodingof `package name; ...` */
  case class UnitDef(id: Identifier, imports: Seq[Import], classes: Seq[Identifier], modules: Seq[ModuleDef], isMain: Boolean) extends Tree {
    def allClasses: Seq[Identifier] = modules.flatMap(_.allClasses) ++ classes 

    def allFunctions(implicit s: Symbols): Seq[Identifier] =
      classes.flatMap(s.getClass(_).methods) ++
      modules.flatMap(_.allFunctions)
  }

  /** $encodingof `object name { ... }` */
  case class ModuleDef(id: Identifier, imports: Seq[Import], classes: Seq[Identifier], functions: Seq[Identifier], modules: Seq[ModuleDef]) extends Tree {
    def allClasses: Seq[Identifier] = modules.flatMap(_.allClasses) ++ classes

    def allFunctions(implicit s: Symbols): Seq[Identifier] =
      classes.flatMap(s.getClass(_).methods) ++
      modules.flatMap(_.allFunctions) ++
      functions
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}


trait Printer extends methods.Printer {
  val trees: Trees
  import trees._

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

    case UnitDef(id, imports, cls, subs, _) =>
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

    case _ => super.ppBody(tree)
  }
}


trait TreeDeconstructor extends methods.TreeDeconstructor {

  protected val s: Trees
  protected val t: Trees

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.Ignore => (Seq(), Seq(), Seq(), (_, _, _) => t.Ignore)
    case _ => super.deconstruct(f)
  }
}
