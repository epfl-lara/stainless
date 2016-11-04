/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package xlang

trait Trees extends oo.Trees { self =>

  case class IsField(isLazy: Boolean) extends Flag("field", Seq(isLazy))
  case object Ignore extends Flag("ignore", Seq.empty)

  override def extractFlag(name: String, args: Seq[Any]): Flag = (name, args) match {
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

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait TreeDeconstructor extends oo.TreeDeconstructor {

  protected val s: Trees
  protected val t: Trees

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.IsField(b) => (Seq(), Seq(), (_, _) => t.IsField(b))
    case s.Ignore => (Seq(), Seq(), (_, _) => t.Ignore)
    case _ => super.deconstruct(f)
  }
}
