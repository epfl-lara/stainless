/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package innerfuns

trait Trees extends inlining.Trees { self =>

  case class LocalFunDef(name: ValDef, tparams: Seq[TypeParameterDef], body: Lambda) extends Definition {
    val id = name.id
    val flags = name.flags
  }

  case class LetRec(fds: Seq[LocalFunDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (fds.forall { case LocalFunDef(vd, tparams, body) =>
        vd.tpe != Untyped && vd.tpe == body.getType
      }) body.getType else Untyped
    }
  }

  case class ApplyLetRec(fun: Variable, tparams: Seq[TypeParameter], args: Seq[Expr]) extends Expr with CachingTyped {
    def tps(implicit s: Symbols): Option[Seq[Type]] = fun.tpe match {
      case FunctionType(from, to) =>
        s.instantiation_>:(tupleTypeWrap(from), tupleTypeWrap(args.map(_.getType))) match {
          case Some(map) if map.filterNot(p => p._1 == p._2).keySet subsetOf tparams.toSet =>
            Some(tparams.map(map))
          case _ => None
        }
      case _ => None
    }

    protected def computeType(implicit s: Symbols): Type = (fun.tpe, tps) match {
      case (FunctionType(_, to), Some(tps)) => s.instantiateType(to, (tparams zip tps).toMap)
      case _ => Untyped
    }
  }


  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps


  /* ========================================
   *               EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }


  /* ========================================
   *               PRINTERS
   * ======================================== */

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case LetRec(defs, body) =>
      defs foreach { case (LocalFunDef(name, tparams, Lambda(args, body))) =>
        for (f <- name.flags) p"""|${f.asString(ctx.opts)}
                                  |"""
        p"def ${name.id}${nary(tparams, ", ", "[", "]")}"
        if (args.nonEmpty) p"(${args})"

        p": ${name.tpe.asInstanceOf[FunctionType].to} = $body"
        p"""|
            |"""
      }

      p"$body"

    case ApplyLetRec(fun, tparams, args) =>
      p"${fun.id}${nary(tparams, ",", "[", "]")}${nary(args, ", ", "(", ")")}"

    case LocalFunDef(name, tparams, body) =>
      for (f <- name.flags) p"""|@${f.asString(ctx.opts)}
                                |"""

      p"def ${name.id}${nary(tparams, ", ", "[", "]")}"
      if (body.args.nonEmpty) p"(${body.args})"
      p": ${name.tpe.asInstanceOf[FunctionType].to} = "
      p"${body.body}"

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case _: LetRec => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(ex: Tree): Seq[Expr] = ex match {
    case LetRec(_, bd) => Seq(bd)
    case _ => super.noBracesSub(ex)
  }

  override protected def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (_: LetRec, Some(_: LetRec)) => false
    case _ => super.requiresBraces(ex, within)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (_, Some(_: LetRec)) => false
    case _ => super.requiresParentheses(ex, within)
  }
}

trait TreeDeconstructor extends inlining.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.LetRec(defs, body) => (
      defs map (_.name.toVariable),
      defs.map(_.body) :+ body,
      defs.flatMap(_.tparams).map(_.tp),
      (vs, es, tps) => {
        var restTps = tps
        var restFuns = defs
        t.LetRec(
          vs.zip(es.init).map{ case (v, e) =>
            val howMany = defs.head.tparams.size
            val (tps, rest) = restTps splitAt howMany
            restTps = restTps drop howMany
            restFuns = restFuns.tail
            t.LocalFunDef(v.toVal, tps.map(tp => t.TypeParameterDef(tp.asInstanceOf[t.TypeParameter])), e.asInstanceOf[t.Lambda])
          },
          es.last
        )
      })

    case s.ApplyLetRec(fun, tparams, args) =>
      (Seq(fun), args, tparams, (vs, es, tps) => {
        t.ApplyLetRec(vs.head, tps.map(_.asInstanceOf[t.TypeParameter]), es)
      })

    case other =>
      super.deconstruct(other)
  }

}

trait ExprOps extends extraction.ExprOps {
  protected val trees: Trees
  import trees._
  /** Returns functions in directly nested LetDefs */
  def directlyNestedFunDefs(e: Expr): Set[LocalFunDef] = {
    fold[Set[LocalFunDef]]{
      case (LetRec(fds,_), fromFdsFromBd) => fromFdsFromBd.last ++ fds
      case (_,             subs)          => subs.flatten.toSet
    }(e)
  }

  def innerFunctionCalls(e: Expr) = {
    collect[Identifier] {
      case ApplyLetRec(fd, _, _) => Set(fd.id)
      case _ => Set()
    }(e)
  }
}
