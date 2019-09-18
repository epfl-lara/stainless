/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerfuns
import inox.utils.{NoPosition, Position}

trait Trees extends inlining.Trees with Definitions { self =>

  case class LetRec(fds: Seq[LocalFunDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (fds.forall { case fd @ LocalFunDef(_, _, _, _, fullBody, _) =>
        s.isSubtypeOf(fullBody.getType, fd.getType)
      }) body.getType else Untyped
    }
  }

  case class ApplyLetRec(
    id: Identifier,
    tparams: Seq[TypeParameter],
    tpe: FunctionType,
    tps: Seq[Type],
    args: Seq[Expr]
  ) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      val tpMap = (tparams zip tps).toMap
      val realFrom = tpe.from.map(tpe => typeOps.instantiateType(tpe.getType, tpMap))
      val realTo = typeOps.instantiateType(tpe.to.getType, tpMap)
      checkParamTypes(args.map(_.getType), realFrom, realTo)
    }
  }


  /** Abstract over [[FunctionInvocation]] and [[ApplyLetRec]] to provide a unified interface
    * to both of them as they have strong commonalities. */
  object FunInvocation {
    def unapply(e: Expr): Option[(Identifier, Seq[Type], Seq[Expr], (Identifier, Seq[Type], Seq[Expr]) => Expr)] = e match {
      case FunctionInvocation(id, tps, es) =>
        Some((id, tps, es, FunctionInvocation))
      case ApplyLetRec(id, tparams, tpe, tps, args) =>
        Some((id, tps, args, (id, tps, args) => ApplyLetRec(id, tparams, tpe, tps, args)))
      case _ => None
    }
  }


  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps


  /* ========================================
   *               EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends inlining.Printer {
  protected val trees: Trees
  import trees._

  override protected def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case LetRec(defs, body) =>
      defs foreach { fd =>
        p"""|$fd
            |"""
      }

      p"$body"

    case ApplyLetRec(id, tparams, tpe, tps, args) =>
      p"$id${nary(tps, ",", "[", "]")}${nary(args, ", ", "(", ")")}"

    case LocalFunDef(id, tparams, params, returnType, fullBody, flags) =>
      for (f <- flags) p"""|@${f.asString(ctx.opts)}
                           |"""
      p"def ${id}${nary(tparams, ", ", "[", "]")}"
      if (params.nonEmpty) p"($params)"

      p": $returnType = $fullBody"

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

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.LetRec(defs, body) => (
      defs map (_.id),
      defs flatMap (_.params) map (_.toVariable),
      (defs map (_.fullBody)) :+ body,
      defs flatMap (d => (d.tparams map (_.tp)) :+ d.returnType),
      defs flatMap (_.flags),
      (ids, vs, es, tps, flags) => {
        var rvs = vs
        var rtps = tps
        var rflags = flags

        val newFds = for {
          ((fd @ s.LocalFunDef(_, tparams, params, _, _, flags), id), e) <- defs zip ids zip es.init
        } yield {
          val (currVs, nextVs) = rvs.splitAt(params.size)
          rvs = nextVs

          val (currTps, nextTps) = rtps.splitAt(tparams.size + 1)
          rtps = nextTps

          val (currFlags, nextFlags) = rflags.splitAt(flags.size)
          rflags = nextFlags

          t.LocalFunDef(
            id,
            currTps.init.map(tp => t.TypeParameterDef(tp.asInstanceOf[t.TypeParameter]).copiedFrom(tp)),
            currVs.map(_.toVal),
            currTps.last,
            e,
            currFlags
          ).copiedFrom(fd)
        }

        t.LetRec(newFds, es.last)
      })

    case s.ApplyLetRec(id, tparams, tpe, tps, args) =>
      (Seq(id), Seq(), args, (tparams :+ tpe) ++ tps, Seq(), (ids, _, es, tps, _) => {
        val (ntparams, ntps) = tps.splitAt(tparams.size)
        t.ApplyLetRec(
          ids.head,
          ntparams.map(_.asInstanceOf[t.TypeParameter]),
          ntps.head.asInstanceOf[t.FunctionType],
          ntps.tail,
          es
        )
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
      case ApplyLetRec(id, _, _, _, _) => Set(id)
      case _ => Set()
    }(e)
  }

  override def variablesOf(e: Expr): Set[Variable] = e match {
    case LetRec(fds, body) => variablesOf(body) ++ fds.flatMap(_.freeVariables)
    case _ => super.variablesOf(e)
  }
}
