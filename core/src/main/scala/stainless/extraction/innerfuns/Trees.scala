/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package innerfuns
import inox.utils.{NoPosition, Position}

trait Trees extends inlining.Trees { self =>

  case class LocalFunDef(name: ValDef, tparams: Seq[TypeParameterDef], body: Lambda) extends Definition {
    val id = name.id
    val flags = name.flags

    override def getPos: Position = super.getPos match {
      case NoPosition => Position.between(name.getPos, body.getPos)
      case pos => pos
    }
  }

  case class LetRec(fds: Seq[LocalFunDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      if (fds.forall { case LocalFunDef(vd, tparams, body) =>
        vd.tpe != Untyped && vd.tpe == body.getType
      }) body.getType else Untyped
    }
  }

  case class ApplyLetRec(fun: Variable, tparams: Seq[TypeParameter], tps: Seq[Type], args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = fun.tpe match {
      case FunctionType(from, to) =>
        val tpMap = (tparams zip tps).toMap
        val realFrom = from.map(s.instantiateType(_, tpMap))
        val realTo = s.instantiateType(to, tpMap)
        checkParamTypes(args.map(_.getType), realFrom, realTo)
      case _ => Untyped
    }
  }


  /** Abstraction over [[FunDef]] and [[LocalFunDef]] to provide a unified interface to both
    * of them as these are generally not distinguished during program transformations. */
  sealed abstract class FunAbstraction(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val params: Seq[ValDef],
    val returnType: Type,
    val fullBody: Expr,
    val flags: Set[Flag]
  ) extends inox.utils.Positioned {
    def copy(
      id: Identifier = id,
      tparams: Seq[TypeParameterDef] = tparams,
      params: Seq[ValDef] = params,
      returnType: Type = returnType,
      fullBody: Expr = fullBody,
      flags: Set[Flag] = flags
    ): FunAbstraction = to(self)(id, tparams, params, returnType, fullBody, flags)

    def to(t: Trees)(
      id: Identifier,
      tparams: Seq[t.TypeParameterDef],
      params: Seq[t.ValDef],
      returnType: t.Type,
      fullBody: t.Expr,
      flags: Set[t.Flag]
    ): t.FunAbstraction

    def toFun: FunDef = asInstanceOf[Outer].fd
    def toLocal: LocalFunDef = asInstanceOf[Inner].fd
  }

  case class Outer(fd: FunDef) extends FunAbstraction(
    fd.id, fd.tparams, fd.params, fd.returnType, fd.fullBody, fd.flags) {
    setPos(fd)

    def to(t: Trees)(
      id: Identifier,
      tparams: Seq[t.TypeParameterDef],
      params: Seq[t.ValDef],
      returnType: t.Type,
      fullBody: t.Expr,
      flags: Set[t.Flag]
    ): t.Outer = t.Outer(new t.FunDef(id, tparams, params, returnType, fullBody, flags).copiedFrom(fd))
  }

  case class Inner(fd: LocalFunDef) extends FunAbstraction(
    fd.name.id, fd.tparams, fd.body.args, fd.name.tpe.asInstanceOf[FunctionType].to, fd.body.body, fd.name.flags) {
    setPos(fd.name)

    def to(t: Trees)(
      id: Identifier,
      tparams: Seq[t.TypeParameterDef],
      params: Seq[t.ValDef],
      returnType: t.Type,
      fullBody: t.Expr,
      flags: Set[t.Flag]
    ): t.Inner = t.Inner(t.LocalFunDef(
      t.ValDef(id, t.FunctionType(params.map(_.tpe), returnType).copiedFrom(returnType), flags).copiedFrom(fd.name),
      tparams,
      t.Lambda(params, fullBody).copiedFrom(fullBody)
    ))
  }

  object FunInvocation {
    def unapply(e: Expr): Option[(Identifier, Seq[Type], Seq[Expr], (Identifier, Seq[Type], Seq[Expr]) => Expr)] = e match {
      case FunctionInvocation(id, tps, es) =>
        Some((id, tps, es, FunctionInvocation))
      case ApplyLetRec(fun, tparams, tps, args) =>
        Some((fun.id, tps, args, (id, tps, args) => ApplyLetRec(fun.copy(id = id), tparams, tps, args)))
      case _ => None
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
}

trait Printer extends inlining.Printer {
  protected val trees: Trees
  import trees._

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

    case ApplyLetRec(fun, tparams, tps, args) =>
      p"${fun.id}${nary(tps, ",", "[", "]")}${nary(args, ", ", "(", ")")}"

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
        t.LetRec(
          (vs zip es.init zip defs).map { case ((v, e), d) =>
            val (tps, rest) = restTps splitAt d.tparams.size
            restTps = rest
            t.LocalFunDef(v.toVal, tps.map(tp => t.TypeParameterDef(tp.asInstanceOf[t.TypeParameter])), e.asInstanceOf[t.Lambda])
          },
          es.last
        )
      })

    case s.ApplyLetRec(fun, tparams, tps, args) =>
      (Seq(fun), args, tparams ++ tps, (vs, es, tps) => {
        val (ntparams, ntps) = tps.splitAt(tparams.size)
        t.ApplyLetRec(vs.head, ntparams.map(_.asInstanceOf[t.TypeParameter]), ntps, es)
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
      case ApplyLetRec(fd, _, _, _) => Set(fd.id)
      case _ => Set()
    }(e)
  }
}
