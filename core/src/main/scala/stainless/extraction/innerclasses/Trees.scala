/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait Trees extends methods.Trees with Definitions with Types { self =>

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
    with DependencyGraph
    with TypeOps { self0: Symbols =>

    @inline def localClasses: Seq[LocalClassDef] = _localClasses.get
    private[this] val _localClasses = inox.utils.Lazy({
      self0.functions.values.flatMap { fd =>
        exprOps.collect[LocalClassDef] {
          case LetClass(lcds, _) => lcds.toSet
          case _ => Set.empty
        } (fd.fullBody)
      }.toSeq
    })
  }

  case class LetClass(classes: Seq[LocalClassDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = body.getType
  }

  case class LocalClassConstructor(lct: LocalClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): LocalClassType = lct
  }

  case class LocalClassSelector(expr: Expr, selector: Identifier, tpe: Type) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = expr.getType match {
      case lct: LocalClassType => tpe
      case _ => Untyped
    }
  }

  case class LocalMethodInvocation(
    receiver: Expr,
    method: Variable,
    tparams: Seq[TypeParameter],
    tps: Seq[Type],
    args: Seq[Expr]
  ) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = method.tpe match {
      case FunctionType(from, to) =>
        val tpMap = (tparams zip tps).toMap
        val realFrom = from.map(typeOps.instantiateType(_, tpMap))
        val realTo = typeOps.instantiateType(to, tpMap)
        checkParamTypes(args.map(_.getType), realFrom, realTo)
      case _ => Untyped
    }
  }

  override val exprOps: ExprOps { val trees: Trees.this.type } = new {
    protected val trees: Trees.this.type = Trees.this
  } with ExprOps

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new innerclasses.TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }

}

trait Printer extends methods.Printer {
  protected val trees: Trees
  import trees._

  protected def localMethods(methods: Seq[LocalMethodDef]): PrintWrapper = {
    implicit pctx: PrinterContext => withSymbols(methods.map(fd => Left(fd)), "def")
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case cd: LocalClassDef =>
      p"class ${cd.id}"
      p"${nary(cd.tparams, ", ", "[", "]")}"
      if (cd.fields.nonEmpty) p"(${cd.fields})"
      if (cd.parents.nonEmpty) p" extends ${nary(cd.parents, " with ")}"
      p"""| {
          |  ${localMethods(cd.methods)}
          |}"""

    case fd: LocalMethodDef =>
      for (an <- fd.flags) {
        p"""|@${an.asString(ctx.opts)}
            |"""
      }

      p"def ${fd.id}${nary(fd.tparams, ", ", "[", "]")}"
      if (fd.params.nonEmpty) {
        p"(${fd.params})"
      }

      p": ${fd.returnType} = "
      p"${fd.fullBody}"

    case LetClass(lcds, body) =>
      lcds foreach { lcd =>
        p"""|$lcd
            |"""
      }
      p"$body"

    case LocalClassConstructor(ct, args) =>
      p"$ct(${nary(args, ", ")})"

    case LocalClassSelector(expr, id, _) =>
      p"$expr.$id"

    case LocalMethodInvocation(caller, method, tparams, tps, args) =>
      p"$caller.${method.id}${nary(tps, ", ", "[", "]")}"
      if (args.nonEmpty) p"($args)"

    case lct: LocalClassType =>
      p"${lct.toClassType}"

    case _ => super.ppBody(tree)
  }

  override protected def isSimpleExpr(e: Expr): Boolean = e match {
    case _: LetClass => false
    case _ => super.isSimpleExpr(e)
  }

  override protected def noBracesSub(ex: Tree): Seq[Expr] = ex match {
    case LetClass(_, bd) => Seq(bd)
    case _ => super.noBracesSub(ex)
  }

  override protected def requiresBraces(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (_: LetClass, Some(_: LetClass)) => false
    case _ => super.requiresBraces(ex, within)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]) = (ex, within) match {
    case (_, Some(_: LetClass)) => false
    case _ => super.requiresParentheses(ex, within)
  }
}

trait DefinitionTransformer extends oo.DefinitionTransformer {
  val s: Trees
  val t: Trees

  def transform(lcd: s.LocalClassDef): t.LocalClassDef = {
    val env = initEnv

    t.LocalClassDef(
      transform(lcd.id, env),
      lcd.tparams.map(transform(_, env)),
      lcd.parents.map(transform(_, env)),
      lcd.fields.map(transform(_, env)),
      lcd.methods.map(transform(_, env)),
      lcd.flags.map(transform(_, env))
    ).copiedFrom(lcd)
  }

  def transform(lmd: s.LocalMethodDef): t.LocalMethodDef = {
    transform(lmd, initEnv)
  }

  def transform(lmd: s.LocalMethodDef, env: Env): t.LocalMethodDef = {
    t.LocalMethodDef(
      transform(lmd.id, env),
      lmd.tparams.map(transform(_, env)),
      lmd.params.map(transform(_, env)),
      transform(lmd.returnType, env),
      transform(lmd.fullBody, env),
      lmd.flags.map(transform(_, env))
    ).copiedFrom(lmd)
  }
}

trait TreeTransformer extends transformers.TreeTransformer with DefinitionTransformer

trait DefinitionTraverser extends oo.DefinitionTraverser {
  val trees: Trees
  import trees._

  def traverse(lcd: LocalClassDef): Unit = {
    val env = initEnv

    traverse(lcd.id, env)
    lcd.tparams.foreach(traverse(_, env))
    lcd.parents.foreach(traverse(_, env))
    lcd.fields.foreach(traverse(_, env))
    lcd.methods.foreach(traverse(_, env))
    lcd.flags.foreach(traverse(_, env))
  }

  def traverse(lmd: LocalMethodDef): Unit = {
    traverse(lmd, initEnv)
  }

  def traverse(lmd: LocalMethodDef, env: Env): Unit = {
    traverse(lmd.id, env)
    lmd.tparams.map(traverse(_, env))
    lmd.params.map(traverse(_, env))
    traverse(lmd.returnType, env)
    traverse(lmd.fullBody, env)
    lmd.flags.map(traverse(_, env))
  }
}

trait TreeTraverser extends transformers.TreeTraverser with DefinitionTraverser

trait TreeDeconstructor extends methods.TreeDeconstructor { self =>
  protected val s: Trees
  protected val t: Trees

  object transformer extends TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  override def deconstruct(tpe: s.Type): Deconstructed[t.Type] = tpe match {
    case s.LocalClassType(id, tparams, tps, parents) =>
      (Seq(id), Seq(), Seq(), tps ++ parents, Seq(), (ids, _, _, allTps, _) =>
        t.LocalClassType(ids.head,
          tparams.map(transformer.transform),
          allTps take tps.length,
          allTps drop tps.length))

    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.LetClass(classes, body) =>
      (
        classes map (_.id),
        classes flatMap (_.fields)  map (_.toVariable),
        Seq(body),
        (classes flatMap (c => c.tparams.map(_.tp))) ++ (classes flatMap (_.parents)),
        classes flatMap (_.flags),
        (ids, vs, es, tps, flags) => {
          var rvs = vs
          var rtps = tps
          var rflags = flags

          val newClasses = for {
            (lcd @ s.LocalClassDef(_, tparams, parents, fields, _, flags), id) <- classes zip ids
          } yield {
            val (currVs, nextVs) = rvs.splitAt(fields.size)
            rvs = nextVs

            val (currTps, nextTps) = rtps.splitAt(tparams.size + parents.size)
            rtps = nextTps

            val (currTparams, currParents) = currTps.splitAt(tparams.size)

            val (currFlags, nextFlags) = rflags.splitAt(flags.size)
            rflags = nextFlags

            t.LocalClassDef(
              id,
              currTparams map (tp => t.TypeParameterDef(tp.asInstanceOf[t.TypeParameter]).copiedFrom(tp)),
              currParents,
              currVs.map(_.toVal),
              lcd.methods.map(fd => transformer.transform(fd)), // FIXME
              currFlags
            ).copiedFrom(lcd)
          }

          t.LetClass(newClasses, es.head)
        }
      )

    case s.LocalClassConstructor(lct, args) =>
      (Seq(), Seq(), args, Seq(lct), Seq(), (_, _, es, tps, _) =>
        t.LocalClassConstructor(tps(0).asInstanceOf[t.LocalClassType], es))

    case s.LocalMethodInvocation(receiver, method, tparams, tps, args) =>
      (Seq(), Seq(method), receiver +: args, tparams ++ tps, Seq(), (_, vs, es, tps, _) => {
        val (ntparams, ntps) = tps.splitAt(tparams.size)
        t.LocalMethodInvocation(es(0), vs(0), ntparams.map(_.asInstanceOf[t.TypeParameter]), ntps, es.tail)
      })

    case s.LocalClassSelector(expr, id, tpe) =>
      (Seq(), Seq(), Seq(expr), Seq(tpe), Seq(), (_, _, es, tps, _) =>
        t.LocalClassSelector(es(0), id, tps(0)))

    case _ => super.deconstruct(e)
  }
}
