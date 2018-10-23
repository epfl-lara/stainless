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
  }

  case class LetClass(lcd: LocalClassDef, body: Expr) extends Expr with CachingTyped {
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
    implicit pctx: PrinterContext => withSymbols(methods.map(fd => Left(fd.toFunDef)), "def")
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

    case LetClass(lcd, body) =>
      p"""|$lcd
          |$body
          |"""

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

trait TreeTransformer extends oo.TreeTransformer {
  val s: Trees
  val t: methods.Trees
}

trait TreeDeconstructor extends methods.TreeDeconstructor { self =>
  protected val s: Trees
  protected val t: Trees

  import t.FunDefLocalOps

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
    case s.LetClass(lcd, body) =>
      (
        Seq(lcd.id),
        lcd.fields.map(_.toVariable),
        Seq(body),
        lcd.parents,
        lcd.flags,
        (ids, vars, es, parents, flags) => {
          val cd = t.LocalClassDef(
            ids.head,
            lcd.tparams.map(transformer.transform),
            parents,
            vars.map(_.toVal),
            lcd.methods.map(fd => transformer.transform(fd.toFunDef).toLocalMethodDef),
            flags
          )

          t.LetClass(cd, es(0))
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
