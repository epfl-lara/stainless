/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait Trees extends methods.Trees with Definitions with Types { self =>

  type Symbols >: Null <: InnerClassesAbstractSymbols

  trait InnerClassesAbstractSymbols
    extends MethodsAbstractSymbols
       with innerclasses.DependencyGraph
       with innerclasses.TypeOps { self0: Symbols =>

    // The only value that can be assigned to `trees`, but that has to be
    // done in a concrete class explicitly overriding `trees`
    // Otherwise, we can run into initialization issue.
    protected val trees: self.type
    // More or less the same here
    protected val symbols: this.type

    @inline def localClasses: Seq[LocalClassDef] = _localClasses.get
    private[this] val _localClasses = inox.utils.Lazy({
      self0.functions.values.flatMap { fd =>
        exprOps.collect[LocalClassDef] {
          case LetClass(lcds, _) => lcds.toSet
          case _ => Set.empty
        } (fd.fullBody)
      }.toSeq
    })

    override def astSize: Int = {
      var result = 0
      val counter = new TreeTraverser {
        val trees: self.type = self

        override def traverse(fd: FunDef) = { result += 1; super.traverse(fd) }
        override def traverse(cd: ClassDef) = { result += 1; super.traverse(cd) }
        override def traverse(sort: ADTSort) = { result += 1; super.traverse(sort) }
        override def traverse(e: Expr) = { result += 1; super.traverse(e) }
        override def traverse(tpe: Type) = { result += 1; super.traverse(tpe) }
        override def traverse(pattern: Pattern) = { result += 1; super.traverse(pattern) }
        override def traverse(vd: ValDef) = { result += 1; super.traverse(vd) }
        override def traverse(id: Identifier): Unit = { result += 1; super.traverse(id) }
        override def traverse(tpd: TypeParameterDef): Unit = { result += 1; super.traverse(tpd) }
        override def traverse(flag: Flag): Unit = { result += 1; super.traverse(flag) }
        override def traverse(lcd: LocalClassDef): Unit = { result += 1; super.traverse(lcd) }
        override def traverse(lmd: LocalMethodDef): Unit = { result += 1; super.traverse(lmd) }
      }

      symbols.functions.values.foreach(counter.traverse)
      symbols.classes.values.foreach(counter.traverse)
      symbols.sorts.values.foreach(counter.traverse)
      symbols.typeDefs.values.foreach(counter.traverse)

      result
    }
  }

  case class LetClass(classes: Seq[LocalClassDef], body: Expr) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = body.getType
  }

  case class LocalThis(lct: LocalClassType) extends Expr with CachingTyped {
    protected def computeType(using Symbols): LocalClassType = lct
  }

  case class LocalClassConstructor(lct: LocalClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(using Symbols): LocalClassType = lct
  }

  case class LocalClassSelector(expr: Expr, selector: Identifier, tpe: Type) extends Expr with CachingTyped {
    protected def computeType(using Symbols): Type = expr.getType match {
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
    protected def computeType(using Symbols): Type = {
      receiver.getType match {
        case lct: LocalClassType =>
          method.tpe match {
            case FunctionType(from, to) =>
              val tpMap = (tparams zip tps).toMap
              val realFrom = from.map(typeOps.instantiateType(_, tpMap))
              val realTo = typeOps.instantiateType(to, tpMap)
              checkParamTypes(args.map(_.getType), realFrom, realTo)
            case _ => Untyped
          }
        case _ => Untyped
      }
    }
  }

  override val exprOps: innerclasses.ExprOps { val trees: self.type } = {
    class ExprOpsImpl(override val trees: self.type) extends innerclasses.ExprOps(trees)
    new ExprOpsImpl(self)
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

    case _ => super.getDeconstructor(that)
  }
}

trait Printer extends methods.Printer {
  protected val trees: Trees
  import trees._

  protected def localMethods(methods: Seq[LocalMethodDef]): PrintWrapper = PrintWrapper {
    withSymbols(methods.map(fd => Left(fd)), "def")
  }

  protected def localTypeDefs(typeDefs: Seq[LocalTypeDef]): PrintWrapper = PrintWrapper {
    withSymbols(typeDefs.map(td => Left(td)), "type")
  }

  override def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
    case cd: LocalClassDef =>
      if (cd.flags contains IsSealed) p"sealed "
      if (cd.flags contains IsAbstract) p"abstract " else p"case "
      for (an <- cd.flags) {
        p"""|@${an.asString(using ctx.opts)}
            |"""
      }
      p"class ${cd.id}"
      p"${nary(cd.tparams, ", ", "[", "]")}"
      if (cd.fields.nonEmpty) p"(${cd.fields})"
      if (cd.parents.nonEmpty) p" extends ${nary(cd.parents, " with ")}"
      p"""| {
          |  ${localTypeDefs(cd.typeMembers)}
          |
          |  ${localMethods(cd.methods)}
          |}"""

    case fd: LocalMethodDef =>
      p"${fd.toFunDef}"

    case td: LocalTypeDef =>
      p"${td.toTypeDef}"

    case LetClass(lcds, body) =>
      lcds foreach { lcd =>
        p"""|$lcd
            |"""
      }
      p"$body"

    case LocalThis(_) =>
      p"this"

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
      lcd.typeMembers.map(transform(_, env)),
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

  def transform(ltd: s.LocalTypeDef): t.LocalTypeDef = {
    transform(ltd, initEnv)
  }

  def transform(ltd: s.LocalTypeDef, env: Env): t.LocalTypeDef = {
    t.LocalTypeDef(
      transform(ltd.id, env),
      ltd.tparams.map(transform(_, env)),
      transform(ltd.rhs, env),
      ltd.flags.map(transform(_, env))
    ).copiedFrom(ltd)
  }
}

trait TreeTransformer extends transformers.TreeTransformer with DefinitionTransformer

class ConcreteTreeTransformer(override val s: Trees, override val t: Trees) extends TreeTransformer

trait DefinitionTraverser extends oo.DefinitionTraverser {
  val trees: Trees
  import trees._

  def traverse(lcd: LocalClassDef): Unit = {
    val env = initEnv
    traverse(lcd, initEnv)
  }

  def traverse(lcd: LocalClassDef, env: Env): Unit = {
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

  class TransformerImpl(override val s: self.s.type, override val t: self.t.type) extends ConcreteTreeTransformer(s, t)
  val transformer = new TransformerImpl(self.s, self.t)

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
            (lcd @ s.LocalClassDef(_, tparams, parents, fields, _, _, flags), id) <- classes zip ids
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
              lcd.methods.map(fd => transformer.transform(fd)),     // FIXME
              lcd.typeMembers.map(td => transformer.transform(td)), // FIXME
              currFlags
            ).copiedFrom(lcd)
          }

          t.LetClass(newClasses, es.head)
        }
      )

    case s.LocalThis(lct) =>
      (Seq(), Seq(), Seq(), Seq(lct), Seq(), (_, _, _, tps, _) =>
        t.LocalThis(tps(0).asInstanceOf[t.LocalClassType]))

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

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor