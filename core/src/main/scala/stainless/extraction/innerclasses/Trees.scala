/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

import inox.utils.{NoPosition, Position}
import scala.collection.mutable.{Map => MutableMap}

trait Trees extends methods.Trees { self =>

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols
    with TypeOps { self0: Symbols =>
  }

  case class LocalClassDef(cd: ClassDef, methods: Seq[FunDef]) extends Definition {
    val id = cd.id
    val flags = cd.flags
    val tparams = cd.tparams
    val fields = cd.fields
    val typeArgs = cd.typeArgs

    def parent(implicit s: Symbols): TypedClassDef = cd.ancestors.head

    def typed(implicit s: Symbols): TypedLocalClassDef = {
      TypedLocalClassDef(this, cd.typed)
    }

    override def getPos: Position = cd.getPos
  }

  case class TypedLocalClassDef(lcd: LocalClassDef, tcd: TypedClassDef)(implicit val symbols: Symbols) extends Tree {
    @inline def id: Identifier = lcd.id
    @inline def typeMap: Map[TypeParameter, Type] = tcd.typeMap
    @inline def fields: Seq[ValDef] = tcd.fields
    @inline def methods: Seq[FunDef] = lcd.methods
    @inline def toType = tcd.toType
    @inline def parentType = lcd.parent.toType
  }

  case class LetClass(lcd: LocalClassDef, body: Expr) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      body.getType(s.withClasses(Seq(lcd.cd)))
    }
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

  case class LocalClassType(cd: ClassDef, tps: Seq[Type]) extends Type {
    lazy val toClassType: ClassType = ClassType(cd.id, tps)
    lazy val toNonLocalType: ClassType = cd.parents.headOption.getOrElse(toClassType)

    def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] = {
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _, _) => vd }
          .orElse(tcd.parents.reverse.view.flatMap(rec).headOption)
      }
      rec(cd.typed)
    }
  }

  override protected def getField(tpe: Type, selector: Identifier)(implicit s: Symbols): Option[ValDef] = tpe match {
    case lct: LocalClassType => lct.getField(selector)
    case _ => super.getField(tpe, selector)
  }

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

  protected def localMethods(funs: Seq[FunDef]): PrintWrapper = {
    implicit pctx: PrinterContext => withSymbols(funs.map(Left(_)), "def")
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case LocalClassDef(cd, methods) =>
      p"""|$cd {
          |  ${localMethods(methods)}
          |}"""

    case LetClass(lcd, body) =>
      p"""|$lcd
          |
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
}

trait TreeTransformer extends oo.TreeTransformer {
  val s: Trees
  val t: methods.Trees
}

trait TreeDeconstructor extends methods.TreeDeconstructor { self =>
  protected val s: Trees
  protected val t: Trees

  object transformer extends TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  override def deconstruct(tpe: s.Type): DeconstructedType = tpe match {
    case s.LocalClassType(cd: s.ClassDef, tps) => (Seq(), tps, Seq(), (_, tps, _) =>
      t.LocalClassType(transformer.transform(cd), tps))

    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(e: s.Expr): DeconstructedExpr = e match {
    case s.LetClass(s.LocalClassDef(cd, methods), body) =>
      (Seq(), Seq(), Seq(body), Seq(), (_, _, es, _) =>
        t.LetClass(t.LocalClassDef(transformer.transform(cd), methods.map(transformer.transform)), es(0)))

    case s.LocalClassConstructor(lct, args) =>
      (Seq(), Seq(), args, Seq(lct), (_, _, es, tps) =>
        t.LocalClassConstructor(tps(0).asInstanceOf[t.LocalClassType], es))

    case s.LocalMethodInvocation(receiver, method, tparams, tps, args) =>
      (Seq(), Seq(method), receiver +: args, tparams ++ tps, (_, vs, es, tps) => {
        val (ntparams, ntps) = tps.splitAt(tparams.size)
        t.LocalMethodInvocation(es(0), vs(0), ntparams.map(_.asInstanceOf[t.TypeParameter]), ntps, es.tail)
      })

    case s.LocalClassSelector(expr, id, tpe) =>
      (Seq(), Seq(), Seq(expr), Seq(tpe), (_, _, es, tps) =>
        t.LocalClassSelector(es(0), id, tps(0)))

    case _ => super.deconstruct(e)
  }
}
