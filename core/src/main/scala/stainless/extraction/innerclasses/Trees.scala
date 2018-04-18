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

  case class LetClass(lcd: LocalClassDef, body: Expr, tpe: Type) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = tpe
  }

  case class LocalClassConstructor(lct: LocalClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): LocalClassType = lct
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

  case class LocalClassType(id: Identifier, tps: Seq[Type]) extends Type {
    val toClassType: ClassType = ClassType(id, tps)
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

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {
    case LocalClassDef(cd, methods) =>
      p"""|$cd {
          |  ${nary(methods, "\n\n")}
          |}"""

    case LetClass(lcd, body, _) =>
      p"""|{
          |  $lcd
          |  $body
          |}"""

    case LocalClassConstructor(ct, args) =>
      p"$ct(${nary(args, ", ")})"

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

trait TreeDeconstructor extends methods.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(tpe: s.Type): DeconstructedType = tpe match {
    case s.LocalClassType(id, tps) => (Seq(id), tps, Seq(), (ids, tps, _) =>
        t.LocalClassType(ids(0), tps))

    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(e: s.Expr): DeconstructedExpr = e match {
    case s.LetClass(lcd, body, tpe) =>
      (Seq(), Seq(), Seq(body), Seq(tpe), (_, _, es, tps) =>
        t.LetClass(lcd.asInstanceOf[t.LocalClassDef], es(0), tps(0)))

    case s.LocalClassConstructor(lct, args) =>
      (Seq(), Seq(), args, Seq(lct), (_, _, es, tps) =>
        t.LocalClassConstructor(tps(0).asInstanceOf[t.LocalClassType], es))

    case s.LocalMethodInvocation(receiver, method, tparams, tps, args) =>
      (Seq(), Seq(method), receiver +: args, tparams ++ tps, (_, vs, es, tps) => {
        val (ntparams, ntps) = tps.splitAt(tparams.size)
        t.LocalMethodInvocation(es(0), vs(0), ntparams.map(_.asInstanceOf[t.TypeParameter]), ntps, es.tail)
      })

    case _ => super.deconstruct(e)
  }
}
