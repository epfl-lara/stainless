/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package anon

import inox.utils.{NoPosition, Position}
import scala.collection.mutable.{Map => MutableMap}

trait Trees extends methods.Trees { self =>

  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols
    extends super.AbstractSymbols { self0: Symbols =>
  }

  case object IsAnonymous extends Flag("anonymous", Seq())

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

  case class LetClass(lcd: LocalClassDef, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = {
      // FIXME: Next line should work
      // checkParamTypes(args.map(_.getType), lcd.typed.fields.map(_.tpe), lcd.typed.toType)
      checkParamTypes(args.map(_.getType), lcd.typed.fields.map(_.tpe), lcd.typed.parentType)
    }
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: Trees => new anon.TreeDeconstructor {
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
      p"""|${cd.parents.head}${nary(cd.typeArgs, ", ", "[", "]")}${nary(cd.fields, ", ", "(", ")")} {
          |  ${nary(methods, "\n\n")}
          |}"""

    case LetClass(lcd, args) => p"new $lcd${nary(args, ", ", "(", ")")}"

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

  override def deconstruct(e: s.Expr): DeconstructedExpr = e match {
    case s.LetClass(lcd, args) =>
      (Seq(), Seq(), args, Seq(), (_, _, es, _) => t.LetClass(lcd.asInstanceOf[t.LocalClassDef], es))
    case _ => super.deconstruct(e)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.IsAnonymous => (Seq(), Seq(), Seq(), (_, _, _) => t.IsAnonymous)
    case _ => super.deconstruct(f)
  }
}
