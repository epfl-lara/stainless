package stainless
package frontends.dotc

import dotty.tools.dotc
import dotc._
import core._
import Types._
import Symbols._
import Constants._
import ast._
import Trees._
import Contexts.{Context => DottyContext}
import plugins._
import transform._

class GhostAccessRewriter extends PluginPhase { self =>
  override val phaseName = "ghost-removal"
  override val runsAfter = Set("stainless")
  override val runsBefore = Set(FirstTransform.name)

  override def run(using dottyCtx: DottyContext): Unit = (new GhostAccessMacroTransform).run

  // GhostAccessRewriter needs to extend PluginPhase (because we would like to return it in StainlessPlugin.init)
  // However, the MacroTransform class is better suited for our needs.
  // Because PluginPhase extends MiniPhase (which is a class) and that MacroTransform is a class, we can't extend
  // both. So we use composition instead of inheritance to achieve our goal.

  private class GhostAccessMacroTransform extends MacroTransform {
    override val phaseName = self.phaseName
    override val runsAfter = self.runsAfter

    override protected def newTransformer(using DottyContext): Transformer = new GhostRewriteTransformer

    private class GhostRewriteTransformer(using DottyContext) extends Transformer {
      val ghostAnnotation = Symbols.requiredClass("stainless.annotation.ghost")

      /**
        * Is this symbol @ghost, or enclosed inside a ghost definition?
        *
        * Note: We exclude constructors from being ghost because we can't remove them anyway
        */
      def effectivelyGhost(sym: Symbol)(using dottyCtx: DottyContext): Boolean =
        (!sym.denot.isConstructor &&
          sym.ownersIterator.exists(_.hasAnnotation(ghostAnnotation)))

      def symbolIndex(tree: tpd.Tree): Int = tree match {
        case Apply(fun, args) => symbolIndex(fun) + 1
        case _ => 0
      }

      // Inspired by Scalac mkZero method, though we do not special-case the NothingType and have it set to null instead.
      def mkZero(tp: Type)(using DottyContext): tpd.Tree = {
        val tpSym = tp.typeSymbol
        // Note: we can't pattern match on defn.UnitClass etc. because they are not stable identifiers.
        tpd.Literal(
          if (tpSym == defn.UnitClass) Constant(())
          else if (tpSym == defn.BooleanClass) Constant(false)
          else if (tpSym == defn.FloatClass) Constant(0.0f)
          else if (tpSym == defn.DoubleClass) Constant(0.0d)
          else if (tpSym == defn.ByteClass) Constant(0.toByte)
          else if (tpSym == defn.ShortClass) Constant(0.toShort)
          else if (tpSym == defn.IntClass) Constant(0)
          else if (tpSym == defn.LongClass) Constant(0L)
          else if (tpSym == defn.CharClass) Constant(0.toChar)
          else Constant(null))
      }

      override def transform(tree: tpd.Tree)(using dottyCtx: DottyContext): tpd.Tree = tree match {
        case Ident(_) if effectivelyGhost(tree.symbol) =>
          mkZero(tree.tpe)

        case Select(_, _) if effectivelyGhost(tree.symbol) =>
          mkZero(tree.tpe)

        case dd@DefDef(name, paramss, tpt, _) if effectivelyGhost(tree.symbol) =>
          cpy.DefDef(tree)(name, paramss, tpt, mkZero(dd.rhs.tpe))

        case vd@ValDef(name, tpt, _) if effectivelyGhost(tree.symbol) =>
          cpy.ValDef(tree)(name, tpt, mkZero(vd.rhs.tpe))

        case Apply(fun, args) if effectivelyGhost(fun.symbol) =>
          mkZero(tree.tpe)

        case f@Apply(fun, args) =>
          val fun1 = super.transform(fun)

          val params = f.symbol.denot.paramSymss
          val leadingTypeParams = params.exists(_.exists(_.isType))
          val allTermParams = if (leadingTypeParams) params.tail else params

          val termParams = allTermParams(symbolIndex(fun))

          val args1 = for ((param, arg) <- termParams.zip(args)) yield
            if (param.hasAnnotation(ghostAnnotation))
              mkZero(param.info)
            else
              transform(arg)

          cpy.Apply(tree)(fun1, args1)

        case Assign(lhs, rhs) if effectivelyGhost(lhs.symbol) =>
          cpy.Assign(tree)(lhs, mkZero(rhs.tpe))

        case _ => super.transform(tree)
      }
    }
  }
}