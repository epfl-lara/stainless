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

class GhostAccessRewriter(afterPhase: String) extends PluginPhase { self =>
  override val phaseName = "ghost-removal"
  override val runsAfter = Set(afterPhase)
  override val runsBefore = Set(FirstTransform.name)

  override def run(using dottyCtx: DottyContext): Unit = (new GhostAccessMacroTransform).run

  // GhostAccessRewriter needs to extend PluginPhase (because we would like to return it in StainlessPlugin.init)
  // However, the MacroTransform class is better suited for our needs.
  // Because PluginPhase extends MiniPhase (which is a class) and that MacroTransform is a class, we can't extend
  // both. So we use composition instead of inheritance to achieve our goal.
  private class GhostAccessMacroTransform(using override val dottyCtx: DottyContext) extends MacroTransform with ASTExtractors {
    import StructuralExtractors._
    import AuxiliaryExtractors._

    private val ghostAnnotation = Symbols.requiredClass("stainless.annotation.ghost")
    private val ghostFun = Symbols.requiredMethod("stainless.lang.ghost")

    override val phaseName = self.phaseName
    override val runsAfter = self.runsAfter

    override protected def newTransformer(using DottyContext): Transformer = new GhostRewriteTransformer

    private class GhostRewriteTransformer(using DottyContext) extends Transformer {

      /**
        * Is this symbol @ghost, or enclosed inside a ghost definition?
        *
        * Note: We exclude constructors from being ghost because we can't remove them anyway
        */
      def effectivelyGhost(sym: Symbol)(using dottyCtx: DottyContext): Boolean =
        (!sym.denot.isConstructor &&
          sym.ownersIterator.exists(_.hasAnnotation(ghostAnnotation)))

      /** 
        * Returns the remaining formal parameter lists of a method/function left
        * to be applied.
        *
        * For instance, for a method `def m[A](x: Int)[B](y: String)`, this
        * returns `List(List(type A), List(value x), List(type B), List(value
        * y))` when called on `m`, or `List(List(type B), List(value y))` when
        * called on `m[A](3)`.
        *
        * Warning: this assumes all arguments for all parameter lists are given
        * at once; it does not handle partial applications.
        */
      def remainingFormalParams(tree: tpd.Tree): List[List[Symbol]] =
        val paramSymss = tpd.funPart(tree).symbol.paramSymss
        val argss = tpd.allArgss(tree)
        if paramSymss.length >= argss.length then
          paramSymss.drop(argss.length)
        else
          Nil

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

        case Apply(fun, args) if effectivelyGhost(fun.symbol) || fun.symbol == ghostFun =>
          mkZero(tree.tpe)

        case ExRequiredExpression(_, true) => tpd.Literal(Constant(()))
        case ExDecreasesExpression(_) => tpd.Literal(Constant(()))
        case ExAssertExpression(_, _, true) => tpd.Literal(Constant(()))
        case ExEnsuredExpression(body, _, true) =>
          transform(body) match {
            case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "Ensuring"), Seq(unwrapped)) => unwrapped
            case body => body
          }

        case ExWhile.WithInvariant(_, body) => transform(body)
        case ExWhile.WithWeakInvariant(_, body) => transform(body)
        case ExWhile.WithInline(body) => transform(body)
        case ExWhile.WithOpaque(body) => transform(body)

        case tree@Apply(fun, args) =>
          val fun1 = super.transform(fun)
          remainingFormalParams(fun1) match
            case params :: _ =>
              val args1 =
                for (param, arg) <- params.zip(args) yield
                  if param.hasAnnotation(ghostAnnotation) then
                    mkZero(param.info)
                  else
                    transform(arg)
              cpy.Apply(tree)(fun1, args1)
            case _ =>
              cpy.Apply(tree)(fun1, args.map(transform))

        case Assign(lhs, rhs) if effectivelyGhost(lhs.symbol) =>
          cpy.Assign(tree)(lhs, mkZero(rhs.tpe))

        case Block(stats, last) =>
          val recStats = transform(stats).filter {
            case tpd.Literal(_) => false
            case _ => true
          }
          val recLast = transform(last)
          // Transform `val v = e; v` into `e` to allow for tail recursion elimination
          (recStats.lastOption, recLast) match {
            case (Some(vd @ ValDef(_, _, _)), iden @ (Ident(_) | Typed(Ident(_), _))) if iden.symbol == vd.symbol =>
              cpy.Block(tree)(recStats.init, vd.rhs)
            case _ => cpy.Block(tree)(recStats, recLast)
          }

        case _ => super.transform(tree)
      }
    }
  }
}
