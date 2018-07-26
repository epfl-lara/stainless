/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.Position

import stainless.ast.{Symbol, SymbolIdentifier}
import stainless.ast.SymbolIdentifier.IdentifierOps

/** This phase transforms super calls into concrete method calls.
 *
 *  It does so by duplicating every method that is being referenced in
 *  a super call, and rewriting the original method to call the duplicate.
 *
 *  This way it becomes possible to call a specific method in the class hierarchy,
 *  as one would otherwise always end up calling the dispatching method that will
 *  be introduced during method lifting.
 *
 *  For example, the following code:
 *
 * {{{
 * abstract class A {
 *   def bar: BigInt = 41
 * }
 *
 * abstract class B extends A
 *
 * abstract class C extends B {
 *   override def bar: BigInt = super.bar + 1
 * }
 *
 * case class D() extends C {
 *   override def bar: BigInt = super.bar * 10
 * }
 * }}}
 *
 * is tranformed into:
 *
 * {{{
 * abstract class A {
 *   def bar: BigInt = A$bar
 *
 *   def A$bar: BigInt = 41
 * }
 *
 * abstract class B extends A
 *
 * abstract class C extends B {
 *   override def bar: BigInt = C$bar
 *
 *   def C$bar: BigInt = A$bar + 1
 * }
 *
 * case class D() extends C {
 *   override def bar: BigInt = C$bar * 10
 * }
 * }}}
 */
trait SuperCalls
  extends CachingPhase
  with DependentlyCachedFunctions
  with IdentitySorts
  with oo.IdentityClasses { self =>

  val s: methods.Trees
  val t: methods.Trees

  override protected type FunctionResult = Seq[t.FunDef]

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols = {
    symbols.withFunctions(functions.flatten)
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    import s._
    import symbols._

    private def findFirstSuperDef(symbol: Symbol, ct: s.ClassType): Option[(s.FunDef, s.ClassDef)] = {
      val cd = classes(ct.id)
      cd.methods(symbols)
        .find(_.symbol == symbol)
        .map(functions)
        .map(fd => (fd, cd))
        .orElse {
          cd.parents.headOption flatMap { ct =>
            findFirstSuperDef(symbol, ct)
          }
        }
    }

    private def prefixedSymbol(prefix: String, symbol: Symbol): Symbol = {
      val last = s"${prefix}$$${symbol.path.last}"
      Symbol((symbol.path.init :+ last) mkString ".")
    }

    val superId: Map[Identifier, Identifier] = {
      functions.values flatMap { fd =>
        val superRefs = s.exprOps.collect[(Identifier, Identifier)] {
          case s.Super(ct) =>
            val symbol = fd.id.unsafeToSymbolIdentifier.symbol
            val Some((superFun, superClass)) = findFirstSuperDef(symbol, ct)
            val superFunId = superFun.id.unsafeToSymbolIdentifier

            val superSymbol = prefixedSymbol(superClass.id.asString, superFunId.symbol)
            Set(superFunId -> SymbolIdentifier(superSymbol))

          case _ => Set()

        } (fd.fullBody)

        superRefs.toSeq
      }
    }.toMap

    override def transform(e: s.Expr): t.Expr = e match {
      case s.MethodInvocation(s.Super(ct), id, tps, args) => super.transform {
        s.MethodInvocation(s.This(ct), superId(id), tps, args)
      }

      case _ => super.transform(e)
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): Seq[t.FunDef] = {
    import s._
    import context.symbols

    context.superId.get(fd.id) match {
      case None => Seq(context.transform(fd))
      case Some(dupId) =>
        val cid = fd.flags collectFirst { case IsMethodOf(cid) => cid }

        assert(cid.isDefined)
        assert(symbols.classes.contains(cid.get))

        val cd = symbols.classes(cid.get)

        val freshParams = fd.params map (_.freshen)
        val freshMap = (fd.params zip freshParams.map(_.toVariable)).toMap
        val superFun = fd.copy(
          id = dupId,
          params = freshParams,
          fullBody = s.exprOps.replaceFromSymbols(freshMap, fd.fullBody)
        )

        val rewrittenFun = fd.copy(
          fullBody = s.MethodInvocation(
            s.This(cd.typed(symbols).toType),
            dupId,
            fd.tparams.map(_.tp),
            fd.params.map(_.toVariable)
          )
        )

        Seq(rewrittenFun, superFun).map(context.transform(_))
    }
  }

}

object SuperCalls {
  def apply(ts: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: ts.type
  } = new SuperCalls {
    override val s: ts.type = ts
    override val t: ts.type = ts
    override val context = ctx
  }
}
