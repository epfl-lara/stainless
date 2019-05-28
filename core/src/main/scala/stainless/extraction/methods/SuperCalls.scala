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
  extends oo.CachingPhase
    with SimpleSorts
    with oo.IdentityTypeDefs
    with oo.SimpleClasses { self =>

  val s: Trees
  val t: Trees

  private[this] val superCache = new utils.ConcurrentCache[SymbolIdentifier, SymbolIdentifier]
  private[this] def superID(id: SymbolIdentifier)(implicit symbols: s.Symbols): SymbolIdentifier =
    superCache.cached(id) {
      val cid = symbols.getFunction(id).flags.collectFirst { case s.IsMethodOf(cid) => cid }.get
      val last = s"${cid.name}$$${id.symbol.path.last}"
      val newSymbol = Symbol((id.symbol.path.init :+ last) mkString ".")
      SymbolIdentifier(newSymbol)
    }

  private class SuperCollector(implicit symbols: s.Symbols) extends s.SelfTreeTraverser {
    private[this] var supers: Set[Identifier] = Set.empty
    def getSupers: Set[Identifier] = supers

    override def traverse(e: s.Expr): Unit = e match {
      case s.MethodInvocation(s.Super(ct), id, _, _) =>
        supers += id
        super.traverse(e)
      case _ => super.traverse(e)
    }
  }

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({ (fd, context) =>
    FunctionKey(fd) + ValueKey(context.mustDuplicate(fd))
  })

  override protected final val sortCache = new ExtractionCache[s.ADTSort, SortResult]({ (sort, context) =>
    val symbols = context.symbols
    val collector = new SuperCollector()(symbols)
    collector.traverse(sort)
    SortKey(sort) + SetKey(collector.getSupers)(symbols)
  })

  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult]({ (cd, context) =>
    val symbols = context.symbols
    val collector = new SuperCollector()(symbols)
    collector.traverse(cd)
    ClassKey(cd) + SetKey(collector.getSupers)(symbols)
  })

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    import s._
    import symbols._

    val supers: Set[Identifier] = {
      val collector = new SuperCollector

      symbols.functions.values.foreach(collector.traverse)
      symbols.sorts.values.foreach(collector.traverse)
      symbols.classes.values.foreach(collector.traverse)
      collector.getSupers
    }

    def mustDuplicate(fd: FunDef): Boolean = supers.contains(fd.id)

    override def transform(e: s.Expr): t.Expr = e match {
      case s.MethodInvocation(sup @ s.Super(ct), id, tps, args) =>
        t.MethodInvocation(
          t.This(transform(ct).asInstanceOf[t.ClassType]).copiedFrom(sup),
          superID(id.unsafeToSymbolIdentifier),
          tps map transform,
          args map transform
        ).copiedFrom(e)

      case _ => super.transform(e)
    }
  }

  override protected type FunctionResult = (t.FunDef, Option[t.FunDef])

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols = {
    symbols.withFunctions(functions.flatMap { case (fd, ofd) => fd +: ofd.toSeq })
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult = {
    import context.symbols
    import s._

    if (context.mustDuplicate(fd)) {
      val sid = superID(fd.id.unsafeToSymbolIdentifier)
      val superFd = exprOps.freshenSignature(
        new s.FunDef(sid, fd.tparams, fd.params, fd.returnType, fd.fullBody, (fd.flags :+ Final).distinct).setPos(fd)
      )

      val cd = symbols.getClass(fd.flags.collectFirst { case s.IsMethodOf(cid) => cid }.get)
      val newFd = fd.copy(fullBody = s.exprOps.withBody(
        fd.fullBody,
        s.MethodInvocation(
          s.This(s.ClassType(cd.id, cd.typeArgs).setPos(fd)).setPos(fd),
          sid, fd.tparams.map(_.tp), fd.params.map(_.toVariable)
        ).copiedFrom(fd)
      )).copiedFrom(fd)

      (context.transform(newFd), Some(context.transform(superFd)))
    } else {
      (context.transform(fd), None)
    }
  }

  override protected def extractSort(context: TransformerContext, sort: s.ADTSort) = context.transform(sort)
  override protected def extractClass(context: TransformerContext, cd: s.ClassDef) = context.transform(cd)
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
