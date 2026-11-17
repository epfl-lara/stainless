/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

import stainless.ast.{Symbol, SymbolIdentifier}
import scala.collection.mutable.{Map => MutableMap}

/** Resolves mixin composition: the methods that classes inherit from several traits, and super calls within traits.
 *
 *  Scala orders the ancestors of a class `C extends P1 with ... with Pn` by its linearization, `C` followed
 *  by the linearizations of `Pn`, ..., `P1`, where only the last occurrence of each class is kept. The
 *  frontend extracts the parents of classes in the order they are written, traits with the [[IsTrait]]
 *  flag, and super calls as written: `super.m(args)` within a method of `X` is `X.super.m(args)`, where
 *  `X.super` has the type of the parent of `X` declaring the method `m` that the call refers to.
 *
 *  Method dispatch in later phases only follows the subclass relation, and super calls are static. This
 *  phase makes the choices of the linearization explicit:
 *
 *  - When a class inherits implementations of a method from traits that don't override each other, it
 *    selects the first one in its linearization with an override that calls it (a forwarder).
 *  - A super call within a trait `X` calls the implementation that comes after `X` in the linearization
 *    of the class of `this`. It becomes a call to an abstract method of `X` (a super accessor), which each
 *    class mixing in `X` implements with a call to that implementation.
 *  - A method of a trait with super calls (a stacked method) has a different meaning in each class mixing
 *    in the trait. Forwarders and super accessors call a copy of it in the class mixing in the trait, where
 *    its super calls are resolved statically. Unlike the calls through super accessors, the calls between
 *    these copies follow the linearization, so that termination is easy to establish.
 *
 *  For example,
 *
 * {{{
 * trait Trees { def name: String = "trees" }
 * trait Printing extends Trees { override def name: String = "printing " + super.name }
 * trait Ext extends Trees { override def name: String = "ext" }
 * case object ext extends Ext with Printing
 * }}}
 *
 *  becomes
 *
 * {{{
 * trait Trees { def name: String = "trees" }
 * trait Printing extends Trees {
 *   override def name: String = "printing " + this.Printing$super$name
 *   def Printing$super$name: String
 * }
 * trait Ext extends Trees { override def name: String = "ext" }
 * case object ext extends Ext with Printing {
 *   override def name: String = this.Printing$name
 *   override def Printing$super$name: String = ext.super.name // `name` of `Ext`
 *   final def Printing$name: String = "printing " + ext.super.name // `name` of `Ext`
 * }
 * }}}
 */
class Mixins(override val s: Trees)(override val t: s.type)
            (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  // Identifiers are stable across runs
  private val accessorSymbols = MutableMap[(Identifier, Symbol), Symbol]()
  private val accessorIds = MutableMap[(Identifier, Symbol), SymbolIdentifier]()
  private val forwarderIds = MutableMap[(Identifier, Symbol), SymbolIdentifier]()
  private val copyIds = MutableMap[(Identifier, Identifier), SymbolIdentifier]()

  private def fullName(id: Identifier): String = id match {
    case sid: SymbolIdentifier => sid.symbol.name
    case _ => id.name
  }

  private def symbolOf(id: Identifier): Symbol = id match {
    case sid: SymbolIdentifier => sid.symbol
    case _ => context.reporter.internalError(s"Unexpected method identifier ${id.asString}")
  }

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    def isTrait(id: Identifier): Boolean = symbols.lookupClass(id).exists(_.flags contains IsTrait)
    def parents(id: Identifier): Seq[Identifier] = symbols.lookupClass(id).toSeq.flatMap(_.parents.map(_.id))

    def ownerOf(fd: FunDef): Option[Identifier] = fd.flags.collectFirst { case IsMethodOf(id) => id }

    def isSuperCall(e: Expr): Boolean = e match {
      case MethodInvocation(Super(_), _, _, _) => true
      case _ => false
    }

    val methods: Map[Identifier, Seq[FunDef]] =
      symbols.functions.values.toSeq.filterNot(_.flags contains IsInvariant)
        .flatMap(fd => ownerOf(fd).map(_ -> fd)).groupMap(_._1)(_._2)

    /** Methods of traits with super calls, whose super calls are dynamic. */
    val stacked: Set[Identifier] = symbols.functions.values.collect {
      case fd if ownerOf(fd).exists(isTrait) && exprOps.exists(isSuperCall)(fd.fullBody) => fd.id
    }.toSet

    val hasMixins = symbols.classes.values.exists(cd => cd.parents.size >= 2)
    if (!hasMixins && stacked.isEmpty) return (symbols, ExtractionSummary.NoSummary)

    val linCache = MutableMap[Identifier, Seq[Identifier]]()

    /** The linearization of the class `id`. */
    def lin(id: Identifier): Seq[Identifier] = linCache.get(id) match {
      case Some(res) => res
      case None =>
        val res = id +: parents(id).foldLeft(Seq.empty[Identifier]) { (acc, p) =>
          val l = lin(p)
          l.filterNot(acc.contains) ++ acc
        }
        linCache(id) = res
        res
    }

    def derivesFrom(id: Identifier, ancestor: Identifier): Boolean = lin(id) contains ancestor

    /** The method `sym` declared in the class `cid`, if any. */
    def declared(cid: Identifier, sym: Symbol): Option[FunDef] =
      methods.getOrElse(cid, Seq.empty).find(fd => symbolOf(fd.id) == sym)

    def isConcrete(fd: FunDef): Boolean = !(fd.flags contains IsAbstract)

    /** The implementation of the method `sym` that comes first in the classes `cids`. */
    def firstImpl(cids: Seq[Identifier], sym: Symbol): Option[FunDef] =
      cids.iterator.flatMap(cid => declared(cid, sym).filter(isConcrete)).nextOption()

    /** Whether the class `id` inherits the trait `trt` from one of its parents that is not a trait,
      * in which case the parent already resolves the mixin composition of `trt`. */
    def inheritsFromClass(id: Identifier, trt: Identifier): Boolean =
      parents(id).exists(p => !isTrait(p) && derivesFrom(p, trt))

    def classType(id: Identifier): ClassType = ClassType(id, symbols.getClass(id).typeArgs)

    /** The type of the ancestor `anc` of the class `id`, from within `id`. */
    def ancestorType(id: Identifier, anc: Identifier): ClassType =
      if (id == anc) classType(id)
      else symbols.getClass(id).typed.ancestors.find(_.id == anc).get.toType

    val copies = MutableMap[(Identifier, Identifier), FunDef]()

    /** Moves trees from within the class `from` into its descendant `into`. */
    class IntoClass(into: Identifier, from: Identifier) extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      private val tpSubst: Map[TypeParameter, Type] =
        if (into == from) Map.empty
        else symbols.getClass(into).typed.ancestors.find(_.id == from).get.tpSubst
      private val ancestors = lin(into).toSet

      override def transform(tpe: Type): Type = tpe match {
        case tp: TypeParameter if tpSubst contains tp => tpSubst(tp)
        case _ => super.transform(tpe)
      }

      override def transform(e: Expr): Expr = e match {
        case This(ct) if ancestors(ct.id) => This(classType(into)).copiedFrom(e)
        // Super calls are resolved statically within the class `into`
        case MethodInvocation(Super(_), id, tps, args) if isTrait(from) =>
          val sym = symbolOf(id)
          val impl = firstImpl(lin(into).dropWhile(_ != from).tail, sym).getOrElse {
            context.reporter.fatalError(e.getPos,
              s"No implementation of ${id.asString} follows ${from.asString} in the linearization of ${into.asString}")
          }
          call(into, impl, tps.map(transform), args.map(transform)).copiedFrom(e)
        case _ => super.transform(e)
      }
    }

    /** The method `fd` of an ancestor of the class `cid`, copied into `cid`, where its super calls are static. */
    def copyOf(cid: Identifier, fd: FunDef): FunDef = copies.get((cid, fd.id)) match {
      case Some(res) => res
      case None =>
        val owner = ownerOf(fd).get
        val id = copyIds.getOrElseUpdate((cid, fd.id), SymbolIdentifier(fullName(cid) + "." + owner.name + "$" + fd.id.name))
        val flags = fd.flags.filter {
          case IsMethodOf(_) | IsAbstract | IsAccessor(_) | IsInvariant | Final => false
          case _ => true
        } ++ Seq(IsMethodOf(cid), Final)
        val copy = new FunDef(id, fd.tparams, fd.params, fd.returnType, fd.fullBody, flags).copiedFrom(fd)
        // Copies don't call each other recursively, as they follow the linearization
        val res = exprOps.freshenSignature(new IntoClass(cid, owner).transform(copy))
        copies((cid, fd.id)) = res
        res
    }

    /** A call to the implementation `fd` from within the class `cid`. */
    def call(cid: Identifier, fd: FunDef, tps: Seq[Type], args: Seq[Expr]): Expr =
      if (stacked(fd.id)) MethodInvocation(This(classType(cid)), copyOf(cid, fd).id, tps, args)
      else MethodInvocation(Super(ancestorType(cid, ownerOf(fd).get)), fd.id, tps, args)

    /** A method of the class `cid` with the signature and specification of `fd`, a method of
      * an ancestor of `cid`, that calls the implementation `impl` (or is abstract). */
    def methodLike(cid: Identifier, id: Identifier, fd: FunDef, impl: Option[FunDef], flags: Seq[Flag]): FunDef = {
      val keptFlags = fd.flags.filter(f => f == Ghost || f.name == "pure")
      val sig = new FunDef(id, fd.tparams, fd.params, fd.returnType,
        exprOps.withBody(fd.fullBody, NoTree(fd.returnType).copiedFrom(fd)),
        keptFlags ++ flags :+ IsMethodOf(cid)).copiedFrom(fd)
      val res = exprOps.freshenSignature(new IntoClass(cid, ownerOf(fd).get).transform(sig))
      impl match {
        case Some(impl) =>
          val body = call(cid, impl, res.tparams.map(_.tp), res.params.map(_.toVariable)).copiedFrom(fd)
          res.copy(fullBody = exprOps.withBody(res.fullBody, body)).copiedFrom(res)
        case None => res
      }
    }

    // The super accessors of traits, for their dynamic super calls
    val superCalls: Map[Identifier, Seq[FunDef]] = stacked.toSeq.map(symbols.getFunction(_)).flatMap { fd =>
      exprOps.collect[FunDef] {
        case MethodInvocation(Super(_), id, _, _) => Set(symbols.getFunction(id))
        case _ => Set.empty
      } (fd.fullBody).map(ownerOf(fd).get -> _)
    }.groupMap(_._1)(_._2).view.mapValues(_.distinctBy(fd => symbolOf(fd.id))).toMap

    def accessorId(trt: Identifier, sym: Symbol): SymbolIdentifier = accessorIds.getOrElseUpdate((trt, sym), {
      SymbolIdentifier(accessorSymbols.getOrElseUpdate((trt, sym), Symbol(fullName(trt) + "$super$" + sym.path.last)))
    })

    val accessors: Seq[FunDef] = superCalls.toSeq.flatMap { case (trt, targets) => targets.map { target =>
      methodLike(trt, accessorId(trt, symbolOf(target.id)), target, None, Seq(IsAbstract))
    }}

    val classes = symbols.classes.values.toSeq.filterNot(cd => isTrait(cd.id))

    val accessorImpls: Seq[FunDef] = for {
      cd <- classes
      (trt, targets) <- superCalls.toSeq if derivesFrom(cd.id, trt) && !inheritsFromClass(cd.id, trt)
      target <- targets
    } yield {
      val impl = firstImpl(lin(cd.id).dropWhile(_ != trt).tail, symbolOf(target.id)).getOrElse {
        context.reporter.fatalError(cd.getPos,
          s"No implementation of ${target.id.asString} follows ${trt.asString} in the linearization of ${cd.id.asString}")
      }
      val accId = accessorId(trt, symbolOf(target.id))
      methodLike(cd.id, SymbolIdentifier(accId.symbol), target, Some(impl), Seq.empty)
    }

    // The forwarders to the implementations that classes inherit through mixin composition
    val forwarders: Seq[FunDef] = for {
      cd <- classes
      sym <- lin(cd.id).tail.flatMap(c => methods.getOrElse(c, Seq.empty).map(fd => symbolOf(fd.id))).distinct
      if declared(cd.id, sym).isEmpty
      winner <- firstImpl(lin(cd.id), sym)
      owner = ownerOf(winner).get
      if !inheritsFromClass(cd.id, owner)
      if stacked(winner.id) || lin(cd.id).exists { c =>
        c != owner && !derivesFrom(owner, c) && declared(c, sym).exists(isConcrete)
      }
    } yield {
      val id = forwarderIds.getOrElseUpdate((cd.id, sym), SymbolIdentifier(sym))
      methodLike(cd.id, id, winner, Some(winner), Seq.empty)
    }

    /** Replaces the dynamic super calls within traits with calls to their super accessors,
      * and calls to stacked methods with calls to their copies in the class. */
    class Transformer(cls: Option[Identifier]) extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      override def transform(e: Expr): Expr = e match {
        case MethodInvocation(Super(_), id, tps, args) if cls.exists(isTrait) =>
          val trt = cls.get
          MethodInvocation(This(classType(trt)).copiedFrom(e), accessorId(trt, symbolOf(id)),
            tps.map(transform), args.map(transform)).copiedFrom(e)
        case MethodInvocation(Super(_), id, tps, args) if stacked(id) =>
          call(cls.get, symbols.getFunction(id), tps.map(transform), args.map(transform)).copiedFrom(e)
        case _ => super.transform(e)
      }
    }

    val functions = symbols.functions.values.toSeq.map(fd => new Transformer(ownerOf(fd)).transform(fd))
    // The copies are created on demand by the forwarders, super accessors and transformed methods
    val newFunctions = functions ++ accessors ++ accessorImpls ++ forwarders ++ copies.values

    val newSymbols = NoSymbols
      .withFunctions(newFunctions)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(symbols.classes.values.toSeq)
      .withTypeDefs(symbols.typeDefs.values.toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object Mixins {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends Mixins(s)(t)
    new Impl(trees, trees)
  }
}
