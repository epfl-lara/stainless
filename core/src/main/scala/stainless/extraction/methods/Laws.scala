/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

import stainless.ast.{Symbol, SymbolIdentifier}
import SymbolIdentifier.unsafeToSymbolIdentifier

class Laws(override val s: Trees, override val t: Trees)
          (using override val context: inox.Context)
  extends oo.CachingPhase
     with oo.IdentityTypeDefs
     with IdentitySorts { self =>
  
  private[this] val lawID = new utils.ConcurrentCached[SymbolIdentifier, SymbolIdentifier](
    id => SymbolIdentifier(id.symbol.name)
  )

  override protected final def getContext(symbols: s.Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected final class TransformerContext(override val s: self.s.type, override val t: self.t.type)
                                          (using val symbols: s.Symbols)
    extends oo.DefinitionTransformer {

    override type Env = Option[Symbol]
    override def initEnv: Env = None

    def missingLaws(cd: s.ClassDef): Seq[(s.TypedClassDef, s.FunDef)] = {
      val lawSymbols = (cd +: cd.ancestors.map(_.cd)).reverse.foldLeft(Set.empty[Symbol]) {
        case (lawSymbols, cd) =>
          val methods = cd.methods
          val methodSymbols = methods.map(_.symbol).toSet
          val newSymbols = methods
            .filter(id => symbols.getFunction(id).flags contains s.Law)
            .map(_.symbol).toSet

          lawSymbols -- methodSymbols ++ newSymbols
      }

      lawSymbols.toSeq.sortBy(_.name).map { symbol =>
        val acd = cd.ancestors.find(_.cd.methods.exists(_.symbol == symbol)).get
        val lawFd = symbols.getFunction(acd.cd.methods.find(_.symbol == symbol).get)
        (acd, lawFd)
      }
    }

    override def transform(e: s.Expr, env: Env): t.Expr = e match {
      case s.MethodInvocation(sup @ s.Super(ct), id, tps, args) if symbols.getFunction(id).flags contains s.Law =>
        if (Some(id.unsafeToSymbolIdentifier.symbol) == env) {
          t.MethodInvocation(
            t.This(transform(ct, env).asInstanceOf[t.ClassType]).copiedFrom(sup),
            lawID(id.unsafeToSymbolIdentifier),
            tps map (transform(_, env)),
            args map (transform(_, env))
          ).copiedFrom(e)
        } else {
          throw MalformedStainlessCode(e, "Cannot refer to super-type law outside of proof body")
        }

      case _ => super.transform(e, env)
    }

    override def transform(fd: s.FunDef): t.FunDef = {
      val env = Some(fd.id.unsafeToSymbolIdentifier.symbol)
      new t.FunDef(
        transform(fd.id, env),
        fd.tparams map (transform(_, env)),
        fd.params map (transform(_, env)),
        transform(fd.returnType, env),
        transform(fd.fullBody, env),
        fd.flags map (transform(_, env))
      ).copiedFrom(fd)
    }
  }

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({ (fd, context) =>
    FunctionKey(fd) + new ValueKey(
      if ((fd.flags exists { case s.IsMethodOf(_) => true case _ => false }) && (fd.flags contains s.Law)) {
        context.symbols.firstSuperMethod(fd.id.unsafeToSymbolIdentifier).toSet[Identifier]
      } else {
        Set.empty[Identifier]
      }
    )
  })

  override protected final type FunctionResult = (t.FunDef, Option[t.FunDef])
  override protected final def registerFunctions(symbols: t.Symbols, functions: Seq[FunctionResult]): t.Symbols = {
    symbols.withFunctions(functions.flatMap(p => p._1 +: p._2.toSeq))
  }

  override protected final def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult = {
    import context.{s => _, t => _, given, _}

    if (fd.flags contains s.Law) {
      // Some sanity checks
      if (!fd.flags.exists { case s.IsMethodOf(_) => true case _ => false })
        throw MalformedStainlessCode(fd, "Unexpected non-method law")

      val cid = fd.flags.collectFirst { case s.IsMethodOf(id) => id }.get
      val cd = symbols.getClass(cid)

      if (!(cd.flags contains s.IsAbstract))
        throw MalformedStainlessCode(fd, "Unexpected law in non-abstract class")
      if (!symbols.isSubtypeOf(fd.returnType, s.BooleanType()))
        throw MalformedStainlessCode(fd, "Unexpected non-boolean typed law")
      if (!fd.hasBody)
        throw MalformedStainlessCode(fd, "Unexpected law without a body")
      if (symbols.isRecursive(fd.id))
        throw MalformedStainlessCode(fd, "Unexpected recursive law")
      if (symbols.firstSuperMethod(fd.id.unsafeToSymbolIdentifier).exists { sid =>
        val sfd = symbols.getFunction(sid)
        !sfd.isAbstract && !sfd.isLaw
      }) throw MalformedStainlessCode(fd, "Unexpected law overriding concrete function")

      val env = Some(fd.id.unsafeToSymbolIdentifier.symbol)
      val ct = t.ClassType(cid, cd.typeArgs.map(transform(_, env))).setPos(fd)
      val lid = lawID(fd.id.unsafeToSymbolIdentifier)

      val newFd: t.FunDef = {
        val vd = t.ValDef(FreshIdentifier("res"), t.BooleanType().setPos(fd.fullBody)).setPos(fd.fullBody)
        val newBody = t.Ensuring(t.NoTree(t.BooleanType().setPos(fd.fullBody)).setPos(fd.fullBody),
          t.Lambda(Seq(vd), t.And(
            vd.toVariable,
            t.MethodInvocation(
              t.This(ct).setPos(fd.fullBody), lid,
              fd.typeArgs map (transform(_, env)),
              fd.params map (vd => transform(vd.toVariable, env))
            ).setPos(fd.fullBody)
          ).setPos(fd.fullBody)).setPos(fd.fullBody)
        ).setPos(fd.fullBody)

        new t.FunDef(
          fd.id,
          fd.tparams map (transform(_, env)),
          fd.params map (transform(_, env)),
          transform(fd.returnType, env),
          newBody,
          ((fd.flags filter (_ != s.Law) map (transform(_, env))) :+ t.IsAbstract).distinct
        ).copiedFrom(fd)
      }

      val propFd: t.FunDef = {
        val s.exprOps.BodyWithSpecs(specs, body) = s.exprOps.BodyWithSpecs(fd.fullBody)
        val newSpecs = specs.map(_.transform(context)(env))
        val returnType = transform(fd.returnType, env)
        val newBody = t.exprOps.reconstructSpecs(newSpecs, Some(t.andJoin(
          symbols.firstSuperMethod(fd.id.unsafeToSymbolIdentifier).map { sid =>
            t.MethodInvocation(
              t.This(ct).setPos(fd), lawID(sid),
              fd.typeArgs map (transform(_, env)),
              fd.params map (vd => transform(vd.toVariable, env))
            ).setPos(fd)
          }.toSeq :+ transform(body, env)
        ).setPos(body)), returnType)

        val newFlags = (
          (fd.flags filter (_ != s.Law) map (transform(_, env))) ++
          Seq(t.InlineOnce, t.Derived(Some(fd.id)), t.Final)
        ).distinct

        t.exprOps.freshenSignature(
          new t.FunDef(
            lid,
            fd.tparams map (transform(_, env)),
            fd.params map (transform(_, env)),
            returnType, newBody, newFlags).setPos(fd)
        )
      }

      (newFd, Some(propFd))
    } else {
      symbols.firstSuperMethod(fd.id.unsafeToSymbolIdentifier)
        .map(id => symbols.getFunction(id))
        .filter(_.flags contains s.Law)
        .map { sfd =>
          // inductive law proofs need the postcondition to be annotated to
          // the proof function, so we inject it there.
          val env = Some(fd.id.unsafeToSymbolIdentifier.symbol)
          val cd = fd.flags.collectFirst { case s.IsMethodOf(id) => symbols.getClass(id) }.get

          val tparams = fd.tparams map (transform(_, env))
          val params = fd.params map (transform(_, env))

          val specced = s.exprOps.BodyWithSpecs(fd.fullBody).addPost
          val newSpecs = specced.specs.map {
            case s.exprOps.Postcondition(l @ s.Lambda(Seq(vd), pred)) =>
              val nvd = transform(vd, env)
              t.exprOps.Postcondition(t.Lambda(Seq(nvd),
                t.and(transform(pred, env), nvd.toVariable, t.MethodInvocation(
                  t.This(t.ClassType(cd.id, cd.typeArgs map (transform(_, env))).copiedFrom(fd)).copiedFrom(fd),
                  lawID(sfd.id.unsafeToSymbolIdentifier),
                  tparams map (_.tp),
                  params map (_.toVariable)
                ).copiedFrom(fd)).copiedFrom(fd)
              ).copiedFrom(fd))

            case spec => spec.transform(context)(env)
          }

          val returnType = transform(fd.returnType, env)
          val newBody = t.exprOps.reconstructSpecs(newSpecs, specced.bodyOpt.map(transform(_, env)), returnType)
          val newFlags = (fd.flags map (transform(_, env))) :+ t.Law
          (new t.FunDef(fd.id, tparams, params, returnType, newBody, newFlags).copiedFrom(fd), None)
        }.getOrElse {
          (context.transform(fd), None)
        }
    }
  }

  override protected final val classCache = new ExtractionCache[s.ClassDef, ClassResult]({ (cd, context) =>
    ClassKey(cd) + SetKey(
      if (cd.flags contains s.IsAbstract) Set.empty[CacheKey]
      else context.missingLaws(cd).map { case (acd, fd) =>
        ClassKey(acd.cd) + FunctionKey(fd) + ValueKey(acd.tpSubst)
      }.toSet[CacheKey]
    )
  })

  override protected final type ClassResult = (t.ClassDef, Seq[t.FunDef])
  override protected final def registerClasses(symbols: t.Symbols, classes: Seq[ClassResult]): t.Symbols = {
    val (cls, funs) = classes.unzip
    symbols.withClasses(cls).withFunctions(funs.flatten)
  }

  override protected final def extractClass(context: TransformerContext, cd: s.ClassDef): ClassResult = {
    import context.{s => _, t => _, _}

    if (!(cd.flags contains s.IsAbstract)) {
      val functions = context.missingLaws(cd).map { case (acd, lawFd) =>
        val env = Some(lawFd.id.unsafeToSymbolIdentifier.symbol)
        val tparams = lawFd.typeArgs
          .map(tp => s.typeOps.instantiateType(tp, acd.tpSubst))
          .map(tp => t.TypeParameterDef(transform(tp, env).asInstanceOf[t.TypeParameter]).copiedFrom(tp))
        val params = lawFd.params
          .map(vd => transform(vd.copy(tpe = s.typeOps.instantiateType(vd.tpe, acd.tpSubst)), env))
        val libraryFlag = if (cd.flags contains s.Library) Seq(t.Library, t.DropVCs) else Seq.empty
        val ghostFlag = if (lawFd.flags contains s.Ghost) Seq(t.Ghost) else Seq.empty

        t.exprOps.freshenSignature(new t.FunDef(
          SymbolIdentifier(lawFd.id.unsafeToSymbolIdentifier.symbol),
          tparams, params,
          transform(s.typeOps.instantiateType(lawFd.returnType, acd.tpSubst), env),
          t.Ensuring(
            t.BooleanLiteral(true).setPos(lawFd),
            t.Lambda(
              Seq(t.ValDef.fresh("res", t.BooleanType().setPos(lawFd)).setPos(lawFd)),
              t.MethodInvocation(
                t.This(t.ClassType(cd.id, cd.typeArgs map (transform(_, env))).setPos(lawFd)).setPos(lawFd),
                lawID(lawFd.id.unsafeToSymbolIdentifier),
                tparams.map(_.tp),
                params.map(_.toVariable)
              ).setPos(lawFd)
            ).setPos(lawFd)
          ).setPos(lawFd),
          Seq(t.IsMethodOf(cd.id), t.Derived(Some(lawFd.id)), t.Law) ++ libraryFlag ++ ghostFlag
        ).setPos(cd))
      }

      (transform(cd), functions)
    } else {
      (transform(cd), Seq.empty)
    }
  }
}

object Laws {
  def apply(tr: Trees)(using inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = {
    class Impl(override val s: tr.type, override val t: tr.type) extends Laws(s, t)
    new Impl(tr, tr)
  }
}
