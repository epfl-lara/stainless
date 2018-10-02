/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import stainless.ast.{Symbol, SymbolIdentifier}
import stainless.ast.SymbolIdentifier.IdentifierOps

trait Laws
  extends oo.CachingPhase
     with IdentitySorts { self =>

  val trees: Trees
  import trees._

  override final val s: trees.type = trees
  override final val t: trees.type = trees

  private[this] val Law = Annotation("law", Seq())
  private[this] def isLaw(fd: FunDef): Boolean = fd.flags contains Law

  private[this] val lawSymbol = new utils.ConcurrentCached[Symbol, Symbol](
    symbol => Symbol((symbol.path.init :+ s"${symbol.path.last}$$prop") mkString ".")
  )

  private[this] val lawID = new utils.ConcurrentCached[SymbolIdentifier, SymbolIdentifier](
    id => SymbolIdentifier(lawSymbol(id.symbol))
  )

  override protected final type TransformerContext = Symbols
  override protected final def getContext(symbols: s.Symbols) = symbols

  override protected final val funCache = new CustomCache[s.FunDef, FunctionResult]({ (fd, symbols) =>
    FunctionKey(fd, symbols) + new ValueKey(
      if ((fd.flags exists { case IsMethodOf(_) => true case _ => false }) && (fd.flags contains Law)) {
        symbols.firstSuper(fd.id.unsafeToSymbolIdentifier).toSet[Identifier]
      } else {
        Set.empty[Identifier]
      }
    )
  })

  override protected final type FunctionResult = (FunDef, Option[FunDef])
  override protected final def registerFunctions(symbols: Symbols, functions: Seq[FunctionResult]): Symbols = {
    symbols.withFunctions(functions.flatMap(p => p._1 +: p._2.toSeq))
  }

  override protected final def extractFunction(symbols: Symbols, fd: FunDef): FunctionResult = {
    if (fd.flags contains Law) {
      // Some sanity checks
      if (!fd.flags.exists { case IsMethodOf(_) => true case _ => false })
        throw MissformedStainlessCode(fd, "Unexpected non-method law")

      val cid = fd.flags.collectFirst { case IsMethodOf(id) => id }.get
      val cd = symbols.getClass(cid)
      val ct = ClassType(cid, cd.typeArgs).setPos(fd)

      if (!(cd.flags contains IsAbstract))
        throw MissformedStainlessCode(fd, "Unexpected law in non-abstract class")
      if (!symbols.isSubtypeOf(fd.returnType, BooleanType()))
        throw MissformedStainlessCode(fd, "Unexpected non-boolean typed law")
      if (!exprOps.withoutSpecs(fd.fullBody).isDefined)
        throw MissformedStainlessCode(fd, "Unexpected law without a body")
      if (symbols.isRecursive(fd.id))
        throw MissformedStainlessCode(fd, "Unexpected recursive law")

      val lid = lawID(fd.id.unsafeToSymbolIdentifier)

      val newFd: FunDef = {
        val vd = ValDef(FreshIdentifier("res"), BooleanType().setPos(fd.fullBody), Seq.empty).setPos(fd.fullBody)
        val newBody = Ensuring(NoTree(BooleanType().setPos(fd.fullBody)).setPos(fd.fullBody),
          Lambda(Seq(vd), And(
            vd.toVariable,
            MethodInvocation(
              This(ct).setPos(fd.fullBody),
              lid, fd.typeArgs, fd.params.map(_.toVariable)
            ).setPos(fd.fullBody)
          ).setPos(fd.fullBody)).setPos(fd.fullBody)
        ).setPos(fd.fullBody)

        fd.copy(fullBody = newBody, flags = (fd.flags ++ Seq(Law, IsAbstract)).distinct)
      }

      val propFd: FunDef = {
        val (specs, body) = exprOps.deconstructSpecs(fd.fullBody)(symbols)
        val newBody = exprOps.reconstructSpecs(specs, Some(andJoin(
          symbols.firstSuper(fd.id.unsafeToSymbolIdentifier).map { sid =>
            MethodInvocation(
              Super(ct).setPos(fd),
              lawID(sid), fd.typeArgs, fd.params.map(_.toVariable)
            ).setPos(fd)
          }.toSeq :+ body.get
        ).setPos(body.get)), fd.returnType)

        val newFlags = fd.flags.filter(_ != Law) :+ InlineOnce :+ Derived(fd.id)

        exprOps.freshenSignature(
          new FunDef(lid, fd.tparams, fd.params, fd.returnType, newBody, newFlags).setPos(fd)
        )
      }

      (newFd, Some(propFd))
    } else {
      (fd, None)
    }
  }

  private def missingLaws(cd: ClassDef)(implicit symbols: Symbols): Seq[(TypedClassDef, FunDef)] = {
    val lawSymbols = (cd +: cd.ancestors.map(_.cd)).reverse.foldLeft(Set.empty[Symbol]) {
      case (lawSymbols, cd) =>
        val methods = cd.methods
        val methodSymbols = methods.map(_.symbol).toSet
        val newSymbols = methods
          .filter(id => symbols.getFunction(id).flags contains Law)
          .map(_.symbol).toSet

        lawSymbols -- methodSymbols ++ newSymbols
    }

    lawSymbols.toSeq.sortBy(_.name).map { symbol =>
      val acd = cd.ancestors.find(_.cd.methods.exists(_.symbol == symbol)).get
      val lawFd = symbols.getFunction(acd.cd.methods.find(_.symbol == symbol).get)
      (acd, lawFd)
    }
  }

  override protected final val classCache = new CustomCache[s.ClassDef, ClassResult]({ (cd, symbols) =>
    new DependencyKey(
      cd.id,
      if (cd.flags contains IsAbstract) Set.empty[CacheKey]
      else missingLaws(cd)(symbols).map { case (acd, fd) =>
        ClassKey(acd.cd, symbols) + FunctionKey(fd, symbols) + new ValueKey(acd.tpSubst)
      }.toSet[CacheKey]
    )
  })

  override protected final type ClassResult = (t.ClassDef, Seq[t.FunDef])
  override protected final def registerClasses(symbols: Symbols, classes: Seq[ClassResult]): Symbols = {
    val (cls, funs) = classes.unzip
    symbols.withClasses(cls).withFunctions(funs.flatten)
  }

  override protected final def extractClass(symbols: Symbols, cd: ClassDef): ClassResult = {
    if (!(cd.flags contains IsAbstract)) {
      val functions = missingLaws(cd)(symbols).map { case (acd, lawFd) =>
        exprOps.freshenSignature(new FunDef(
          SymbolIdentifier(lawFd.id.unsafeToSymbolIdentifier.symbol),
          lawFd.typeArgs
            .map(tp => typeOps.instantiateType(tp, acd.tpSubst))
            .map(tp => TypeParameterDef(tp.asInstanceOf[TypeParameter])),
          lawFd.params.map(vd => vd.copy(tpe = typeOps.instantiateType(vd.tpe, acd.tpSubst))),
          typeOps.instantiateType(lawFd.returnType, acd.tpSubst),
          BooleanLiteral(true).setPos(lawFd),
          Seq(IsMethodOf(cd.id))
        ).setPos(cd))
      }

      (cd, functions)
    } else {
      (cd, Seq.empty)
    }
  }
}

object Laws {
  def apply(tr: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new {
    override val trees: tr.type = tr
  } with Laws {
    override val context = ctx
  }
}
