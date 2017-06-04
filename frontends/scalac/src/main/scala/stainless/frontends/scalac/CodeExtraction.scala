/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import stainless.ast.SymbolIdentifier
import extraction.xlang.{trees => xt}

import scala.reflect.internal.util._
import scala.collection.mutable.{Map => MutableMap, ListBuffer}

import scala.language.implicitConversions

trait CodeExtraction extends ASTExtractors {
  self: StainlessExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import scala.collection.immutable.Set

  lazy val reporter = self.ctx.reporter
  implicit val debugSection = DebugSectionExtraction

  implicit def scalaPosToInoxPos(p: global.Position): inox.utils.Position = {
    if (p == NoPosition) {
      inox.utils.NoPosition
    } else if (p.isRange) {
      val start = p.focusStart
      val end   = p.focusEnd
      inox.utils.RangePosition(start.line, start.column, start.point,
                               end.line, end.column, end.point,
                               p.source.file.file)
    } else {
      inox.utils.OffsetPosition(p.line, p.column, p.point,
                                p.source.file.file)
    }
  }

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(val pos: Position, msg: String, val ot: Option[Tree])
    extends Exception(msg)

  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }

  class Extraction(compilationUnits: List[CompilationUnit]) {

    private val symbolToSymbol: MutableMap[Symbol, ast.Symbol] = MutableMap.empty
    private val symbolToIdentifier: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
    private def getIdentifier(sym: Symbol): SymbolIdentifier = {
      //val sym = s.accessedOrSelf.orElse(s)
      symbolToIdentifier.get(sym) match {
        case Some(id) => id
        case None =>
          val top = if (sym.overrideChain.nonEmpty) sym.overrideChain.last else sym
          val symbol = symbolToSymbol.get(top) match {
            case Some(symbol) => symbol
            case None =>
              val name = sym.fullName.toString.trim
              val symbol = ast.Symbol(if (name.endsWith("$")) name.init else name)
              symbolToSymbol += top -> symbol
              symbol
          }

          val id = SymbolIdentifier(symbol)
          symbolToIdentifier += sym -> id
          id
      }
    }

    private def annotationsOf(sym: Symbol, ignoreOwner: Boolean = false): Set[xt.Flag] = {
      getAnnotations(sym, ignoreOwner).map { case (name, args) =>
        xt.extractFlag(name, args.map(extractTree(_)(DefContext())))
      }.toSet
    }

    case class DefContext(
      tparams: Map[Symbol, xt.TypeParameter] = Map(),
      vars: Map[Symbol, () => xt.Expr] = Map(),
      mutableVars: Map[Symbol, () => xt.Variable] = Map(),
      localFuns: Map[Symbol, (xt.ValDef, Seq[xt.TypeParameterDef])] = Map(),
      isExtern: Boolean = false
    ){
      def union(that: DefContext) = {
        copy(this.tparams ++ that.tparams,
             this.vars ++ that.vars,
             this.mutableVars ++ that.mutableVars,
             this.localFuns ++ that.localFuns,
             this.isExtern || that.isExtern)
      }

      def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)

      def withNewVars(nvars: Traversable[(Symbol, () => xt.Expr)]) = {
        copy(vars = vars ++ nvars)
      }

      def withNewVar(s: Symbol, v: () => xt.Variable) = {
        copy(vars = vars + (s -> v))
      }

      def withNewMutableVar(s: Symbol, v: () => xt.Variable) = {
        copy(mutableVars = mutableVars + (s -> v))
      }

      def withNewMutableVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
        copy(mutableVars = mutableVars ++ nvars)
      }

      def withLocalFun(sym: Symbol, vd: xt.ValDef, tparams: Seq[xt.TypeParameterDef]) = {
        copy(localFuns = this.localFuns + (sym -> ((vd, tparams))))
      }
    }

    def extractProgram: (List[xt.UnitDef], Program { val trees: xt.type }) = try {
      val unitsAcc     = new ListBuffer[xt.UnitDef]
      val classesAcc   = new ListBuffer[xt.ClassDef]
      val functionsAcc = new ListBuffer[xt.FunDef]

      for (u <- compilationUnits) {
        val (id, stats) = u.body match {
          // package object
          case PackageDef(refTree, List(pd @ PackageDef(inner, body))) =>
            (FreshIdentifier(extractRef(inner).mkString("$")), pd.stats)

          case pd @ PackageDef(refTree, lst) =>
            (FreshIdentifier(u.source.file.name.replaceFirst("[.][^.]+$", "")), pd.stats)

          case _ => outOfSubsetError(u.body, "Unexpected unit body")
        }

        val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(stats)
        assert(functions.isEmpty, "Packages shouldn't contain functions")

        unitsAcc += xt.UnitDef(
          id,
          imports,
          classes,
          subs,
          !(Main.libraryFiles contains u.source.file.absolute.path)
        ).setPos(u.body.pos)

        classesAcc ++= allClasses
        functionsAcc ++= allFunctions
      }

      val program: Program { val trees: xt.type } = new inox.Program {
        val trees: xt.type = xt
        val ctx = self.ctx
        val symbols = xt.NoSymbols.withClasses(classesAcc).withFunctions(functionsAcc)
      }

      (unitsAcc.toList, program)
    } catch {
      case e: ImpureCodeEncounteredException =>
        reporter.debug(s"Extraction failed because of:")
        reporter.debug(e.pos, e.getMessage, e)
        reporter.fatalError(e.pos, e.getMessage)
    }

    // This one never fails, on error, it returns Untyped
    def stainlessType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = {
      try {
        extractType(tpt)
      } catch {
        case e: ImpureCodeEncounteredException =>
          reporter.debug(e.pos, "[ignored] " + e.getMessage, e)
          xt.Untyped
      }
    }

    private def extractStatic(stats: List[Tree]): (
      Seq[xt.Import],
      Seq[Identifier],
      Seq[Identifier],
      Seq[xt.ModuleDef],
      Seq[xt.ClassDef],
      Seq[xt.FunDef]
    ) = {
      var imports   : Seq[xt.Import]    = Seq.empty
      var classes   : Seq[Identifier]   = Seq.empty
      var functions : Seq[Identifier]   = Seq.empty
      var subs      : Seq[xt.ModuleDef] = Seq.empty

      var allClasses   : Seq[xt.ClassDef] = Seq.empty
      var allFunctions : Seq[xt.FunDef]   = Seq.empty

      for (d <- stats) d match {
        case EmptyTree =>
          // ignore

        case t if (
          (annotationsOf(t.symbol) contains xt.Ignore) ||
          (t.symbol.isSynthetic && !t.symbol.isImplicit)
        ) =>
          // ignore

        case ExtractorHelpers.ExSymbol("stainless", "annotation", "ignore") =>
          // ignore (can't be @ignored because of the dotty compiler)

        case ExConstructorDef() 
           | ExLazyFieldDef()
           | ExFieldAccessorFunction() =>
          // ignore

        case i @ Import(_, _) =>
          imports ++= extractImports(i)

        case td @ ExObjectDef(_, _) =>
          val (obj, newClasses, newFunctions) = extractObject(td)
          subs :+= obj
          allClasses ++= newClasses
          allFunctions ++= newFunctions

        case cd: ClassDef =>
          val (xcd, newFunctions) = extractClass(cd)
          classes :+= xcd.id
          allClasses :+= xcd
          allFunctions ++= newFunctions

        case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
          val fd = extractFunction(fsym, tparams, vparams, rhs)(DefContext())
          functions :+= fd.id
          allFunctions :+= fd

        case t @ ExFieldDef(fsym, _, rhs) =>
          val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
          functions :+= fd.id
          allFunctions :+= fd

        case t @ ExLazyAccessorFunction(fsym, _, rhs) =>
          val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
          functions :+= fd.id
          allFunctions :+= fd

        case t if t.symbol.isSynthetic =>
          // ignore

        case other =>
          reporter.warning(other.pos, "Could not extract tree in static container: " + other)
      }

      (imports, classes, functions, subs, allClasses, allFunctions)
    }

    def extractPackage(id: Identifier, u: CompilationUnit, pd: PackageDef): (xt.UnitDef, Seq[xt.ClassDef], Seq[xt.FunDef]) = {
      val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(pd.stats)
      assert(functions.isEmpty, "Packages shouldn't contain functions")

      val unit = xt.UnitDef(
        id,
        imports,
        classes,
        subs,
        !(Main.libraryFiles contains u.source.file.absolute.path)
      ).setPos(pd.pos)

      (unit, allClasses, allFunctions)
    }

    private def extractObject(obj: ClassDef): (xt.ModuleDef, Seq[xt.ClassDef], Seq[xt.FunDef]) = {
      val ExObjectDef(_, template) = obj
      val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(template.body)

      val module = xt.ModuleDef(
        getIdentifier(obj.symbol),
        imports,
        classes,
        functions,
        subs
      ).setPos(obj.pos)

      (module, allClasses, allFunctions)
    }

    private val ignoreClasses = Set(
      ObjectClass.tpe,
      SerializableClass.tpe,
      ProductRootClass.tpe,
      AnyRefClass.tpe
    )

    private val invSymbol = stainless.ast.Symbol("inv")

    private def extractClass(cd: ClassDef): (xt.ClassDef, Seq[xt.FunDef]) = {
      val sym = cd.symbol
      val id = getIdentifier(sym)

      val tparamsSyms = sym.tpe match {
        case TypeRef(_, _, tps) => typeParamSymbols(tps)
        case _ => Nil
      }

      val tparams = extractTypeParams(tparamsSyms)

      val tpCtx = DefContext((tparamsSyms zip tparams).toMap)

      val parents = cd.impl.parents.flatMap(p => p.tpe match {
        case tpe if ignoreClasses(tpe) => None
        case tp @ TypeRef(_, _, _) => Some(extractType(tp)(tpCtx, p.pos).asInstanceOf[xt.ClassType])
        case _ => None
      })

      val annots = annotationsOf(sym)
      val flags = annots ++
        (if (sym.isAbstractClass) Some(xt.IsAbstract) else None) ++
        (if (sym.isSealed) Some(xt.IsSealed) else None)

      val constructor = cd.impl.children.find {
        case ExConstructorDef() => true
        case _ => false
      }.get.asInstanceOf[DefDef]

      val vds = constructor.vparamss.flatten
      val symbols = cd.impl.children.collect {
        case df @ DefDef(_, name, _, _, _, _)
        if df.symbol.isAccessor && df.symbol.isParamAccessor && !name.endsWith("_$eq") => df.symbol
      }

      val fields = (symbols zip vds).map { case (sym, vd) =>
        val tpe = stainlessType(vd.tpt.tpe)(tpCtx, vd.pos)
        val id = getIdentifier(sym)
        val flags = annotationsOf(sym, ignoreOwner = true)
        if (sym.accessedOrSelf.isMutable) xt.VarDef(id, tpe, flags).setPos(sym.pos)
        else xt.ValDef(id, tpe, flags).setPos(sym.pos)
      }

      val defCtx = tpCtx.withNewVars((symbols zip fields.map(vd => () => vd.toVariable)).toMap)

      var invariants: Seq[xt.Expr] = Seq.empty
      var methods: Seq[xt.FunDef] = Seq.empty

      for (d <- cd.impl.body) d match {
        case EmptyTree =>
          // ignore

        case t if (
          (annotationsOf(t.symbol) contains xt.Ignore) ||
          (t.symbol.isSynthetic && !t.symbol.isImplicit)
        ) =>
          // ignore

        case ExRequiredExpression(body) =>
          invariants :+= extractTree(body)(defCtx)

        case dd @ DefDef(_, name, _, _, _, _) if dd.symbol.name.toString.startsWith("copy$default$") =>
          // @nv: FIXME - think about handling default value functions

        case t @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
          methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx)

        case t @ ExFieldDef(fsym, _, rhs) =>
          methods :+= extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)

        case t @ ExLazyAccessorFunction(fsym, _, rhs) =>
          methods :+= extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)

        case ExCaseClassSyntheticJunk()
           | ExConstructorDef()
           | ExLazyFieldDef()
           | ExFieldAccessorFunction() =>
             // ignore

        case ValDef(_, _, _, _) =>
          // ignore (corresponds to constructor fields)

        case d if d.symbol.isSynthetic =>
          // ignore

        case d if d.symbol.isVar =>
          // ignore

        case other =>
          reporter.warning(other.pos, "Could not extract tree in class: " + other + " (" + other.getClass + ")")
      }

      val optInv = if (invariants.isEmpty) None else Some({
        val fd = new xt.FunDef(SymbolIdentifier(invSymbol), Seq.empty, Seq.empty, xt.BooleanType,
          if (invariants.size == 1) invariants.head else xt.And(invariants),
          Set(xt.IsInvariant) ++ annots
        )
        fd.setPos(inox.utils.Position.between(invariants.head.getPos, invariants.last.getPos))
        fd
      })

      val allMethods = (methods ++ optInv).map(fd => fd.copy(flags = fd.flags + xt.IsMethodOf(id)))

      val xcd = new xt.ClassDef(
        id,
        tparams.map(tp => xt.TypeParameterDef(tp)),
        parents,
        fields,
        flags
      ).setPos(sym.pos)

      (xcd, allMethods)
    }

    private def getSelectChain(e: Tree): List[String] = {
      def rec(e: Tree): List[Name] = e match {
        case Select(q, name) => name :: rec(q)
        case Ident(name) => List(name)
        case EmptyTree => List()
        case _ =>
          ctx.reporter.internalError("getSelectChain: unexpected Tree:\n" + e.toString)
      }
      rec(e).reverseMap(_.toString)
    }

    private def extractRef(ref: RefTree): List[String] = {
      (getSelectChain(ref.qualifier) :+ ref.name.toString).filter(_ != "<empty>")
    }

    private def extractImports(i: Import): Seq[xt.Import] = {
      val Import(expr, sels) = i

      val prefix = getSelectChain(expr)

      val allSels = sels map { prefix :+ _.name.toString }

      // Make a different import for each selector at the end of the chain
      allSels flatMap { selectors =>
        assert(selectors.nonEmpty)
        val (thePath, isWild) = selectors.last match {
          case "_" => (selectors.dropRight(1), true)
          case _   => (selectors, false)
        }

        Some(xt.Import(thePath, isWild))
      }
    }

    private def extractFunction(
      sym: Symbol,
      tparams: Seq[Symbol],
      vparams: Seq[ValDef],
      rhs: Tree,
      typeParams: Option[Seq[xt.TypeParameter]] = None
    )(implicit dctx: DefContext): xt.FunDef = {

      // Type params of the function itself
      val extparams = typeParamSymbols(sym.typeParams.map(_.tpe))
      val ntparams = typeParams.getOrElse(extractTypeParams(extparams))

      val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams).toMap)

      val newParams = sym.info.paramss.flatten.map { sym =>
        val ptpe = stainlessType(sym.tpe)(nctx, sym.pos)
        val tpe = if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe) else ptpe
        val flags = annotationsOf(sym, ignoreOwner = true)
        xt.ValDef(FreshIdentifier(sym.name.toString).setPos(sym.pos), tpe, flags).setPos(sym.pos)
      }

      val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

      val id = getIdentifier(sym)

      var flags = annotationsOf(sym).toSet ++
        (if (sym.isImplicit) Set(xt.Inline, xt.Implicit) else Set()) ++
        (if (sym.isAccessor) Set(xt.IsField(sym.isLazy)) else Set())

      val body =
        if (!(flags contains xt.IsField(true))) rhs
        else rhs match {
          case Block(List(Assign(_, realBody)), _) => realBody
          case _ => outOfSubsetError(rhs, "Wrong form of lazy accessor")
        }

      val paramsMap = (vparams.map(_.symbol) zip newParams).map { case (s, vd) =>
        s -> (if (s.isByNameParam) () => xt.Application(vd.toVariable, Seq()) else () => vd.toVariable)
      }.toMap

      val fctx = dctx
        .withNewVars(paramsMap)
        .copy(tparams = dctx.tparams ++ (tparams zip ntparams))
        .copy(isExtern = dctx.isExtern || (flags contains xt.Extern))

      val finalBody = if (rhs == EmptyTree) {
        flags += xt.IsAbstract
        xt.NoTree(returnType).setPos(sym.pos)
      } else {
        xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
      }

      val fullBody = if (fctx.isExtern) {
        xt.exprOps.withBody(finalBody, xt.NoTree(returnType).setPos(body.pos))
      } else {
        finalBody
      }

      new xt.FunDef(
        id,
        ntparams.map(tp => xt.TypeParameterDef(tp)),
        newParams,
        returnType,
        fullBody,
        flags
      ).setPos(sym.pos)
    }

    private def typeParamSymbols(tps: Seq[Type]): Seq[Symbol] = tps.flatMap {
      case TypeRef(_, sym, Nil) =>
        Some(sym)
      case t =>
        outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
        None
    }

    private def extractTypeParams(syms: Seq[Symbol]): Seq[xt.TypeParameter] = syms.map { sym =>
      val variance = if (sym.isCovariant) Some(xt.Variance(true)) else if (sym.isContravariant) Some(xt.Variance(false)) else None
      xt.TypeParameter(FreshIdentifier(sym.name.toString), variance.toSet)
    }

    private def extractPattern(p: Tree, binder: Option[xt.ValDef] = None)(implicit dctx: DefContext): (xt.Pattern, DefContext) = p match {
      case b @ Bind(name, t @ Typed(pat, tpt)) =>
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(b.symbol, ignoreOwner = true)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol, () => vd.toVariable)
        extractPattern(t, Some(vd))(pctx)

      case b @ Bind(name, pat) =>
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(b), annotationsOf(b.symbol, ignoreOwner = true)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol, () => vd.toVariable)
        extractPattern(pat, Some(vd))(pctx)

      case t @ Typed(Ident(nme.WILDCARD), tpt) =>
        extractType(tpt) match {
          case ct: xt.ClassType =>
            (xt.InstanceOfPattern(binder, ct).setPos(p.pos), dctx)

          case lt =>
            outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
        }

      case Ident(nme.WILDCARD) =>
        (xt.WildcardPattern(binder).setPos(p.pos), dctx)

      case s @ Select(_, b) if s.tpe.typeSymbol.isCase =>
        // case Obj =>
        extractType(s) match {
          case ct: xt.ClassType =>
            (xt.ClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
          case _ =>
            outOfSubsetError(s, "Invalid type "+s.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) =>
        extractType(a) match {
          case ct: xt.ClassType =>
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
            val nctx = subDctx.foldLeft(dctx)(_ union _)
            (xt.ClassPattern(binder, ct, subPatterns).setPos(p.pos), nctx)

          case xt.TupleType(argsTpes) =>
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
            val nctx = subDctx.foldLeft(dctx)(_ union _)
            (xt.TuplePattern(binder, subPatterns).setPos(p.pos), nctx)

          case _ =>
            outOfSubsetError(a, "Invalid type "+a.tpe+" for .isInstanceOf")
        }

      case ExBigIntPattern(n: Literal) =>
        val lit = xt.IntegerLiteral(BigInt(n.value.stringValue))
        (xt.LiteralPattern(binder, lit), dctx)

      case ExInt8Literal(i)    => (xt.LiteralPattern(binder, xt.Int8Literal(i)),    dctx)
      case ExInt16Literal(i)   => (xt.LiteralPattern(binder, xt.Int16Literal(i)),   dctx)
      case ExInt32Literal(i)   => (xt.LiteralPattern(binder, xt.Int32Literal(i)),   dctx)
      case ExInt64Literal(i)   => (xt.LiteralPattern(binder, xt.Int64Literal(i)),   dctx)
      case ExBooleanLiteral(b) => (xt.LiteralPattern(binder, xt.BooleanLiteral(b)), dctx)
      case ExUnitLiteral()     => (xt.LiteralPattern(binder, xt.UnitLiteral()),     dctx)
      case ExStringLiteral(s)  => (xt.LiteralPattern(binder, xt.StringLiteral(s)),  dctx)

      case up @ ExUnapplyPattern(t, args) =>
        val (sub, ctx) = args.map (extractPattern(_)).unzip
        val nctx = ctx.foldLeft(dctx)(_ union _)
        val id = getIdentifier(t.symbol)
        val tps = t match {
          case TypeApply(_, tps) => tps.map(extractType)
          case _ => Seq.empty
        }

        (xt.UnapplyPattern(binder, id, tps, sub).setPos(up.pos), ctx.foldLeft(dctx)(_ union _))

      case _ =>
        outOfSubsetError(p, "Unsupported pattern: " + p)
    }

    private def extractMatchCase(cd: CaseDef)(implicit dctx: DefContext): xt.MatchCase = {
      val (recPattern, ndctx) = extractPattern(cd.pat)
      val recBody             = extractTree(cd.body)(ndctx)

      if(cd.guard == EmptyTree) {
        xt.MatchCase(recPattern, None, recBody).setPos(cd.pos)
      } else {
        val recGuard = extractTree(cd.guard)(ndctx)
        xt.MatchCase(recPattern, Some(recGuard), recBody).setPos(cd.pos)
      }
    }

    private def extractTreeOrNoTree(tr: Tree)(implicit dctx: DefContext): xt.Expr = {
      try {
        extractTree(tr)
      } catch {
        case e: ImpureCodeEncounteredException =>
          if (dctx.isExtern) {
            xt.NoTree(extractType(tr)).setPos(tr.pos)
          } else {
            throw e
          }
      }
    }

    private def extractBlock(es: List[Tree])(implicit dctx: DefContext): xt.Expr = {
      val fctx = es.collect {
        case ExFunctionDef(sym, tparams, vparams, tpt, rhs) => (sym, tparams)
      }.foldLeft(dctx) { case (dctx, (sym, tparams)) =>
        val extparams = typeParamSymbols(sym.typeParams.map(_.tpe))
        val tparams = extractTypeParams(extparams)
        val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip tparams).toMap)

        val paramTypes = sym.info.paramss.flatten.map { sym =>
          val ptpe = stainlessType(sym.tpe)(nctx, sym.pos)
          if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe) else ptpe
        }
        val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)
        val name = xt.ValDef(
          getIdentifier(sym),
          xt.FunctionType(paramTypes, returnType).setPos(sym.pos),
          annotationsOf(sym)
        ).setPos(sym.pos)

        dctx.withLocalFun(sym, name, tparams.map(tp => xt.TypeParameterDef(tp)))
      }

      val (vds, vctx) = es.collect {
        case v @ ValDef(_, name, tpt, _) => (v.symbol, name, tpt)
      }.foldLeft((Map.empty[Symbol, xt.ValDef], fctx)) { case ((vds, dctx), (sym, name, tpt)) =>
        if (!sym.isMutable) {
          val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
          (vds + (sym -> vd), dctx.withNewVar(sym, () => vd.toVariable))
        } else {
          val vd = xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
          (vds + (sym -> vd), dctx.withNewMutableVar(sym, () => vd.toVariable))
        }
      }

      def rec(es: List[Tree]): xt.Expr = es match {
        case Nil => xt.UnitLiteral()

        case (e @ ExAssertExpression(contract, oerr)) :: xs =>
          val const = extractTree(contract)(vctx)
          val b     = rec(xs)
          xt.Assert(const, oerr, b).setPos(e.pos)

        case (e @ ExRequiredExpression(contract)) :: xs =>
          val pre = extractTree(contract)(vctx)
          val b   = rec(xs)
          xt.Require(pre, b).setPos(e.pos)

        case (e @ ExDecreasesExpression(ranks)) :: xs =>
          val rs = ranks.map(extractTree(_)(vctx))
          val b = rec(xs)
          xt.Decreases(xt.tupleWrap(rs), b).setPos(e.pos)

        case (d @ ExFunctionDef(sym, tparams, vparams, tpt, rhs)) :: xs =>
          val (vd, tdefs) = vctx.localFuns(sym)
          val fd = extractFunction(sym, tparams, vparams, rhs, typeParams = Some(tdefs.map(_.tp)))(vctx)
          val letRec = xt.LocalFunDef(vd, tdefs, xt.Lambda(fd.params, fd.fullBody).setPos(d.pos))

          rec(xs) match {
            case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body).setPos(d.pos)
            case other => xt.LetRec(Seq(letRec), other).setPos(d.pos)
          }

        case (v @ ValDef(mods, name, tpt, _)) :: xs =>
          if (mods.isMutable) {
            xt.LetVar(vds(v.symbol), extractTree(v.rhs)(vctx), rec(xs)).setPos(v.pos)
          } else {
            xt.Let(vds(v.symbol), extractTree(v.rhs)(vctx), rec(xs)).setPos(v.pos)
          }

        case x :: Nil =>
          extractTree(x)(vctx)

        case x :: rest =>
          rec(rest) match {
            case xt.Block(elems, last) =>
              xt.Block(extractTree(x)(vctx) +: elems, last).setPos(x.pos)
            case e =>
              xt.Block(Seq(extractTree(x)(vctx)), e).setPos(x.pos)
          }
      }

      rec(es)
    }

    private def extractArgs(sym: Symbol, args: Seq[Tree])(implicit dctx: DefContext): Seq[xt.Expr] = {
      (sym.paramLists.flatten zip args.map(extractTree)).map {
        case (sym, e) => if (sym.isByNameParam) xt.Lambda(Seq.empty, e).setPos(e.getPos) else e
      }
    }

    private def extractTree(tr: Tree)(implicit dctx: DefContext): xt.Expr = (tr match {
      case Block(es, e) =>
        val b = extractBlock(es :+ e)
        xt.exprOps.flattenBlocks(b)

      case ExAssertExpression(e, oerr) =>
        xt.Assert(extractTree(e), oerr, xt.UnitLiteral().setPos(tr.pos))

      case ExRequiredExpression(body) =>
        xt.Require(extractTree(body), xt.UnitLiteral().setPos(tr.pos))

      case ExEnsuredExpression(body, contract) =>
        val post = extractTree(contract)
        val b = extractTreeOrNoTree(body)

        val closure = post match {
          case l: xt.Lambda => l
          case other =>
            val tpe = extractType(body)
            val vd = xt.ValDef(FreshIdentifier("res"), tpe, Set.empty).setPos(post)
            xt.Lambda(Seq(vd), extractType(contract) match {
              case xt.BooleanType => post
              case _ => xt.Application(other, Seq(vd.toVariable)).setPos(post)
            }).setPos(post)
        }

        xt.Ensuring(b, closure)

      case t @ ExHoldsWithProofExpression(body, ExMaybeBecauseExpressionWrapper(proof)) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
        val p = extractTreeOrNoTree(proof)
        val and = xt.And(p, vd.toVariable).setPos(tr.pos)
        val post = xt.Lambda(Seq(vd), and).setPos(tr.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      case t @ ExHoldsExpression(body) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
        val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      // If the because statement encompasses a holds statement
      case t @ ExBecauseExpression(ExHoldsExpression(body), proof) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
        val p = extractTreeOrNoTree(proof)
        val and = xt.And(p, vd.toVariable).setPos(tr.pos)
        val post = xt.Lambda(Seq(vd), and).setPos(tr.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      case t @ ExComputesExpression(body, expected) =>
        val b = extractTreeOrNoTree(body).setPos(body.pos)
        val expectedExpr = extractTreeOrNoTree(expected).setPos(expected.pos)
        val vd = xt.ValDef(FreshIdentifier("res"), extractType(body), Set.empty).setPos(tr.pos)
        val post = xt.Lambda(Seq(vd), xt.Equals(vd.toVariable, expectedExpr)).setPos(tr.pos)
        xt.Ensuring(b, post)

      case ExPreExpression(f) =>
        xt.Pre(extractTree(f))

      case t @ ExBigLengthExpression(input) =>
        xt.StringLength(extractTreeOrNoTree(input))

      case t @ ExBigSubstringExpression(input, start) =>
        val in = extractTreeOrNoTree(input)
        val st = extractTreeOrNoTree(start)
        val vd = xt.ValDef(FreshIdentifier("s", true), xt.StringType, Set.empty)
        xt.Let(vd, in, xt.SubString(vd.toVariable, st, xt.StringLength(vd.toVariable)))

      case t @ ExBigSubstring2Expression(input, start, end) =>
        val in = extractTreeOrNoTree(input)
        val st = extractTreeOrNoTree(start)
        val en = extractTreeOrNoTree(end)
        xt.SubString(in, st, en)

      case ExArrayLiteral(tpe, args) =>
        xt.FiniteArray(args.map(extractTree), extractType(tpe)(dctx, tr.pos))

      case s @ ExCaseObject(sym) =>
        extractType(s) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, Seq.empty)
          case tpe => outOfSubsetError(tr, "Unexpected class constructor type: " + tpe)
        }

      case ExTuple(tpes, exprs) =>
        xt.Tuple(exprs map extractTree)

      case ExOldExpression(t) => t match {
        case t: This => xt.Old(extractTree(t))
        case v if dctx.isVariable(v.symbol) =>
          xt.Old(dctx.vars.get(v.symbol).orElse(dctx.mutableVars.get(v.symbol)).get())
        case _ => outOfSubsetError(tr, "Old is only defined on `this` and variables")
      }

      case ExErrorExpression(str, tpt) =>
        xt.Error(extractType(tpt), str)

      case ExTupleExtract(tuple, index) =>
        xt.TupleSelect(extractTree(tuple), index)

      /**
       * XLang Extractors
       */

      case a @ ExAssign(sym, rhs) =>
        dctx.mutableVars.get(sym) match {
          case Some(fun) =>
            xt.Assignment(fun().setPos(a.pos), extractTree(rhs))

          case None =>
            outOfSubsetError(a, "Undeclared variable.")
        }

      case wh @ ExWhile(cond, body) =>
        xt.While(extractTree(cond), extractTree(body), None)

      case wh @ ExWhileWithInvariant(cond, body, inv) =>
        xt.While(extractTree(cond), extractTree(body), Some(extractTree(inv)))

      case update @ ExUpdate(lhs, index, newValue) =>
        xt.ArrayUpdate(extractTree(lhs), extractTree(index), extractTree(newValue))

      case ExBigIntLiteral(n: Literal) =>
        xt.IntegerLiteral(BigInt(n.value.stringValue))

      case ExBigIntLiteral(n) => outOfSubsetError(tr, "Non-literal BigInt constructor")

      case ExIntToBigInt(tree) =>
        extractTree(tree) match {
          case xt.Int32Literal(n) => xt.IntegerLiteral(BigInt(n))
          case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
        }

      case ExRealLiteral(n, d) =>
        (extractTree(n), extractTree(d)) match {
          case (xt.IntegerLiteral(n), xt.IntegerLiteral(d)) => xt.FractionLiteral(n, d)
          case _ => outOfSubsetError(tr, "Real not build from literals")
        }

      case ExRealIntLiteral(n) =>
        extractTree(n) match {
          case xt.IntegerLiteral(n) => xt.FractionLiteral(n, 1)
          case _ => outOfSubsetError(tr, "Real not build from literals")
        }

      case ExInt8Literal(v) => xt.Int8Literal(v)
      case ExInt16Literal(v) => xt.Int16Literal(v)
      case ExInt32Literal(v) => xt.Int32Literal(v)
      case ExInt64Literal(v) => xt.Int64Literal(v)
      case ExBooleanLiteral(v) => xt.BooleanLiteral(v)
      case ExUnitLiteral() => xt.UnitLiteral()
      case ExCharLiteral(c) => xt.CharLiteral(c)
      case ExStringLiteral(s) => xt.StringLiteral(s)

      case ExIdentity(body) => extractTree(body)

      case ExTyped(e, _) => extractTree(e)

      case ex @ ExIdentifier(sym, tpt) =>
        dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
          case Some(builder) => builder().setPos(ex.pos)
          case None => dctx.localFuns.get(sym) match {
            case Some((vd, tparams)) =>
              assert(tparams.isEmpty, "Unexpected application " + ex + " without type parameters")
              xt.ApplyLetRec(vd.toVariable, Seq.empty, Seq.empty, Seq.empty)
            case None => xt.FunctionInvocation(getIdentifier(sym), Seq.empty, Seq.empty)
          }
        }

      case hole @ ExHoleExpression(tpt, exprs) =>
        // FIXME: we ignore [[exprs]] for now...
        xt.Hole(extractType(tpt))

      case chs @ ExChooseExpression(body) =>
        extractTree(body) match {
          case xt.Lambda(Seq(vd), body) => xt.Choose(vd, body)
          case _ => outOfSubsetError(tr, "Unexpected choose definition")
        }

      case l @ ExLambdaExpression(args, body) =>
        val vds = args map(vd => xt.ValDef(
          FreshIdentifier(vd.symbol.name.toString),
          extractType(vd.tpt),
          annotationsOf(vd.symbol, ignoreOwner = true)
        ).setPos(vd.pos))

        val newVars = (args zip vds).map { case (vd, lvd) =>
          vd.symbol -> (() => lvd.toVariable)
        }

        val exBody = extractTree(body)(dctx.withNewVars(newVars))
        xt.Lambda(vds, exBody)

      case ExForallExpression(contract) =>
        extractTree(contract) match {
          case l: xt.Lambda => xt.Forall(l.args, l.body).setPos(l)
          case pred => extractType(contract) match {
            case xt.FunctionType(from, to) =>
              val args = from.map(tpe => xt.ValDef(FreshIdentifier("x", true), tpe).setPos(pred))
              xt.Forall(args, xt.Application(pred, args.map(_.toVariable)).setPos(pred))
            case _ => 
              outOfSubsetError(tr, "Unsupported forall definition: " + tr)
          }
        }

      case ExFiniteMap(tptFrom, tptTo, args) =>
        val to = extractType(tptTo)
        val pairs = args.map {
          case ExTuple(_, Seq(key, value)) =>
            (extractTree(key), extractTree(value))
          case tree =>
            val ex = extractTree(tree)
            (xt.TupleSelect(ex, 1), xt.TupleSelect(ex, 2))
        }

        val somePairs = pairs.map { case (key, value) =>
          key -> xt.ClassConstructor(
            xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
            Seq(value)
          ).setPos(tr.pos)
        }

        val dflt = xt.ClassConstructor(
          xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
          Seq.empty
        ).setPos(tr.pos)

        val optTo = xt.ClassType(getIdentifier(optionSymbol), Seq(to))
        xt.FiniteMap(somePairs, dflt, extractType(tptFrom), optTo)

      case ExFiniteSet(tpt, args) =>
        xt.FiniteSet(args.map(extractTree), extractType(tpt))

      case ExFiniteBag(tpt, args) =>
        xt.FiniteBag(args.map {
          case ExTuple(_, Seq(key, value)) =>
            (extractTree(key), extractTree(value))
          case tree =>
            val ex = extractTree(tree)
            (xt.TupleSelect(ex, 1), xt.TupleSelect(ex, 2))
        }, extractType(tpt))

      case ExClassConstruction(tpt, args) =>
        extractType(tpt) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, args.map(extractTree))
          case _ => outOfSubsetError(tr, "Construction of a non-class type.")
        }

      case ExNot(e)        => xt.Not(extractTree(e))
      case ExUMinus(e)     => injectCast(xt.UMinus)(e)
      case ExBVNot(e)      => injectCast(xt.BVNot)(e)

      case ExNotEquals(l, r) => xt.Not(((extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
        case (bi @ xt.BVLiteral(_, _), _, e, xt.IntegerType) => xt.Equals(xt.IntegerLiteral(bi.toBigInt).setPos(l.pos), e)
        case (e, xt.IntegerType, bi @ xt.BVLiteral(_, _), _) => xt.Equals(e, xt.IntegerLiteral(bi.toBigInt).setPos(r.pos))
        case _ => injectCasts(xt.Equals)(l, r)
      }).setPos(tr.pos))

      case ExEquals(l, r) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
        case (bi @ xt.BVLiteral(_, _), _, e, xt.IntegerType) => xt.Equals(xt.IntegerLiteral(bi.toBigInt).setPos(l.pos), e)
        case (e, xt.IntegerType, bi @ xt.BVLiteral(_, _), _) => xt.Equals(e, xt.IntegerLiteral(bi.toBigInt).setPos(r.pos))
        case _ => injectCasts(xt.Equals)(l, r)
      }

      case ExArrayFill(baseType, length, defaultValue) =>
        val lengthRec = extractTree(length)
        val defaultValueRec = extractTree(defaultValue)
        xt.LargeArray(Map.empty, extractTree(defaultValue), extractTree(length), extractType(baseType))

      case ExIfThenElse(t1,t2,t3) =>
        xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

      case ExAsInstanceOf(expr, tt) =>
        extractType(tt) match {
          case ct: xt.ClassType => xt.AsInstanceOf(extractTree(expr), ct)
          case _ => outOfSubsetError(tr, "asInstanceOf can only cast to class types")
        }

      case ExIsInstanceOf(expr, tt) =>
        extractType(tt) match {
          case ct: xt.ClassType => xt.IsInstanceOf(extractTree(expr), ct)
          case _ => outOfSubsetError(tr, "isInstanceOf can only be used with class types")
        }

      case pm @ ExPatternMatching(sel, cses) =>
        val rs = extractTree(sel)
        val rc = cses.map(extractMatchCase)
        xt.MatchExpr(rs, rc)

      case t: This =>
        extractType(t) match {
          case ct: xt.ClassType => xt.This(ct)
          case _ => outOfSubsetError(t, "Invalid usage of `this`")
        }

      case aup @ ExArrayUpdated(ar, k, v) =>
        xt.ArrayUpdated(extractTree(ar), extractTree(k), extractTree(v))

      case l @ ExListLiteral(tpe, elems) =>
        val rtpe = extractType(tpe)
        val cons = xt.ClassType(getIdentifier(consSymbol), Seq(rtpe))
        val nil  = xt.ClassType(getIdentifier(nilSymbol),  Seq(rtpe))

        elems.foldRight(xt.ClassConstructor(nil, Seq())) {
          case (e, ls) => xt.ClassConstructor(cons, Seq(extractTree(e), ls))
        }

      case ExImplies(lhs, rhs) =>
        xt.Implies(extractTree(lhs), extractTree(rhs))

      case c @ ExCall(rec, sym, tps, args) => rec match {
        case None =>
          dctx.localFuns.get(sym) match {
            case None =>
              xt.FunctionInvocation(getIdentifier(sym), tps.map(extractType), extractArgs(sym, args))
            case Some((vd, tparams)) =>
              xt.ApplyLetRec(vd.toVariable, tparams.map(_.tp), tps.map(extractType), extractArgs(sym, args))
          }

        case Some(lhs) => extractType(lhs) match {
          case ct: xt.ClassType =>
            val isMethod = sym.isMethod &&
              !sym.isCaseAccessor && !sym.accessedOrSelf.isCaseAccessor &&
              !(sym.isAccessor && sym.owner.isImplicit)

            if (isMethod) xt.MethodInvocation(
              extractTree(lhs),
              getIdentifier(sym),
              tps.map(extractType),
              extractArgs(sym, args)
            ) else args match {
              case Seq() =>
                xt.ClassSelector(extractTree(lhs), getIdentifier(sym))
              case Seq(rhs) =>
                val getter = sym.accessed.getterIn(sym.owner)
                xt.FieldAssignment(extractTree(lhs), getIdentifier(getter), extractTree(rhs))
              case _ => outOfSubsetError(tr, "Unexpected call")
            }

          case ft: xt.FunctionType =>
            xt.Application(extractTree(lhs), args.map(extractTree))

          case tpe => (tpe, sym.name.decode.toString, args) match {
            case (xt.StringType, "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
            case (xt.IntegerType | xt.BVType(_) | xt.RealType, "+", Seq(rhs)) => injectCasts(xt.Plus)(lhs, rhs)

            case (xt.SetType(_), "+",  Seq(rhs)) => xt.SetAdd(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "++", Seq(rhs)) => xt.SetUnion(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "&",  Seq(rhs)) => xt.SetIntersection(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "--", Seq(rhs)) => xt.SetDifference(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "subsetOf", Seq(rhs)) => xt.SubsetOf(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "contains", Seq(rhs)) => xt.ElementOfSet(extractTree(rhs), extractTree(lhs))
            case (xt.SetType(b), "-", Seq(rhs))  => xt.SetDifference(extractTree(lhs), xt.FiniteSet(Seq(extractTree(rhs)), b).setPos(tr.pos))

            case (xt.BagType(_), "+",   Seq(rhs)) => xt.BagAdd(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "++",  Seq(rhs)) => xt.BagUnion(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "&",   Seq(rhs)) => xt.BagIntersection(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "--",  Seq(rhs)) => xt.BagDifference(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "get", Seq(rhs)) => xt.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

            case (xt.ArrayType(_), "apply",   Seq(rhs))          => xt.ArraySelect(extractTree(lhs), extractTree(rhs))
            case (xt.ArrayType(_), "length",  Seq())             => xt.ArrayLength(extractTree(lhs))
            case (xt.ArrayType(_), "updated", Seq(index, value)) => xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))
            case (xt.ArrayType(_), "clone",   Seq())             => extractTree(lhs)

            case (xt.MapType(_, _), "get", Seq(rhs)) =>
              xt.MapApply(extractTree(lhs), extractTree(rhs))

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "apply", Seq(rhs)) =>
              val (l, r) = (extractTree(lhs), extractTree(rhs))
              val someTpe = xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos)
              xt.Assert(
                xt.IsInstanceOf(xt.MapApply(l, r).setPos(tr.pos), someTpe).setPos(tr.pos),
                Some("Map undefined at this index"),
                xt.ClassSelector(
                  xt.AsInstanceOf(xt.MapApply(l, r).setPos(tr.pos), someTpe).setPos(tr.pos),
                  getIdentifier(someSymbol.caseFieldAccessors.head)
                ).setPos(tr.pos)
              )

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "isDefinedAt" | "contains", Seq(rhs)) =>
              xt.Not(xt.Equals(
                xt.MapApply(extractTree(lhs), extractTree(rhs)).setPos(tr.pos),
                xt.ClassConstructor(
                  xt.ClassType(getIdentifier(noneSymbol).setPos(tr.pos), Seq(to)).setPos(tr.pos),
                  Seq()
                ).setPos(tr.pos)
              ).setPos(tr.pos))

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "updated" | "+", Seq(key, value)) =>
              xt.MapUpdated(
                extractTree(lhs), extractTree(key),
                xt.ClassConstructor(
                  xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                  Seq(extractTree(value))
                ).setPos(tr.pos)
              )

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "+", Seq(rhs)) =>
              val value = extractTree(rhs)
              xt.MapUpdated(
                extractTree(lhs), xt.TupleSelect(value, 1).setPos(tr.pos),
                xt.ClassConstructor(
                  xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                  Seq(xt.TupleSelect(value, 2).setPos(tr.pos))
                ).setPos(tr.pos)
              )

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "++", Seq(rhs)) =>
              extractTree(rhs) match {
                case xt.FiniteMap(pairs,  default, keyType, valueType) =>
                  pairs.foldLeft(extractTree(lhs)) { case (map, (k, v)) =>
                    xt.MapUpdated(map, k, v).setPos(tr.pos)
                  }

                case _ => outOfSubsetError(tr, "Can't extract map union with non-finite map")
              }

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "getOrElse", Seq(key, orElse)) =>
              xt.MethodInvocation(
                xt.MapApply(extractTree(lhs), extractTree(key)).setPos(tr.pos),
                getIdentifier(optionSymbol.tpe.member(TermName("getOrElse"))),
                Seq.empty,
                Seq(xt.Lambda(Seq(), extractTree(orElse)).setPos(tr.pos))
              )

            case (_, "unary_+", Seq()) => injectCast(e => e)(lhs)
            case (_, "-",   Seq(rhs)) => injectCasts(xt.Minus)(lhs, rhs)
            case (_, "*",   Seq(rhs)) => injectCasts(xt.Times)(lhs, rhs)
            case (_, "%",   Seq(rhs)) => injectCasts(xt.Remainder)(lhs, rhs)
            case (_, "mod", Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
            case (_, "/",   Seq(rhs)) => injectCasts(xt.Division)(lhs, rhs)
            case (_, ">",   Seq(rhs)) => injectCasts(xt.GreaterThan)(lhs, rhs)
            case (_, ">=",  Seq(rhs)) => injectCasts(xt.GreaterEquals)(lhs, rhs)
            case (_, "<",   Seq(rhs)) => injectCasts(xt.LessThan)(lhs, rhs)
            case (_, "<=",  Seq(rhs)) => injectCasts(xt.LessEquals)(lhs, rhs)

            case (xt.BVType(_), "|",   Seq(rhs)) => injectCasts(xt.BVOr)(lhs, rhs)
            case (xt.BVType(_), "&",   Seq(rhs)) => injectCasts(xt.BVAnd)(lhs, rhs)
            case (xt.BVType(_), "^",   Seq(rhs)) => injectCasts(xt.BVXor)(lhs, rhs)
            case (xt.BVType(_), "<<",  Seq(rhs)) => injectCastsForShift(xt.BVShiftLeft)(lhs, rhs)
            case (xt.BVType(_), ">>",  Seq(rhs)) => injectCastsForShift(xt.BVAShiftRight)(lhs, rhs)
            case (xt.BVType(_), ">>>", Seq(rhs)) => injectCastsForShift(xt.BVLShiftRight)(lhs, rhs)

            case (xt.BooleanType, "|", Seq(rhs)) => xt.BoolBitwiseOr(extractTree(lhs), extractTree(rhs))
            case (xt.BooleanType, "&", Seq(rhs)) => xt.BoolBitwiseAnd(extractTree(lhs), extractTree(rhs))
            case (xt.BooleanType, "^", Seq(rhs)) => xt.BoolBitwiseXor(extractTree(lhs), extractTree(rhs))

            case (_, "&&",  Seq(rhs)) => xt.And(extractTree(lhs), extractTree(rhs))
            case (_, "||",  Seq(rhs)) => xt.Or(extractTree(lhs), extractTree(rhs))

            case (tpe, "toByte", Seq()) => tpe match {
              case xt.BVType(8) => extractTree(lhs)
              case xt.BVType(16 | 32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(8))
              case tpe => outOfSubsetError(tr, s"Unexpected cast .toByte from $tpe")
            }

            case (tpe, "toShort", Seq()) => tpe match {
              case xt.BVType(8) => xt.BVWideningCast(extractTree(lhs), xt.BVType(16))
              case xt.BVType(16) => extractTree(lhs)
              case xt.BVType(32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(16))
              case tpe => outOfSubsetError(tr, s"Unexpected cast .toShort from $tpe")
            }

            case (tpe, "toInt", Seq()) => tpe match {
              case xt.BVType(8 | 16) => xt.BVWideningCast(extractTree(lhs), xt.BVType(32))
              case xt.BVType(32) => extractTree(lhs)
              case xt.BVType(64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(32))
              case tpe => outOfSubsetError(tr, s"Unexpected cast .toInt from $tpe")
            }

            case (tpe, "toLong", Seq()) => tpe match {
              case xt.BVType(8 | 16 | 32 ) => xt.BVWideningCast(extractTree(lhs), xt.BVType(64))
              case xt.BVType(64) => extractTree(lhs)
              case tpe => outOfSubsetError(tr, s"Unexpected cast .toLong from $tpe")
            }

            case (tpe, name, args) =>
              outOfSubsetError(tr, "Unknown call to " + name +
                s" on $lhs (${extractType(lhs)}) with arguments $args of type ${args.map(a => extractType(a))}")
          }
        }
      }

      // default behaviour is to complain :)
      case _ => outOfSubsetError(tr, "Could not extract " + tr + " (Scala tree of type "+tr.getClass+")")
    }).setPos(tr.pos)

    /** Inject implicit widening casts according to the Java semantics (5.6.2. Binary Numeric Promotion) */
    private def injectCasts(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                           (lhs0: Tree, rhs0: Tree)
                           (implicit dctx: DefContext): xt.Expr = {
      injectCastsImpl(ctor)(lhs0, rhs0, false)
    }

    /**
     *  Inject casts, special edition for shift operations.
     *
     *  NOTE In THEORY, the rhs needs to be promoted independently of lhs.
     *       In PRACTICE, Inox requires that both operands have the same type.
     *       [[CodeGeneration]] is applying a narrowing cast from Long to Int
     *       if needed. Here we add the opposite, and safe operation when lhs
     *       is a Long. We do not support shift operations when rhs is Long
     *       but lhs is a smaller BVType.
     */
    private def injectCastsForShift(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                                   (lhs0: Tree, rhs0: Tree)
                                   (implicit dctx: DefContext): xt.Expr = {
      injectCastsImpl(ctor)(lhs0, rhs0, true)
    }

    private def injectCastsImpl(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                               (lhs0: Tree, rhs0: Tree, shift: Boolean)
                               (implicit dctx: DefContext): xt.Expr = {
      def checkBits(tr: Tree, tpe: xt.Type) = tpe match {
        case xt.BVType(8 | 16 | 32 | 64) => // Byte, Short, Int or Long are ok
        case xt.BVType(s) => outOfSubsetError(tr, s"Unexpected integer of $s bits")
        case _ => // non-bitvector types are ok too
      }

      val lhs = extractTree(lhs0)
      val rhs = extractTree(rhs0)

      val ltpe = extractType(lhs0)
      checkBits(lhs0, ltpe)
      val rtpe = extractType(rhs0)
      checkBits(rhs0, rtpe)

      def id = { e: xt.Expr => e }
      def widen32 = { e: xt.Expr => xt.BVWideningCast(e, xt.BVType(32)) }
      def widen64 = { e: xt.Expr => xt.BVWideningCast(e, xt.BVType(64)) }

      val (lctor, rctor) = (ltpe, rtpe) match {
        case (xt.BVType(64), xt.BVType(64))          => (id, id)
        case (xt.BVType(64), xt.BVType(_))           => (id, widen64)
        case (xt.BVType(_),  xt.BVType(64)) if shift => outOfSubsetError(rhs0, s"Unsupported shift")
        case (xt.BVType(_),  xt.BVType(64))          => (widen64, id)
        case (xt.BVType(32), xt.BVType(32))          => (id, id)
        case (xt.BVType(32), xt.BVType(_))           => (id, widen32)
        case (xt.BVType(_),  xt.BVType(32))          => (widen32, id)
        case (xt.BVType(_),  xt.BVType(_))           => (widen32, widen32)

        case (xt.BVType(_), _) | (_, xt.BVType(_)) =>
          outOfSubsetError(lhs0, s"Unexpected combination of types: $ltpe and $rtpe")

        case (_, _) => (id, id)
      }

      ctor(lctor(lhs), rctor(rhs))
    }

    /** Inject implicit widening cast according to the Java semantics (5.6.1. Unary Numeric Promotion) */
    private def injectCast(ctor: xt.Expr => xt.Expr)(e0: Tree)(implicit dctx: DefContext): xt.Expr = {
      val e = extractTree(e0)
      val etpe = extractType(e0)

      val id = { e: xt.Expr => e }
      val widen32 = { e: xt.Expr => xt.BVWideningCast(e, xt.Int32Type) }

      val ector = etpe match {
        case xt.BVType(8 | 16) => widen32
        case xt.BVType(32 | 64) => id
        case xt.BVType(s) => outOfSubsetError(e0, s"Unexpected integer type of $s bits")
        case _ => id
      }

      ctor(ector(e))
    }

    private def extractType(t: Tree)(implicit dctx: DefContext): xt.Type = {
      extractType(t.tpe)(dctx, t.pos)
    }

    private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = (tpt match {
      case CharTpe    => xt.CharType
      case ByteTpe    => xt.Int8Type
      case ShortTpe   => xt.Int16Type
      case IntTpe     => xt.Int32Type
      case LongTpe    => xt.Int64Type
      case BooleanTpe => xt.BooleanType
      case UnitTpe    => xt.UnitType
      case AnyTpe     => xt.AnyType
      case NothingTpe => xt.NothingType

      case ct: ConstantType => extractType(ct.value.tpe)

      case TypeRef(_, sym, _) if isBigIntSym(sym) => xt.IntegerType
      case TypeRef(_, sym, _) if isRealSym(sym)   => xt.RealType
      case TypeRef(_, sym, _) if isStringSym(sym) => xt.StringType

      case TypeRef(_, sym, btt :: Nil) if isScalaSetSym(sym) =>
        outOfSubsetError(pos, "Scala's Set API is no longer extracted. Make sure you import leon.lang.Set that defines supported Set operations.")

      case TypeRef(_, sym, List(a,b)) if isScalaMapSym(sym) =>
        outOfSubsetError(pos, "Scala's Map API is no longer extracted. Make sure you import leon.lang.Map that defines supported Map operations.")

      case TypeRef(_, sym, btt :: Nil) if isSetSym(sym) =>
        xt.SetType(extractType(btt))

      case TypeRef(_, sym, btt :: Nil) if isBagSym(sym) =>
        xt.BagType(extractType(btt))

      case TypeRef(_, sym, List(ftt,ttt)) if isMapSym(sym) =>
        xt.MapType(extractType(ftt), xt.ClassType(getIdentifier(optionSymbol), Seq(extractType(ttt))).setPos(pos))

      case TypeRef(_, sym, tps) if isTuple(sym, tps.size) =>
        xt.TupleType(tps map extractType)

      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
        xt.ArrayType(extractType(btt))

      case TypeRef(_, sym, subs) if subs.size >= 1 && isFunction(sym, subs.size - 1) =>
        val from = subs.init
        val to   = subs.last
        xt.FunctionType(from map extractType, extractType(to))

      case TypeRef(_, sym, tps) if isByNameSym(sym) =>
        extractType(tps.head)

      case TypeRef(_, sym, _) if sym.isAbstractType =>
        if (dctx.tparams contains sym) {
          dctx.tparams(sym)
        } else {
          outOfSubsetError(pos, "Unknown type parameter "+sym)
        }

      case tr @ TypeRef(_, sym, tps) if sym.isClass =>
        xt.ClassType(getIdentifier(sym), tps.map(extractType))

      case tt: ThisType =>
        xt.ClassType(getIdentifier(tt.sym), tt.sym.typeParams.map(dctx.tparams))

      case SingleType(pre, sym) if sym.isModule =>
        xt.ClassType(getIdentifier(sym.moduleClass), Nil)

      case SingleType(_, sym) if sym.isTerm =>
        extractType(tpt.widen)

      case RefinedType(parents, defs) if defs.isEmpty =>
        /**
         * For cases like if(a) e1 else e2 where
         *   e1 <: C1,
         *   e2 <: C2,
         *   with C1,C2 <: C
         *
         * Scala might infer a type for C such as: Product with Serializable with C
         * we generalize to the first known type, e.g. C.
         */
        parents.filter(ptpe => !ignoreClasses(ptpe)).headOption.map(extractType) match {
          case Some(tpe) =>
            tpe

          case None =>
            outOfSubsetError(tpt.typeSymbol.pos, "Could not extract refined type: "+tpt+" ("+tpt.getClass+")")
        }

      case AnnotatedType(_, tpe) => extractType(tpe)

      case _ =>
        if (tpt ne null) {
          outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type: "+tpt+" ("+tpt.getClass+")")
        } else {
          outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
        }
    }).setPos(pos)
  }
}
