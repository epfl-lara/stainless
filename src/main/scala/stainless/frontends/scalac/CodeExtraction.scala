/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import stainless.ast.SymbolIdentifier
import inox.ast.{Identifier, FreshIdentifier}
import xlang.{trees => xt}

import scala.reflect.internal.util._
import scala.collection.mutable.{Map => MutableMap}

import scala.language.implicitConversions

trait CodeExtraction extends ASTExtractors {
  self: LeonExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import scala.collection.immutable.Set

  lazy val reporter = self.ctx.reporter

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

  /*
  def leonPosToScalaPos(spos: global.Position, p: LeonPosition): global.Position = {
    (spos, p) match {
      case (NoPosition, _) =>
        NoPosition

      case (p, dp: DefinedPosition) =>
        new OffsetPosition(p.source, dp.focusBegin.point)

      case _ =>
        NoPosition

    }
  }
  */

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(val pos: Position, msg: String, val ot: Option[Tree])
    extends Exception(msg)

  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }

  // Simple case classes to capture the representation of units/modules after discovering them.
  case class ScalaUnit(
    name : String,
    pack : PackageRef,
    imports : List[Import],
    defs : List[Tree],
    isPrintable : Boolean
  )

  class Extraction(units: List[CompilationUnit]) {

    private val symbolToIdentifier: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
    private def getIdentifier(sym: Symbol): SymbolIdentifier = symbolToIdentifier.get(sym) match {
      case Some(id) => id
      case None =>
        val name = sym.name.toString
        val id = SymbolIdentifier(if (name.endsWith("$")) name.init else name)
        symbolToIdentifier += sym -> id
        id
    }

    case class DefContext(
      tparams: Map[Symbol, xt.TypeParameter] = Map(),
      vars: Map[Symbol, () => xt.Variable] = Map(),
      mutableVars: Map[Symbol, () => xt.Variable] = Map(),
      localFuns: Map[Symbol, xt.LocalFunDef] = Map(),
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

      def withNewVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
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

      def withLocalFun(s: Symbol, lf: xt.LocalFunDef) = {
        copy(localFuns = this.localsFuns + (s -> lf))
      }
    }

    // This one never fails, on error, it returns Untyped
    def stainlessType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = {
      try {
        extractType(tpt)
      } catch {
        case e: ImpureCodeEncounteredException =>
          e.printStackTrace()
          Untyped
      }
    }

    private def isIgnored(s: Symbol) = {
      (annotationsOf(s) contains "ignore")
    }

    private def isLibrary(u: CompilationUnit) = Build.libFiles contains u.source.file.absolute.path

    private def extractStatic(stats: List[Tree]): (
      Seq[xtImport],
      Seq[Identifier],
      Seq[Identifier],
      Seq[xt.DefSet],
      Seq[xt.ClassDef],
      Seq[xt.FunDef]
    ) = {
      var imports   : Seq[xt.Import]  = Seq.empty
      var classes   : Seq[Identifier] = Seq.empty
      var functions : Seq[Identifier] = Seq.empty
      var subs      : Seq[xt.DefSet]  = Seq.empty

      var allClasses   : Seq[xt.ClassDef] = Seq.empty
      var allFunctions : Seq[xt.FunDef]   = Seq.empty

      for (d <- stats) d match {
        case EmptyTree =>
          // ignore

        case t if (annotationsOf(t.symbols) contains xt.Ignore) || (t.symbol is Synthetic) =>
          // ignore

        case i @ Import(_, _) =>
          imports ++= extractImports(i)

        case td @ ExObjectDef() =>
          val (obj, newClasses, newFunctions) = extractObject(td)
          subs :+= obj
          allClasses ++= newClasses
          allFunctions ++= newFunctions

        case cd @ ExClassDef() =>
          val (xcd, newFunctions) = extractClass(cd)
          classes :+= xcd.id
          allClasses :+= xcd
          allFunctions ++= newFunctions

        case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
          val fd = extractFunction(fsym, tparams, vparams, rhs)(DefContext(), dd.pos)
          functions :+= fd.id
          allFunctions :+= fd

        case t @ ExFieldDef(fsym, _, rhs) =>
          val fd = extractFunction(fsym, Seq(), Seq(), rhs)(DefContext(), t.pos)
          functions :+= fd.id
          allFunctions :+= fd

        case t @ ExLazyFieldDef(fsym, _, rhs) =>
          val fd = extractFunction(fsym, Seq(), Seq(), rhs)(DefContext(), t.pos)
          functions :+= fd.id
          allFunctions :+= fd

        case pd @ PackageDef(_, _) =>
          val (pkg, newClasses, newFunctions) = extractPackage(pd)
          subs :+= pkg
          allClasses ++= newClauses
          allFunctions ++= newFunctions

        case other =>
          reporter.warning(other.pos, "Could not extract tree in static container: " + other)
      }

      (imports, classes, functions, subs, allClasses, allFunctions)
    }

    def extractPackage(pd: PackageDef): (xt.PackageDef, Seq[xt.ClassDef], Seq[xt.FunDef]) = {
      val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(pd.stats)
      assert(functions.isEmpty, "Packages shouldn't contain functions")

      val pkg = xt.PackageDef(
        getIdentifier(pd.symbol),
        imports,
        classes,
        subs
      ).setPos(pd.pos)

      (pkg, allClasses, allFunctions)
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
      ).setPos(td.pos)

      (module, allClasses, allFunctions)
    }

    private val invSymbol = stainless.ast.Symbol("inv")

    private def extractClass(cd: ClassDef): (xt.ClassDef, Seq[xt.FunDef]) = {
      val sym = cd.symbol
      val id = getIdentifier(sym)

      val tparamsMap = sym.tpe match {
        case TypeRef(_, _, tps) => extractTypeParams(tps)
        case _ => Nil
      }

      val parent = sym.tpe.parents.headOption match {
        case Some(tpe) if tpe.typeSymbol == defn.ObjectClass => None
        case Some(TypeRef(_, parentSym, tps)) => Some(getIdentifier(parentSym))
        case _ => None
      }

      val tparams = tparamsMap.map(t => xt.TypeParameterDef(t._2))
      val tpCtx = DefContext((tparamsMap.map(_._1) zip tparams.map(_.tp)).toMap)

      val flags = annotationsOf(sym) ++ (if (sym.isAbstractClass) Some(xt.IsAbstract) else None)

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
        val tpe = stainlessType(vd.tpe)(tpCtx, vd.pos)
        val id = freshId(vd.symbol)
        if (vd.symbol.isMutable) xt.VarDef(id, tpe).setPos(sym.pos)
        else xt.ValDef(id, tpe).setPos(sym.pos)
      }

      val defCtx = tpCtx.withNewVars((symbols zip fields.map(vd => () => vd.toVariable)).toMap)

      var invariants: Seq[xt.Expr] = Seq.empty
      var methods: Seq[xt.FunDef] = Seq.empty

      for (d <- cd.impl.body) d match {
        case EmptyTree =>
          // ignore

        case t if (annotationsOf(t.symbol) contains xt.Ignore) || (t.symbol.isSynthetic) =>
          // ignore

        case ExRequiredExpression(body) =>
          invariants :+= extractTree(body)(defCtx)

        case dd @ DefDef(name, _, _, _, _) if dd.symbol.name.toString.startsWith("copy$default$") =>
          // @nv: FIXME - think about handling default value functions

        case t @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
          methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx, t.pos)

        case t @ ExFieldDef(fsym, _, rhs) =>
          methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)

        case t @ ExLazyFieldDef(fsym, _, rhs) =>
          methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)

        case other =>
          reporter.warning(other.pos, "Could not extract tree in class: " + other)
      }

      val optInv = if (invariants.isEmpty) None else Some(
        new xt.FunDef(SymbolIdentifier(invSymbol), Seq.empty, Seq.empty, xt.BooleanType,
          if (invariants.size == 1) invariants.head else xt.And(invariants),
          Set(xt.IsInvariant)
        )
      )

      val allMethods = methods ++ optInv

      val cd = new xt.ClassDef(
        id,
        tparams,
        parent,
        fields,
        allMethods.map(_.id.asInstanceOf[SymbolIdentifier]),
        flags
      ).setPos(sym.pos)

      (cd, allMethods)
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

    private def extractPackageRef(refPath: RefTree): PackageRef = {
      (getSelectChain(refPath.qualifier) :+ refPath.name.toString).filter(_ != "<empty>")
    }

    private def extractImports(i: Import, current: UnitDef): Seq[xt.Import] = {
      val Import(expr, sels) = i
      import DefOps._

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

    private def extractFunction(sym: Symbol, rhs: Tree)(implicit dctx: DefContext): FunDef = {
      // Type params of the function itself
      val tparams = extractTypeParams(sym.typeParams.map(_.tpe))

      val nctx = dctx.copy(tparams = dctx.tparams ++ tparams.toMap)

      val newParams = sym.info.paramss.flatten.map { sym =>
        val ptpe = stainlessType(sym.tpe)(nctx, sym.pos)
        val tpe = if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe) else ptpe
        xt.ValDef(FreshIdentifier(sym.name.toString).setPos(sym.pos), tpe).setPos(sym.pos)
      }

      val tparamsDef = tparams.map(t => xt.TypeParameterDef(t._2))

      val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

      val id = getIdentifier(sym)

      var flags = annotationsOf(sym).toSet ++ (if (sym.isImplicit) Some(xt.Inline) else None)

      val body =
        if (!(flags contains xt.IsField(true))) rhs
        else rhs match {
          case Block(List(Assign(_, realBody)), _) => realBody
          case _ => outOfSubsetError(rhs, "Wrong form of lazy accessor")
        }

      val fctx = nctx.withNewVars((sym.info.paramss.flatten zip newParams.map(vd => () => vd.toVariable)).toMap)

      val finalBody = if (rhs == EmptyTree) {
        flags += xt.IsAbstract
        xt.NoTree(returnType)
      } else try {
        xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
      } catch {
        case e: ImpureCodeEncounteredException =>
          reporter.error(e.pos, e.getMessage)
          e.printStackTrace()

          flags += xt.IsAbstract
          xt.NoTree(returnType)
      }

      val fullBody = if (fctx.isExtern) {
        xt.exprOps.withBody(finalBody, xt.NoTree(returnType).setPos(body.pos))
      } else {
        finalBody
      }

      new xt.FunDef(
        id,
        tparamsDef,
        newParams,
        returnType,
        fullBody,
        flags
      ).setPos(sym.pos)
    }

    private def extractTypeParams(tps: Seq[Type]): Seq[(Symbol, xt.TypeParameter)] = tps.flatMap {
      case TypeRef(_, sym, Nil) =>
        Some(sym -> xt.TypeParameter.fresh(sym.name.toString))
      case t =>
        outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
        None
    }

    private def extractPattern(p: Tree, binder: Option[xt.ValDef] = None)(implicit dctx: DefContext): (xt.Pattern, DefContext) = p match {
      case b @ Bind(name, t @ Typed(pat, tpt)) =>
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
        extractPattern(t, Some(vd))(pctx)

      case b @ Bind(name, pat) =>
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(b)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
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
            (xt.ADTPattern(binder, ct, Seq()).setPos(p.pos), dctx)
          case _ =>
            outOfSubsetError(s, "Invalid type "+s.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) =>
        extractType(a) match {
          case ct: xt.ClassType =>
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
            val nctx = subDctx.foldLeft(dctx)(_ union _)
            (xt.ADTPattern(binder, ct, subPatterns).setPos(p.pos), nctx)

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

      case ExInt32Literal(i)   => (xt.LiteralPattern(binder, xt.IntLiteral(i)),     dctx)
      case ExBooleanLiteral(b) => (xt.LiteralPattern(binder, xt.BooleanLiteral(b)), dctx)
      case ExUnitLiteral()     => (xt.LiteralPattern(binder, xt.UnitLiteral()),     dctx)
      case ExStringLiteral(s)  => (xt.LiteralPattern(binder, xt.StringLiteral(s)),  dctx)

      case up @ ExUnapplyPattern(s, args) =>
        val (sub, ctx) = args.map (extractPattern(_)).unzip
        val nctx = ctx.foldLeft(dctx)(_ union _)
        val id = getIdentifier(s.symbol)

        // TODO: get types!

        (UnapplyPattern(binder, id, Seq.empty, sub).setPos(up.pos), ctx.foldLeft(dctx)(_ union _))

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

    private def extractBlock(es: List[Tree])(implicit dctx: DefContext): xt.Expr = es match {
      case Nil => xt.UnitLiteral()

      case e @ ExAssert(contract, oerr) :: xs =>
        val const = extractTree(contract)
        val b     = extractBlock(xs)
        xt.Assert(const, oerr, b).setPos(e)

      case e @ ExRequiredExpression(contract) :: xs =>
        val pre = extractTree(contract)
        val b   = extractBlock(xs)
        xt.Require(pre, b).setPos(e)

      case v @ ValDef(name, tpt, _) :: xs =>
        val vd = if (!v.symbol.isMutable) {
          vt.ValDef(FreshIdentifier(name.toString), extractType(tpt)).setPos(v.pos)
        } else {
          xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)).setPos(v.pos)
        }

        val restTree = extractBlocks(xs) {
          if (!v.symbol.isMutable) {
            dctx.withNewVar(v.symbol -> (() => vd.toVariable))
          } else {
            dctx.withNewMutableVar(v.symbol -> (() => vd.toVariable))
          }
        }

        xt.Let(vd, extractTree(v.rhs), restTree).setPos(v.getPos)

      case d @ ExFunctionDef(sym, tparams, params, ret, b) :: xs =>
        val fd = extractFunction(sym, tparams, params, b)(dctx, d.pos)
        val letRec = xt.LocalFunDef(
          xt.ValDef(fd.id, extractType(ret)(dctx, d.pos)),
          fd.tparams,
          xt.Lambda(fd.params, fd.fullBody)
        )
        extractBlock(xs)(dctx.withLocalFun(sym, letRec)) match {
          case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body)
          case other => xt.LetRec(Seq(letRec), other)
        }

      case x :: Nil =>
        extractTree(x)

      case x :: _ =>
        outOfSubsetError(x, "Unexpected head of block")
    }

    private def extractTree(tr: Tree)(implicit dctx: DefContext): xt.Expr = (tr match {
      case Block(es, e) =>
        val b = extractBlock(es :+ e)
        xt.exprOps.flattenBlocks(b)

      case ExEnsuredExpression(body, contract) =>
        val post = extractTree(contract)
        val b = extractTreeOrNoTree(body)
        val tpe = extractType(body)

        val closure = post match {
          case l: Lambda => l
          case other =>
            val vd = xt.ValDef(FreshIdentifier("res"), tpe).setPos(post)
            Lambda(Seq(vd), xt.Application(other, Seq(vd.toVariable))).setPos(post)
        }

        xt.Ensuring(b, closure)

      case t @ ExHoldsWithProofExpression(body, ExMaybeBecauseExpressionWrapper(proof)) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType).setPos(current.pos)
        val p = extractTreeOrNoTree(proof)
        val post = xt.Lambda(Seq(vd), xt.And(Seq(p, vd.toVariable))).setPos(current.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      case t @ ExHoldsExpression(body) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType).setPos(current.pos)
        val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(current.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      // If the because statement encompasses a holds statement
      case t @ ExBecauseExpression(ExHoldsExpression(body), proof) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), BooleanType).setPos(current.pos)
        val p = extractTreeOrNoTree(proof)
        val post = xt.Lambda(Seq(vd), xt.And(Seq(p, vd.toVariable))).setPos(current.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      case t @ ExComputesExpression(body, expected) =>
        val b = extractTreeOrNoTree(body).setPos(body.pos)
        val expectedExpr = extractTreeOrNoTree(expected).setPos(expected.pos)
        val vd = xt.ValDef(FreshIdentifier("res"), extractType(body)).setPos(current.pos)
        val post = xt.Lambda(Seq(vd), xt.Equals(vd.toVariable, expectedExpr)).setPos(current.pos)
        xt.Ensuring(b, post)

      case t @ ExBigLengthExpression(input) =>
        xt.StringLength(extractTreeOrNoTree(input))

      case t @ ExBigSubstringExpression(input, start) =>
        val in = extractTreeOrNoTree(input)
        val st = extractTreeOrNoTree(start)
        val vd = xt.ValDef(FreshIdentifier("s", true), xt.StringType)
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
          case xt.IntLiteral(n) => xt.IntegerLiteral(BigInt(n))
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

      case ExInt32Literal(v) => xt.IntLiteral(v)
      case ExBooleanLiteral(v) => xt.BooleanLiteral(v)
      case ExUnitLiteral() => xt.UnitLiteral()
      case ExCharLiteral(c) => xt.CharLiteral(c)
      case ExStringLiteral(s) => xt.StringLiteral(s)

      case ExLocally(body) => xt.extractTree(body)

      case ExTyped(e, _) =>
        // TODO: refine type here?
        extractTree(e)

      case ex @ ExIdentifier(sym, tpt) =>
        dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
          case Some(builder) => builder().setPos(ex.pos)
          case None => dctx.localFuns.get(sym) match {
            case Some(f) => xt.ApplyLetRec(f.name.toVariable, f.tparams, args map extractTree)
            case None => xt.FunctionInvocation(getIdentifier(sym), Seq.empty, Seq.empty)
          }
        }

      case hole @ ExHoleExpression(tpt, exprs) =>
        xt.Hole(extractType(tpt), exprs.map(extractTree))

      case chs @ ExChooseExpression(body) =>
        xt.Choose(extractTree(body))

      case l @ ExLambdaExpression(args, body) =>
        val vds = args map(vd => xt.ValDef(
          FreshIdentifier(vd.symbol.name.toString),
          extractType(vd.tpt)
        ).setPos(vd.pos))

        val newVars = (args zip vds).map { case (vd, lvd) =>
          vd.symbol -> (() => lvd.toVariable)
        }

        val exBody = extractTree(body)(dctx.withNewVars(newVars))
        xt.Lambda(vds, exBody)

      case ExForallExpression(args, body) =>
        val vds = args map { case (tpt, sym) =>
          xt.ValDef(FreshIdentifier(sym.name.toString), extractType(tpt)).setPos(sym.pos)
        }

        val newVars = (args zip vds).map { case ((_, sym), lvd) =>
          sym -> (() => lvd.toVariable)
        }

        val exBody = extractTree(body)(dctx.withNewVars(newVars))
        xt.Forall(vds, exBody)

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

        xt.FiniteMap(somePairs, dflt, extractType(tptFrom))

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

      case ExCaseClassConstruction(tpt, args) =>
        extractType(tpt) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, args.map(extractTree))
          case _ => outOfSubsetError(tr, "Construction of a non-class type.")
        }

      case ExNot(e)        => xt.Not(extractTree(e))
      case ExUMinus(e)     => xt.UMinus(extractTree(e))
      case ExBVNot(e)      => xt.BVNot(extractTree(e))

      case ExNotEquals(l, r) =>
        xt.Not(xt.Equals(extractTree(l), extractTree(r)).setPos(tr.pos))

      case ExEquals(l, r) =>
        xt.Equals(extractTree(l), extractTree(r))

      case ExArrayFill(baseType, length, defaultValue) =>
        val lengthRec = extractTree(length)
        val defaultValueRec = extractTree(defaultValue)
        xt.LargeArray(Map.empty, extractTree(defaultValue), extractTree(length))

      case ExIfThenElse(t1,t2,t3) =>
        xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

      case ExAsInstanceOf(expr, tt) =>
        extractType(tt) match {
          case ct: xt.ClassType => xt.AsInstanceOf(extractTree(expr), ct)
          case _ => outOfSubsetError(tr, "asInstanceOf can only cast to class types")
        }

      case ExIsInstanceOf(tt, cc) =>
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
          case ct: ClassType => xt.This(ct)
          case _ => outOfSubsetError(t, "Invalid usage of `this`")
        }

      case aup @ ExArrayUpdated(ar, k, v) =>
        xt.ArrayUpdated(extractTree(ar), extractTree(k), extractTree(v))

      case l @ ExListLiteral(tpe, elems) =>
        val rtpe = extractType(tpe)
        val cons = xt.ADTType(libraryCaseClass(l.pos, "leon.collection.Cons"), Seq(rtpe))
        val nil  = xt.ADTType(libraryCaseClass(l.pos, "leon.collection.Nil"),  Seq(rtpe))

        elems.foldRight(xt.ADT(nil, Seq())) {
          case (e, ls) => xt.ADT(cons, Seq(extractTree(e), ls))
        }

      case ExImplies(lhs, rhs) =>
        xt.Implies(extractTree(lhs), extractTree(rhs))

      case c @ ExCall(rec, sym, tps, args) => rec match {
        case None =>
          dctx.localFuns.get(sym) match {
            case None =>
              xt.FunctionInvocation(getIdentifier(sym), tps.map(extractType), args.map(extractTree))
            case Some(f) =>
              xt.ApplyLetRec(f.name.toVariable, f.tparams, f.args.map(extractTree))
          }

        case Some(lhs) => extractType(lhs) match {
          case ct: xt.ClassType =>
            if (sym.isMethod) xt.MethodInvocation(
              extractTree(lhs),
              getIdentifier(sym),
              tps.map(extractType),
              args.map(extractTree)
            ) else args match {
              case Seq() => xt.ClassSelector(extractTree(lhs), getIdentifier(sym))
              case Seq(rhs) => xt.FieldAssignment(extractTree(lhs), getIdentifier(sym), extractTree(rhs))
              case _ => outOfSubsetError(tr, "Unexpected call")
            }

          case ft: xt.FunctionType =>
            xt.Application(extractTree(lhs), args.map(extractTree))

          case tpe => (tpe, sym.name.decode.toString, args) match {
            case (xt.StringType, "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
            case (xt.IntegerType | xt.BVType(_) | xt.RealType, "+", Seq(rhs)) => xt.Plus(extractTree(lhs), extractTree(rhs))

            case xt.SetType()

          }
        }

        (rrec, sym.name.decoded, rargs) match {
          case (null, _, args) =>
            val (fd, convertArgs) = getFunDef(sym, c.pos, allowFreeArgs=true)
            val newTps = tps.map(t => extractType(t))
            val tfd = fd.typed(newTps)

            FunctionInvocation(tfd, convertArgs(tfd, args))

          case (IsTyped(rec, ct: ClassType), methodName, args) if isMethod(sym) || ignoredMethods(sym) =>
            val (fd, convertArgs) = getFunDef(sym, c.pos)
            val cd = methodToClass(fd)

            val newTps = tps.map(t => extractType(t))
            val tfd = fd.typed(newTps)

            MethodInvocation(rec, cd, tfd, convertArgs(tfd, args))

          case (IsTyped(rec, ft: FunctionType), _, args) =>
            application(rec, args)

          case (IsTyped(rec, cct: CaseClassType), name, Nil) if cct.classDef.fields.exists(_.id.name == name) =>
            val fieldID = cct.classDef.fields.find(_.id.name == name).get.id

            caseClassSelector(cct, rec, fieldID)

          //mutable variables
          case (IsTyped(rec, cct: CaseClassType), name, List(e1)) if isMutator(sym) =>
            val id = cct.classDef.fields.find(_.id.name == name.dropRight(2)).get.id
            FieldAssignment(rec, id, e1)


          //String methods
          case (IsTyped(a1, StringType), "toString", List()) =>
            a1
          case (IsTyped(a1, WithStringconverter(converter)), "toString", List()) =>
            converter(a1)
          case (IsTyped(a1, StringType), "+", List(IsTyped(a2, StringType))) =>
            StringConcat(a1, a2)
          case (IsTyped(a1, StringType), "+", List(IsTyped(a2, WithStringconverter(converter)))) =>
            StringConcat(a1, converter(a2))
          case (IsTyped(a1, WithStringconverter(converter)), "+", List(IsTyped(a2, StringType))) =>
            StringConcat(converter(a1), a2)
          case (IsTyped(a1, StringType), "length", List()) =>
            StringLength(a1)
          case (IsTyped(a1, StringType), "substring", List(IsTyped(start, Int32Type))) =>
            val s = FreshIdentifier("s", StringType)
            let(s, a1,
            SubString(Variable(s), start, StringLength(Variable(s)))
            )
          case (IsTyped(a1, StringType), "substring", List(IsTyped(start, Int32Type), IsTyped(end, Int32Type))) =>
            SubString(a1, start, end)
          
          //BigInt methods
          case (IsTyped(a1, IntegerType), "+", List(IsTyped(a2, IntegerType))) =>
            Plus(a1, a2)
          case (IsTyped(a1, IntegerType), "-", List(IsTyped(a2, IntegerType))) =>
            Minus(a1, a2)
          case (IsTyped(a1, IntegerType), "*", List(IsTyped(a2, IntegerType))) =>
            Times(a1, a2)
          case (IsTyped(a1, IntegerType), "%", List(IsTyped(a2, IntegerType))) =>
            Remainder(a1, a2)
          case (IsTyped(a1, IntegerType), "mod", List(IsTyped(a2, IntegerType))) =>
            Modulo(a1, a2)
          case (IsTyped(a1, IntegerType), "/", List(IsTyped(a2, IntegerType))) =>
            Division(a1, a2)
          case (IsTyped(a1, IntegerType), ">", List(IsTyped(a2, IntegerType))) =>
            GreaterThan(a1, a2)
          case (IsTyped(a1, IntegerType), ">=", List(IsTyped(a2, IntegerType))) =>
            GreaterEquals(a1, a2)
          case (IsTyped(a1, IntegerType), "<", List(IsTyped(a2, IntegerType))) =>
            LessThan(a1, a2)
          case (IsTyped(a1, IntegerType), "<=", List(IsTyped(a2, IntegerType))) =>
            LessEquals(a1, a2)


          //Real methods
          case (IsTyped(a1, RealType), "+", List(IsTyped(a2, RealType))) =>
            RealPlus(a1, a2)
          case (IsTyped(a1, RealType), "-", List(IsTyped(a2, RealType))) =>
            RealMinus(a1, a2)
          case (IsTyped(a1, RealType), "*", List(IsTyped(a2, RealType))) =>
            RealTimes(a1, a2)
          case (IsTyped(a1, RealType), "/", List(IsTyped(a2, RealType))) =>
            RealDivision(a1, a2)
          case (IsTyped(a1, RealType), ">", List(IsTyped(a2, RealType))) =>
            GreaterThan(a1, a2)
          case (IsTyped(a1, RealType), ">=", List(IsTyped(a2, RealType))) =>
            GreaterEquals(a1, a2)
          case (IsTyped(a1, RealType), "<", List(IsTyped(a2, RealType))) =>
            LessThan(a1, a2)
          case (IsTyped(a1, RealType), "<=", List(IsTyped(a2, RealType))) =>
            LessEquals(a1, a2)


          // Int methods
          case (IsTyped(a1, Int32Type), "+", List(IsTyped(a2, Int32Type))) =>
            BVPlus(a1, a2)
          case (IsTyped(a1, Int32Type), "-", List(IsTyped(a2, Int32Type))) =>
            BVMinus(a1, a2)
          case (IsTyped(a1, Int32Type), "*", List(IsTyped(a2, Int32Type))) =>
            BVTimes(a1, a2)
          case (IsTyped(a1, Int32Type), "%", List(IsTyped(a2, Int32Type))) =>
            BVRemainder(a1, a2)
          case (IsTyped(a1, Int32Type), "/", List(IsTyped(a2, Int32Type))) =>
            BVDivision(a1, a2)

          case (IsTyped(a1, Int32Type), "|", List(IsTyped(a2, Int32Type))) =>
            BVOr(a1, a2)
          case (IsTyped(a1, Int32Type), "&", List(IsTyped(a2, Int32Type))) =>
            BVAnd(a1, a2)
          case (IsTyped(a1, Int32Type), "^", List(IsTyped(a2, Int32Type))) =>
            BVXOr(a1, a2)
          case (IsTyped(a1, Int32Type), "<<", List(IsTyped(a2, Int32Type))) =>
            BVShiftLeft(a1, a2)
          case (IsTyped(a1, Int32Type), ">>", List(IsTyped(a2, Int32Type))) =>
            BVAShiftRight(a1, a2)
          case (IsTyped(a1, Int32Type), ">>>", List(IsTyped(a2, Int32Type))) =>
            BVLShiftRight(a1, a2)

          case (IsTyped(a1, Int32Type), ">", List(IsTyped(a2, Int32Type))) =>
            GreaterThan(a1, a2)
          case (IsTyped(a1, Int32Type), ">=", List(IsTyped(a2, Int32Type))) =>
            GreaterEquals(a1, a2)
          case (IsTyped(a1, Int32Type), "<", List(IsTyped(a2, Int32Type))) =>
            LessThan(a1, a2)
          case (IsTyped(a1, Int32Type), "<=", List(IsTyped(a2, Int32Type))) =>
            LessEquals(a1, a2)


          // Boolean methods
          case (IsTyped(a1, BooleanType), "&&", List(IsTyped(a2, BooleanType))) =>
            and(a1, a2)

          case (IsTyped(a1, BooleanType), "||", List(IsTyped(a2, BooleanType))) =>
            or(a1, a2)


          // Set methods
          case (IsTyped(a1, SetType(b1)), "size", Nil) =>
            SetCardinality(a1)

          //case (IsTyped(a1, SetType(b1)), "min", Nil) =>
          //  SetMin(a1)

          //case (IsTyped(a1, SetType(b1)), "max", Nil) =>
          //  SetMax(a1)

          case (IsTyped(a1, SetType(b1)), "+", List(a2)) =>
            SetAdd(a1, a2)

          case (IsTyped(a1, SetType(b1)), "++", List(IsTyped(a2, SetType(b2))))  if b1 == b2 =>
            SetUnion(a1, a2)

          case (IsTyped(a1, SetType(b1)), "&", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
            SetIntersection(a1, a2)

          case (IsTyped(a1, SetType(b1)), "subsetOf", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
            SubsetOf(a1, a2)

          case (IsTyped(a1, SetType(b1)), "--", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
            SetDifference(a1, a2)

          case (IsTyped(a1, SetType(b1)), "contains", List(a2)) =>
            ElementOfSet(a2, a1)

          case (IsTyped(a1, SetType(b1)), "isEmpty", List()) =>
            Equals(a1, FiniteSet(Set(), b1))


          // Bag methods
          case (IsTyped(a1, BagType(b1)), "+", List(a2)) =>
            BagAdd(a1, a2)

          case (IsTyped(a1, BagType(b1)), "++", List(IsTyped(a2, BagType(b2)))) if b1 == b2 =>
            BagUnion(a1, a2)

          case (IsTyped(a1, BagType(b1)), "&", List(IsTyped(a2, BagType(b2)))) if b1 == b2 =>
            BagIntersection(a1, a2)

          case (IsTyped(a1, BagType(b1)), "--", List(IsTyped(a2, BagType(b2)))) if b1 == b2 =>
            BagDifference(a1, a2)

          case (IsTyped(a1, BagType(b1)), "get", List(a2)) =>
            MultiplicityInBag(a2, a1)

          case (IsTyped(a1, BagType(b1)), "isEmpty", List()) =>
            Equals(a1, FiniteBag(Map(), b1))


          // Array methods
          case (IsTyped(a1, ArrayType(vt)), "apply", List(a2)) =>
            ArraySelect(a1, a2)

          case (IsTyped(a1, at: ArrayType), "length", Nil) =>
            ArrayLength(a1)

          case (IsTyped(a1, at: ArrayType), "updated", List(k, v)) =>
            ArrayUpdated(a1, k, v)

          case (IsTyped(a1, at: ArrayType), "clone", Nil) =>
            a1

          // Map methods
          case (IsTyped(a1, MapType(_, vt)), "apply", List(a2)) =>
            MapApply(a1, a2)

          case (IsTyped(a1, MapType(_, vt)), "get", List(a2)) =>
            val someClass = CaseClassType(libraryCaseClass(sym.pos, "leon.lang.Some"), Seq(vt))
            val noneClass = CaseClassType(libraryCaseClass(sym.pos, "leon.lang.None"), Seq(vt))

            IfExpr(MapIsDefinedAt(a1, a2).setPos(current.pos),
              CaseClass(someClass, Seq(MapApply(a1, a2).setPos(current.pos))).setPos(current.pos),
              CaseClass(noneClass, Seq()).setPos(current.pos))

          case (IsTyped(a1, MapType(_, vt)), "getOrElse", List(a2, a3)) =>
            IfExpr(MapIsDefinedAt(a1, a2).setPos(current.pos),
              MapApply(a1, a2).setPos(current.pos),
              a3)

          case (IsTyped(a1, mt: MapType), "isDefinedAt", List(a2)) =>
            MapIsDefinedAt(a1, a2)

          case (IsTyped(a1, mt: MapType), "contains", List(a2)) =>
            MapIsDefinedAt(a1, a2)

          case (IsTyped(a1, mt: MapType), "updated", List(k, v)) =>
            MapUnion(a1, FiniteMap(Map(k -> v), mt.from, mt.to))

          case (IsTyped(a1, mt: MapType), "+", List(k, v)) =>
            MapUnion(a1, FiniteMap(Map(k -> v), mt.from, mt.to))

          case (IsTyped(a1, mt: MapType), "+", List(IsTyped(kv, TupleType(List(_, _))))) =>
            kv match {
              case Tuple(List(k, v)) =>
                MapUnion(a1, FiniteMap(Map(k -> v), mt.from, mt.to))
              case kv =>
                MapUnion(a1, FiniteMap(Map(TupleSelect(kv, 1) -> TupleSelect(kv, 2)), mt.from, mt.to))
            }

          case (IsTyped(a1, mt1: MapType), "++", List(IsTyped(a2, mt2: MapType)))  if mt1 == mt2 =>
            MapUnion(a1, a2)

          // Char operations
          case (IsTyped(a1, CharType), ">", List(IsTyped(a2, CharType))) =>
            GreaterThan(a1, a2)

          case (IsTyped(a1, CharType), ">=", List(IsTyped(a2, CharType))) =>
            GreaterEquals(a1, a2)

          case (IsTyped(a1, CharType), "<", List(IsTyped(a2, CharType))) =>
            LessThan(a1, a2)

          case (IsTyped(a1, CharType), "<=", List(IsTyped(a2, CharType))) =>
            LessEquals(a1, a2)

          case (a1, name, a2) =>
            val typea1 = a1.getType
            val typea2 = a2.map(_.getType).mkString(",")
            val sa2 = a2.mkString(",")
            outOfSubsetError(tr, "Unknown call to " + name + s" on $a1 ($typea1) with arguments $sa2 of type $typea2")
        }

      // default behaviour is to complain :)
      case _ =>
        outOfSubsetError(tr, "Could not extract as PureScala (Scala tree of type "+tr.getClass+")")
    }).setPos(tr)

    private def extractType(t: Tree)(implicit dctx: DefContext): xt.Type = {
      extractType(t.tpe)(dctx, t.pos)
    }

    private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = tpt match {
      case tpe if tpe == CharClass.tpe    => xt.CharType
      case tpe if tpe == IntClass.tpe     => xt.Int32Type
      case tpe if tpe == BooleanClass.tpe => xt.BooleanType
      case tpe if tpe == UnitClass.tpe    => xt.UnitType
      case tpe if tpe == NothingClass.tpe => xt.Untyped

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
        xt.MapType(extractType(ftt), extractType(ttt))

      case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2)))

      case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3)))

      case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4)))

      case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4),extractType(t5)))

      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
        xt.ArrayType(extractType(btt))

      case TypeRef(_, sym, subs) if subs.size >= 1 && isFunction(sym, subs.size - 1) =>
        val from = subs.init
        val to   = subs.last
        xt.FunctionType(from map extractType, extractType(to))

      case TypeRef(_, sym, tps) if isByNameSym(sym) =>
        extractType(tps.head)

      case tr @ TypeRef(_, sym, tps) =>
        val leontps = tps.map(extractType)

        if (sym.isAbstractType) {
          if(dctx.tparams contains sym) {
            dctx.tparams(sym)
          } else {
            outOfSubsetError(pos, "Unknown type parameter "+sym)
          }
        } else {
          getClassType(sym, leontps)
        }

      case tt: ThisType =>
        val cd = getClassDef(tt.sym, pos)
        cd.typed // Typed using own's type parameters

      case SingleType(_, sym) =>
        getClassType(sym.moduleClass, Nil)

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
        parents.flatMap { ptpe =>
          try {
            Some(extractType(ptpe))
          } catch {
            case e: ImpureCodeEncounteredException =>
              None
        }}.headOption match {
          case Some(tpe) =>
            tpe

          case None =>
            outOfSubsetError(tpt.typeSymbol.pos, "Could not extract refined type as PureScala: "+tpt+" ("+tpt.getClass+")")
        }

      case AnnotatedType(_, tpe) => extractType(tpe)

      case _ =>
        if (tpt ne null) {
          outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type as PureScala: "+tpt+" ("+tpt.getClass+")")
        } else {
          outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
        }
    }
  }
}
