/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._
import util.Positions._

import stainless.ast.SymbolIdentifier
import extraction.xlang.{trees => xt}

import scala.language.implicitConversions

class CodeExtraction(inoxCtx: inox.Context, symbols: SymbolsContext)(implicit val ctx: Context)
  extends ASTExtractors {

  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  lazy val reporter = inoxCtx.reporter
  implicit val debugSection = DebugSectionExtraction

  implicit def dottyPosToInoxPos(p: Position): inox.utils.Position = {
    if (!p.exists) {
      inox.utils.NoPosition
    } else if (p.start != p.end) {
      val start = ctx.source.atPos(p.startPos)
      val end   = ctx.source.atPos(p.endPos)
      inox.utils.RangePosition(start.line + 1, start.column + 1, start.point,
                               end.line + 1, end.column + 1, end.point,
                               ctx.source.file.file)
    } else {
      val sp = ctx.source.atPos(p)
      inox.utils.OffsetPosition(sp.line + 1, sp.column + 1, sp.point,
                                ctx.source.file.file)
    }
  }

  private def annotationsOf(sym: Symbol, ignoreOwner: Boolean = false): Set[xt.Flag] = {
    val actualSymbol = sym // .accessedOrSelf
    (for {
      a <- actualSymbol.annotations ++ (if (!ignoreOwner) actualSymbol.owner.annotations else Set.empty)
      name = a.symbol.fullName.toString.replaceAll("\\.package\\$\\.", ".")
      if name startsWith "stainless.annotation."
      shortName = name drop "stainless.annotation.".length
    } yield {
      xt.extractFlag(shortName, a.arguments.map(extractTree(_)(DefContext())))
    }).toSet
  }

  /** An exception thrown when non-stainless compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(val pos: Position, msg: String, val ot: Option[tpd.Tree])
    extends Exception(msg)

  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: tpd.Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }

  private case class DefContext(
    tparams: Map[Symbol, xt.TypeParameter] = Map(),
    vars: Map[Symbol, () => xt.Expr] = Map(),
    mutableVars: Map[Symbol, () => xt.Variable] = Map(),
    localFuns: Map[Symbol, (xt.ValDef, Seq[xt.TypeParameterDef])] = Map(),
    isExtern: Boolean = false
  ) {
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

    def withNewVar(nvar: (Symbol, () => xt.Expr)) = {
      copy(vars = vars + nvar)
    }

    def withNewMutableVar(nvar: (Symbol, () => xt.Variable)) = {
      copy(mutableVars = mutableVars + nvar)
    }

    def withNewMutableVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
      copy(mutableVars = mutableVars ++ nvars)
    }

    def withLocalFun(sym: Symbol, vd: xt.ValDef, tparams: Seq[xt.TypeParameterDef]) = {
      copy(localFuns = this.localFuns + (sym -> ((vd, tparams))))
    }
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

  private def extractImports(i: tpd.Import): Seq[xt.Import] = {
    def selectorChain(t: tpd.Tree): Seq[String] = t match {
      case Select(t2, name) => selectorChain(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case tpd.EmptyTree => Seq.empty
      case _ => outOfSubsetError(t, "Unexpected import selector: " + t)
    }

    val prefix = selectorChain(i.expr)
    val imports = i.selectors.map {
      case Ident(name) => prefix :+ name.toString
      case Thicket(Seq(Ident(name), _)) => prefix :+ name.toString
    }

    imports.map {
      case path :+ "_" => xt.Import(path, true)
      case p => xt.Import(p, false)
    }
  }

  def extractRef(t: tpd.RefTree): Identifier = {
    def rec(t: tpd.Tree): Seq[String] = t match {
      case Select(t2, name) => rec(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case tpd.EmptyTree => Seq.empty
      case _ => outOfSubsetError(t, "Unexpected selector " + t)
    }

    val refs = (rec(t.qualifier) :+ t.name.toString).filter(_ != "<empty>")
    FreshIdentifier(refs.mkString("$"))
  }

  def extractStatic(stats: List[tpd.Tree]): (
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
      case tpd.EmptyTree =>
        // ignore

      case t if (annotationsOf(t.symbol) contains xt.Ignore) || (t.symbol is Synthetic) =>
        // ignore

      case vd @ ValDef(_, _, _) if vd.symbol is Module =>
        // ignore

      case t @ ExSymbol("stainless", "annotation", "package$", "ignore") if t.isInstanceOf[tpd.TypeDef] =>
        // don't extract the `ignore` annotation class

      case i @ Import(_, _) =>
        imports ++= extractImports(i)

      case pd @ PackageDef(ref, stats) =>
        val (imports, classes, functions, modules, newClasses, newFunctions) = extractStatic(stats)
        subs :+= xt.ModuleDef(extractRef(ref), imports, classes, functions, modules)
        allClasses ++= newClasses
        allFunctions ++= newFunctions

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

      // Normal function
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        val fd = extractFunction(fsym, tparams, vparams, rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, Seq(), Seq(), rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      case other =>
        reporter.warning(other.pos, "Could not extract tree in static container: " + other)
    }

    (imports, classes, functions, subs, allClasses, allFunctions)
  }

  private def extractObject(td: tpd.TypeDef): (xt.ModuleDef, Seq[xt.ClassDef], Seq[xt.FunDef]) = {
    val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(td.rhs.asInstanceOf[tpd.Template].body)

    val module = xt.ModuleDef(
      symbols.getIdentifier(td.symbol),
      imports,
      classes,
      functions,
      subs
    ).setPos(td.pos)

    (module, allClasses, allFunctions)
  }

  private val invSymbol = stainless.ast.Symbol("inv")

  private def extractClass(td: tpd.TypeDef): (xt.ClassDef, Seq[xt.FunDef]) = {
    val sym = td.symbol
    val id = symbols.getIdentifier(sym)

    val template = td.rhs.asInstanceOf[tpd.Template]

    val extparams = sym.asClass.typeParams.map(extractTypeParam)
    val tpCtx = DefContext((sym.asClass.typeParams zip extparams).toMap)

    val parents = template.parents.flatMap(p => p.tpe match {
      case tpe if tpe.typeSymbol == defn.ObjectClass => None
      case tpe if defn.isProductClass(tpe.classSymbol) => None
      case tpe => Some(extractType(tpe)(tpCtx, p.pos).asInstanceOf[xt.ClassType])
    })

    val flags = annotationsOf(sym) ++ (if (sym is Abstract) Some(xt.IsAbstract) else None)

    val args = template.constr.vparamss.flatten
    val fieldCtx = DefContext((typeParamSymbols(template.constr.tparams) zip extparams).toMap)
    val fields = args.map { vd =>
      val tpe = stainlessType(vd.tpt.tpe)(fieldCtx, vd.pos)
      val vdSym = sym.info.decl(vd.symbol.name).symbol
      val id = symbols.getIdentifier(vdSym)
      val flags = annotationsOf(vdSym, ignoreOwner = true)
      if (vdSym.symbol is Mutable) xt.VarDef(id, tpe, flags).setPos(vd.pos)
      else xt.ValDef(id, tpe, flags).setPos(vd.pos)
    }

    val defCtx = tpCtx.withNewVars((args.map(_.symbol) zip fields.map(vd => () => vd.toVariable)).toMap)

    var invariants: Seq[xt.Expr] = Seq.empty
    var methods: Seq[xt.FunDef] = Seq.empty

    // We collect the methods and fields
    for (d <- template.body) d match {
      case tpd.EmptyTree =>
        // ignore

      case t if (
        (annotationsOf(t.symbol) contains xt.Ignore) ||
        ((t.symbol is Synthetic) && !(t.symbol is Implicit))
      ) =>
        // ignore

      case vd @ ValDef(_, _, _) if vd.symbol is ParamAccessor =>
        // ignore

      case dd @ DefDef(nme.CONSTRUCTOR, _, _, _, _) =>
        // ignore

      case td @ TypeDef(_, _) if td.symbol is Param =>
        // ignore

      // Class invariants
      case ExRequire(body) =>
        invariants :+= extractTree(body)(defCtx)

      // Default arguments of copy method
      case dd @ DefDef(name, _, _, _, _) if dd.symbol.name.toString.startsWith("copy$default$") =>
        // @nv: FIXME - check with dotty team about this and default arguments in general

      // Normal methods
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx)

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx)

      case d if d.symbol is Synthetic =>
        // ignore

      case d if d.symbol is Mutable =>
        // ignore

      case other =>
        reporter.warning(other.pos, "Could not extract tree in class: " + other)
    }

    val optInv = if (invariants.isEmpty) None else Some {
      new xt.FunDef(SymbolIdentifier(invSymbol), Seq.empty, Seq.empty, xt.BooleanType,
        if (invariants.size == 1) invariants.head else xt.And(invariants),
        Set(xt.IsInvariant) ++ flags
      )
    }

    val allMethods = (methods ++ optInv).map(fd => fd.copy(flags = fd.flags + xt.IsMethodOf(id)))

    (new xt.ClassDef(
      id,
      extparams.map(xt.TypeParameterDef(_)),
      parents,
      fields,
      flags
    ).setPos(sym.pos), allMethods)
  }

  //trim because sometimes Scala names end with a trailing space, looks nicer without the space
  private def freshId(sym: Symbol): Identifier = FreshIdentifier(sym.name.toString.trim)

  private def extractFunction(
    sym: Symbol,
    tdefs: Seq[tpd.TypeDef],
    vdefs: Seq[tpd.ValDef],
    rhs: tpd.Tree,
    typeParams: Option[Seq[xt.TypeParameter]] = None
  )(implicit dctx: DefContext): xt.FunDef = {

    // Type params of the function itself
    val extparams = typeParamSymbols(tdefs)
    val ntparams = typeParams.getOrElse(extparams map extractTypeParam)

    val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams).toMap)

    val (newParams, fctx0) = vdefs.foldLeft((Seq.empty[xt.ValDef], nctx)) { case ((params, dctx), param) =>
      val tpe = stainlessType(param.tpe)(dctx, param.tpt.pos)
      val ptpe = param.tpt match {
        case ByNameTypeTree(_) => xt.FunctionType(Seq(), tpe).setPos(param.tpt.pos)
        case _ => tpe
      }

      val flags = annotationsOf(param.symbol, ignoreOwner = true)
      val vd = xt.ValDef(FreshIdentifier(param.symbol.name.toString), ptpe, flags).setPos(param.pos)
      val expr = param.tpt match {
        case ByNameTypeTree(_) => () => xt.Application(vd.toVariable, Seq())
        case _ => () => vd.toVariable
      }

      (params :+ vd, dctx.withNewVar(param.symbol -> expr))
    }

    val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

    var flags = annotationsOf(sym).toSet ++ (if (sym is Implicit) Some(xt.Inline) else None)

    val id = symbols.getIdentifier(sym)

    // If this is a lazy field definition, drop the assignment/ accessing
    val body =
      if (!(flags contains xt.IsField(true))) rhs
      else rhs match {
        case Block(List(Assign(_, realBody)), _) => realBody
        case _ => outOfSubsetError(rhs, "Wrong form of lazy accessor")
      }

    val fctx = fctx0.copy(isExtern = fctx0.isExtern || (flags contains xt.Extern))

    val finalBody = if (rhs == tpd.EmptyTree) {
      flags += xt.IsAbstract
      xt.NoTree(returnType)
    } else {
      xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
    }

    //if (fctx.isExtern && !exists(_.isInstanceOf[NoTree])(finalBody)) {
    //  reporter.warning(finalBody.getPos, "External function could be extracted as Leon tree: "+finalBody)
    //}

    val fullBody = if (fctx.isExtern) {
      xt.exprOps.withBody(finalBody, xt.NoTree(returnType).setPos(body.pos))
    } else {
      finalBody
    }

    // Post-extraction sanity checks

    val fd = new xt.FunDef(
      id,
      ntparams.map(tp => xt.TypeParameterDef(tp)),
      newParams,
      returnType,
      fullBody,
      flags)

    fd.setPos(sym.pos)

    fd
  }

  private def typeParamSymbols(tdefs: Seq[tpd.TypeDef]): Seq[Symbol] = tdefs.flatMap(_.tpe match {
    case tp @ TypeRef(_, _) =>
      Some(tp.symbol)
    case t =>
      outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
      None
  })

  private def extractTypeParam(sym: Symbol): xt.TypeParameter = {
    val variance = if (sym is Covariant) Some(xt.Variance(true)) else if (sym is Contravariant) Some(xt.Variance(false)) else None
    xt.TypeParameter(symbols.getIdentifier(sym), variance.toSet)
  }

  private def extractPattern(p: tpd.Tree, binder: Option[xt.ValDef] = None)(implicit dctx: DefContext): (xt.Pattern, DefContext) = p match {
    case b @ Bind(name, t @ Typed(pat, tpt)) =>
      val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(b.symbol)).setPos(b.pos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(t, Some(vd))(pctx)

    case b @ Bind(name, pat) =>
      val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(b), annotationsOf(b.symbol)).setPos(b.pos)
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

    case s @ Select(_, b) if s.tpe.typeSymbol is (Case | Module) =>
      // case Obj =>
      extractType(s) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
        case _ =>
          outOfSubsetError(s, "Invalid instance pattern: "+s)
      }

    case id @ Ident(_) if id.symbol is (Case | Module) =>
      extractType(id) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
        case _ => 
          outOfSubsetError(id, "Invalid instance pattern: "+id)
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

    case UnApply(ExSymbol("stainless", "lang", "package$", "BigInt$", "unapply"), _, Seq(Literal(n))) =>
      val lit = xt.IntegerLiteral(BigInt(n.stringValue))
      (xt.LiteralPattern(binder, lit), dctx)

    case ExInt8Literal(i)    => (xt.LiteralPattern(binder, xt.Int8Literal(i)),    dctx)
    case ExInt16Literal(i)   => (xt.LiteralPattern(binder, xt.Int16Literal(i)),   dctx)
    case ExInt32Literal(i)   => (xt.LiteralPattern(binder, xt.Int32Literal(i)),   dctx)
    case ExInt64Literal(i)   => (xt.LiteralPattern(binder, xt.Int64Literal(i)),   dctx)
    case ExBooleanLiteral(b) => (xt.LiteralPattern(binder, xt.BooleanLiteral(b)), dctx)
    case ExUnitLiteral()     => (xt.LiteralPattern(binder, xt.UnitLiteral()),     dctx)
    case ExStringLiteral(s)  => (xt.LiteralPattern(binder, xt.StringLiteral(s)),  dctx)

    case t @ Typed(UnApply(f, _, pats), tp) =>
      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)

      val sym = f.symbol
      if (sym.owner.exists && sym.owner.is(Synthetic) &&
          sym.owner.companionClass.exists && sym.owner.companionClass.is(Case)) {
        val ct = extractType(tp).asInstanceOf[xt.ClassType]
        (xt.ClassPattern(binder, ct, subPatterns).setPos(p.pos), nctx)
      } else {
        val id = symbols.getIdentifier(sym)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.UnapplyPattern(binder, id, tps, subPatterns).setPos(t.pos), nctx)
      }

    case UnApply(f, _, pats) =>
      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)

      val sym = f.symbol
      if (sym.owner.exists && TupleSymbol.unapply(sym.owner.companionClass).isDefined) {
        (xt.TuplePattern(binder, subPatterns), nctx)
      } else if (sym.owner.exists && sym.owner.is(Synthetic) &&
          sym.owner.companionClass.exists && sym.owner.companionClass.is(Case)) {
        val id = symbols.getIdentifier(sym.owner.symbol.companionClass)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.ClassPattern(binder, xt.ClassType(id, tps).setPos(p.pos), subPatterns).setPos(p.pos), nctx)
      } else {
        val id = symbols.getIdentifier(sym)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.UnapplyPattern(binder, id, tps, subPatterns).setPos(p.pos), nctx)
      }

    case _ =>
      outOfSubsetError(p, "Unsupported pattern: "+p)
  }

  private def extractMatchCase(cd: tpd.CaseDef)(implicit dctx: DefContext): xt.MatchCase = {
    val (recPattern, ndctx) = extractPattern(cd.pat)
    val recBody             = extractTree(cd.body)(ndctx)

    if (cd.guard == tpd.EmptyTree) {
      xt.MatchCase(recPattern, None, recBody).setPos(cd.pos)
    } else {
      val recGuard = extractTree(cd.guard)(ndctx)
      xt.MatchCase(recPattern, Some(recGuard), recBody).setPos(cd.pos)
    }
  }

  private def extractTreeOrNoTree(tr: tpd.Tree)(implicit dctx: DefContext): xt.Expr = {
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

  private def extractSeq(args: Seq[tpd.Tree])(implicit dctx: DefContext): Seq[xt.Expr] = args match {
    case Seq(SeqLiteral(es, _)) =>
      es.map(extractTree)
    case Seq(Typed(SeqLiteral(es, _), tpt)) if tpt.tpe.typeSymbol == defn.RepeatedParamClass =>
      es.map(extractTree)
    case _ =>
      args.map(extractTree)
  }

  private def extractBlock(es: List[tpd.Tree])(implicit dctx: DefContext): xt.Expr = {
    val fctx = es.collect {
      case ExFunctionDef(sym, tparams, vparams, tpt, rhs) => (sym, tparams, vparams)
    }.foldLeft(dctx) { case (dctx, (sym, tparams, vparams)) =>
      val extparams = typeParamSymbols(tparams)
      val ntparams = extparams map extractTypeParam
      val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams).toMap)

      val paramTypes = vparams.map { param =>
        val ptpe = stainlessType(param.tpe)(nctx, param.pos)
        param.tpt match {
          case ByNameTypeTree(_) => xt.FunctionType(Seq(), ptpe)
          case _ => ptpe
        }
      }
      val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)
      val name = xt.ValDef(
        symbols.getIdentifier(sym),
        xt.FunctionType(paramTypes, returnType).setPos(sym.pos),
        annotationsOf(sym)
      ).setPos(sym.pos)

      dctx.withLocalFun(sym, name, ntparams.map(tp => xt.TypeParameterDef(tp)))
    }

    val (vds, vctx) = es.collect {
      case v @ ValDef(name, tpt, _) => (v.symbol, name, tpt)
    }.foldLeft((Map.empty[Symbol, xt.ValDef], fctx)) { case ((vds, dctx), (sym, name, tpt)) =>
      if (sym is Mutable) {
        val vd = xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
        (vds + (sym -> vd), dctx.withNewMutableVar(sym, () => vd.toVariable))
      } else {
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
        (vds + (sym -> vd), dctx.withNewVar(sym, () => vd.toVariable))
      }
    }

    def rec(es: List[tpd.Tree]): xt.Expr = es match {
      case Nil => xt.UnitLiteral()

      case (e @ ExAssert(contract, oerr)) :: xs =>
        val const = extractTree(contract)(vctx)
        val b     = rec(xs)
        xt.Assert(const, oerr, b).setPos(e.pos)

      case (e @ ExRequire(contract)) :: xs =>
        val pre = extractTree(contract)(vctx)
        val b   = rec(xs)
        xt.Require(pre, b).setPos(e.pos)

      case (e @ ExDecreases(ranks)) :: xs =>
        val measure = xt.tupleWrap(ranks.map(extractTree(_)(vctx)))
        val b       = rec(xs)
        xt.Decreases(measure, b).setPos(e.pos)

      case (d @ ExFunctionDef(sym, tparams, params, ret, b)) :: xs =>
        val (vd, tdefs) = vctx.localFuns(sym)
        val fd = extractFunction(sym, tparams, params, b, typeParams = Some(tdefs.map(_.tp)))(vctx)
        val letRec = xt.LocalFunDef(vd, tdefs, xt.Lambda(fd.params, fd.fullBody).setPos(d.pos))

        rec(xs) match {
          case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body).setPos(d.pos)
          case other => xt.LetRec(Seq(letRec), other).setPos(d.pos)
        }

      case (v @ ValDef(name, tpt, _)) :: xs =>
        if (v.symbol is Mutable) {
          xt.LetVar(vds(v.symbol), extractTree(v.rhs)(vctx), rec(xs)).setPos(v.pos)
        } else {
          xt.Let(vds(v.symbol), extractTree(v.rhs)(vctx), rec(xs)).setPos(v.pos)
        }

      case ExWhile(cond, body, rest) =>
        val wh = xt.While(extractTree(cond), extractBlock(body), None).setPos(es.head.pos)
        rec(rest) match {
          case xt.Block(elems, last) => xt.Block(wh +: elems, last).setPos(es.head.pos)
          case e => xt.Block(Seq(wh), e).setPos(es.head.pos)
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

  private def extractArgs(sym: Symbol, args: Seq[tpd.Tree])(implicit dctx: DefContext): Seq[xt.Expr] = {
    (args zip sym.info.paramInfoss.flatten) map {
      case (arg, ExprType(_)) => xt.Lambda(Seq(), extractTree(arg)).setPos(arg.pos)
      case (arg, _) => extractTree(arg)
    }
  }

  private def extractTree(tr: tpd.Tree)(implicit dctx: DefContext): xt.Expr = (tr match {
    case Block(Seq(dd @ DefDef(_, _, Seq(vparams), _, _)), ExUnwrapped(Closure(Nil, call, targetTpt))) if call.symbol == dd.symbol =>
      val vds = vparams map (vd => xt.ValDef(
        FreshIdentifier(vd.symbol.name.toString),
        extractType(vd.tpt),
        annotationsOf(vd.symbol)
      ).setPos(vd.pos))

      xt.Lambda(vds, extractTree(dd.rhs)(dctx.withNewVars((vparams zip vds).map {
        case (v, vd) => v.symbol -> (() => vd.toVariable)
      })))

    case Block(es, e) =>
      val b = extractBlock(es :+ e)
      xt.exprOps.flattenBlocks(b)

    case ExAssert(contract, oerr) =>
      xt.Assert(extractTree(contract), oerr, xt.UnitLiteral().setPos(tr.pos))

    case ExUnwrapped(tree) if tree ne tr => extractTree(tree)

    case ExEnsuring(body, contract) =>
      val post = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      val closure = post match {
        case l: xt.Lambda => l
        case other =>
          val tpe = extractType(tr)
          val vd = xt.ValDef(FreshIdentifier("res"), tpe, Set.empty).setPos(post)
          xt.Lambda(Seq(vd), extractType(contract) match {
            case xt.BooleanType => post
            case _ => xt.Application(other, Seq(vd.toVariable)).setPos(post)
          }).setPos(post)
      }

      xt.Ensuring(b, closure)

    // an optional "because" is allowed
    case t @ ExHolds(body, Apply(ExSymbol("stainless", "lang", "package$", "because"), Seq(proof))) =>
      val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post)

    case t @ ExHolds(body, proof) =>
      val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post)

    case t @ ExHolds(body) =>
      val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post)

    // If the because statement encompasses a holds statement
    case t @ ExBecause(ExHolds(body), proof) =>
      val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post)

    case t @ ExComputes(body, expected) =>
      val tpe = extractType(body)
      val vd = xt.ValDef(FreshIdentifier("holds"), tpe, Set.empty).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.Equals(vd.toVariable, extractTreeOrNoTree(expected)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post)

    case ExPre(f) => xt.Pre(extractTree(f))
    case ExOld(e) => xt.Old(extractTree(e))

    case t @ Select(
      str @ ExSymbol("stainless", "lang", "package$", "StringDecorations"),
      ExNamed("bigLength")
    ) => xt.StringLength(extractTree(str).setPos(str.pos))

    case t @ Apply(Select(
      str @ ExSymbol("stainless", "lang", "package$", "StringDecorations"),
      ExNamed("bigSubstring")
    ), startTree :: rest) =>
      val start = extractTree(startTree).setPos(startTree.pos)
      rest match {
        case Seq() =>
          val vd = xt.ValDef(FreshIdentifier("s"), xt.StringType, Set.empty).setPos(str.pos)
          xt.Let(vd, extractTreeOrNoTree(str),
            xt.SubString(vd.toVariable, start,
              xt.StringLength(vd.toVariable).setPos(t.pos)
            ).setPos(t.pos))
        case Seq(endTree) =>
          xt.SubString(extractTreeOrNoTree(str), start, extractTreeOrNoTree(endTree))
        case _ => outOfSubsetError(t, "Unknown \"bigSubstring\" call: " + t)
      }

    case Apply(TypeApply(ExSymbol("scala", "Array$", "apply"), Seq(tpt)), args) =>
      xt.FiniteArray(extractSeq(args), extractType(tpt))

    case Apply(Apply(TypeApply(ExSymbol("scala", "Array$", "apply"), Seq(tpt)), args), Seq(_)) =>
      xt.FiniteArray(extractSeq(args), extractType(tpt))

    case Apply(ExSymbol("scala", "Array$", "apply"), head +: tail) =>
      val xt.ArrayType(base) = extractType(tr)
      xt.FiniteArray(extractTree(head) +: extractSeq(tail), base)

    case s @ Select(_, _) if s.tpe.typeSymbol is ModuleClass =>
      extractType(s) match {
        case ct: xt.ClassType => xt.ClassConstructor(ct, Seq.empty)
        case tpe => outOfSubsetError(tr, "Unexepected class constructor type: " + tpe)
      }

    case ExTuple(args) =>
      xt.Tuple(args.map(extractTree))

    case Apply(TypeApply(ExSymbol("stainless", "lang", "error"), Seq(tpt)), Seq(Literal(cnst))) =>
      xt.Error(extractType(tpt), cnst.stringValue)

    case ExTupleSelect(tuple, i) =>
      xt.TupleSelect(extractTree(tuple), i)

    // FIXME case ExDefaultValueFunction

    /**
     * XLang Extractors
     */

    case a @ Assign(id @ Ident(_), rhs) =>
      dctx.mutableVars.get(id.symbol) match {
        case Some(fun) =>
          xt.Assignment(fun().setPos(id.pos), extractTree(rhs))

        case None => id.tpe match {
          case TermRef(tt: ThisType, _) =>
            xt.FieldAssignment(
              xt.This(extractType(tt)(dctx, id.pos).asInstanceOf[xt.ClassType]).setPos(id.pos),
              symbols.getIdentifier(id.symbol),
              extractTree(rhs)
            )

          case _ =>
            outOfSubsetError(a, "Undeclared variable.")
        }
      }

    case Assign(s @ Select(lhs, name), rhs) =>
      xt.FieldAssignment(extractTree(lhs), symbols.getIdentifier(s.symbol), extractTree(rhs))

    case ExCall(
      Some(rec),
      ExSymbol("stainless", "lang", "package$", "WhileDecorations", "invariant"),
      Seq(),
      Seq(pred)
    ) => extractTree(rec) match {
      case b @ xt.Block(Seq(w @ xt.While(cond, body, None)), e) =>
        xt.Block(Seq(xt.While(cond, body, Some(extractTree(pred))).copiedFrom(w)), e).copiedFrom(b)
      case e =>
        outOfSubsetError(tr, "Unexpected while loop invariant.")
    }

    case ExBigIntLiteral(Literal(cnst)) =>
      xt.IntegerLiteral(BigInt(cnst.stringValue))

    case Apply(ExSymbol("scala", "math", "BigInt$", "int2bigInt"), Seq(t)) => extractTree(t) match {
      case xt.Int32Literal(n) => xt.IntegerLiteral(BigInt(n))
      case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
    }

    case ExRealLiteral(args) => args.map(extractTree) match {
      case Seq(xt.IntegerLiteral(n), xt.IntegerLiteral(d)) => xt.FractionLiteral(n, d)
      case Seq(xt.IntegerLiteral(n)) => xt.FractionLiteral(n, 1)
      case _ => outOfSubsetError(tr, "Real not built from literals")
    }

    case ExInt8Literal(v)  => xt.Int8Literal(v)
    case ExInt16Literal(v) => xt.Int16Literal(v)
    case ExInt32Literal(v) => xt.Int32Literal(v)
    case ExInt64Literal(v) => xt.Int64Literal(v)

    case ExBooleanLiteral(v) =>
      xt.BooleanLiteral(v)

    case ExUnitLiteral() =>
      xt.UnitLiteral()

    case Apply(TypeApply(ExSymbol("scala", "Predef$", "locally"), _), Seq(body)) =>
      extractTree(body)

    case Typed(e, _) =>
      extractTree(e)

    case Inlined(_, members, body) =>
      extractBlock(members :+ body)

    case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "choose"), Seq(tpt)), Seq(pred)) =>
      extractTree(pred) match {
        case xt.Lambda(Seq(vd), body) => xt.Choose(vd, body)
        case e => extractType(tpt) match {
          case xt.FunctionType(Seq(argType), xt.BooleanType) =>
            val vd = xt.ValDef(FreshIdentifier("x", true), argType, Set.empty).setPos(pred.pos)
            xt.Choose(vd, xt.Application(e, Seq(vd.toVariable)).setPos(pred.pos))
          case _ => outOfSubsetError(tr, "Expected choose to take a function-typed predicate")
        }
      }

    case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "forall"), types), Seq(fun)) =>
      extractTree(fun) match {
        case xt.Lambda(vds, body) => xt.Forall(vds, body)
        case pred => extractType(fun) match {
          case xt.FunctionType(from, to) =>
            val args = from.map(tpe => xt.ValDef(FreshIdentifier("x", true), tpe).setPos(pred))
            xt.Forall(args, xt.Application(pred, args.map(_.toVariable)).setPos(pred))
          case _ =>
            outOfSubsetError(tr, "Unsupported forall definition: " + tr)
        }
      }

    case Apply(TypeApply(
      ExSymbol("stainless", "lang", "Map$", "apply"),
      Seq(tptFrom, tptTo)
    ), args) =>
      val to = extractType(tptTo)
      val pairs = extractSeq(args) map {
        case xt.Tuple(Seq(key, value)) => key -> value
        case e => (xt.TupleSelect(e, 1).setPos(e), xt.TupleSelect(e, 2).setPos(e))
      }

      val somePairs = pairs.map { case (key, value) =>
        key -> xt.ClassConstructor(
          xt.ClassType(symbols.getIdentifier(someSymbol), Seq(to)).setPos(value),
          Seq(value)
        ).setPos(value)
      }

      val dflt = xt.ClassConstructor(
        xt.ClassType(symbols.getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
        Seq.empty
      ).setPos(tr.pos)

      val optTo = xt.ClassType(symbols.getIdentifier(optionSymbol), Seq(to))
      xt.FiniteMap(somePairs, dflt, extractType(tptFrom), optTo)

    case Apply(TypeApply(
      ExSymbol("stainless", "lang", "Set$", "apply"),
      Seq(tpt)
    ), args) => xt.FiniteSet(extractSeq(args), extractType(tpt))

    case Apply(TypeApply(
      ExSymbol("stainless", "lang", "Bag$", "apply"),
      Seq(tpt)
    ), args) => xt.FiniteBag(extractSeq(args).map {
      case xt.Tuple(Seq(key, value)) => key -> value
      case e => (xt.TupleSelect(e, 1).setPos(e), xt.TupleSelect(e, 2).setPos(e))
    }, extractType(tpt))

    case Select(e, nme.UNARY_+) => injectCast(e => e)(e)
    case Select(e, nme.UNARY_!) => xt.Not(extractTree(e))
    case Select(e, nme.UNARY_-) => injectCast(xt.UMinus)(e)
    case Select(e, nme.UNARY_~) => injectCast(xt.BVNot)(e)

    case Apply(Select(l, nme.NE), Seq(r)) => xt.Not(((extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (lit @ xt.BVLiteral(_, _), _, e, xt.IntegerType) => xt.Equals(xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit), e)
      case (e, xt.IntegerType, lit @ xt.BVLiteral(_, _), _) => xt.Equals(e, xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit))
      case _ => injectCasts(xt.Equals)(l, r)
    }).setPos(tr.pos))

    case Apply(Select(l, nme.EQ), Seq(r)) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (lit @ xt.BVLiteral(_, _), _, e, xt.IntegerType) => xt.Equals(xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit), e)
      case (e, xt.IntegerType, lit @ xt.BVLiteral(_, _), _) => xt.Equals(e, xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit))
      case _ => injectCasts(xt.Equals)(l, r)
    }

    case Apply(Apply(Apply(TypeApply(
      ExSymbol("scala", "Array$", "fill"),
      Seq(baseType)
    ), Seq(length)), Seq(dflt)), _) =>
      xt.LargeArray(Map.empty, extractTree(dflt), extractTree(length), extractType(baseType))

    case If(t1,t2,t3) =>
      xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

    case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_asInstanceOf =>
      extractType(tpt) match {
        case ct: xt.ClassType => xt.AsInstanceOf(extractTree(t), ct)
        case _ =>
          // XXX @nv: dotc generates spurious `asInstanceOf` casts for now, se
          //          we will have to rely on later type checks within Stainless
          //          to catch issues stemming from casts we ignored here.
          // outOfSubsetError(tr, "asInstanceOf can only cast to class types")
          extractTree(t)
      }

    case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_isInstanceOf =>
      extractType(tpt) match {
        case ct: xt.ClassType => xt.IsInstanceOf(extractTree(t), ct)
        case _ => outOfSubsetError(tr, "isInstanceOf can only be used with class types")
      }

    case Match(scrut, cases) =>
      xt.MatchExpr(extractTree(scrut), cases.map(extractMatchCase))

    case t @ This(_) =>
      extractType(t) match {
        case ct: xt.ClassType => xt.This(ct)
        case _ => outOfSubsetError(t, "Invalid usage of `this`")
      }

    case Apply(Apply(
      TypeApply(Select(Apply(ExSymbol("scala", "Predef$", s), Seq(lhs)), ExNamed("updated")), _),
      Seq(index, value)
    ), Seq(Apply(_, _))) if s.toString contains "Array" =>
      xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))

    case Apply(TypeApply(ExSymbol("stainless", "collection", "List$", "apply"), Seq(tpt)), args) =>
      val tpe = extractType(tpt)
      val cons = xt.ClassType(symbols.getIdentifier(consSymbol), Seq(tpe))
      val nil  = xt.ClassType(symbols.getIdentifier(nilSymbol),  Seq(tpe))
      extractSeq(args).foldRight(xt.ClassConstructor(nil, Seq.empty).setPos(tr.pos)) {
        case (e, ls) => xt.ClassConstructor(cons, Seq(e, ls)).setPos(e)
      }

    case ExCharLiteral(c) => xt.CharLiteral(c)
    case ExStringLiteral(s) => xt.StringLiteral(s)

    case Apply(Select(
      Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), Seq(lhs)),
      ExNamed("$eq$eq$greater")
    ), Seq(rhs)) => xt.Implies(extractTree(lhs), extractTree(rhs))

    case Apply(tree, args) if defn.isFunctionType(tree.tpe) =>
      xt.Application(extractTree(tree), args map extractTree)

    case NamedArg(name, arg) => extractTree(arg)

    case ExConstructor(tpe, args) => extractType(tpe)(dctx, tr.pos) match {
      case ct: xt.ClassType => xt.ClassConstructor(ct, args map extractTree)
      case tt: xt.TupleType => xt.Tuple(args map extractTree)
      case _ => outOfSubsetError(tr, "Unexpected constructor " + tr)
    }

    case ex @ ExIdentifier(sym, tpt) if dctx.vars contains sym => dctx.vars(sym)().setPos(ex.pos)
    case ex @ ExIdentifier(sym, tpt) if dctx.mutableVars contains sym => dctx.mutableVars(sym)().setPos(ex.pos)

    case ExThisCall(tt, sym, tps, args) =>
      val thiss = xt.This(extractType(tt)(dctx, tr.pos).asInstanceOf[xt.ClassType]).setPos(tr.pos)
      if (sym is ParamAccessor) {
        xt.ClassSelector(thiss, symbols.getIdentifier(sym))
      } else {
        xt.MethodInvocation(thiss, symbols.getIdentifier(sym), tps map extractType, extractArgs(sym, args))
      }

    case ExCall(rec, sym, tps, args) => rec match {
      case None =>
        dctx.localFuns.get(sym) match {
          case None =>
            xt.FunctionInvocation(symbols.getIdentifier(sym), tps map extractType, extractArgs(sym, args))
          case Some((name, tparams)) =>
            xt.ApplyLetRec(name.toVariable, tparams.map(_.tp), tps map extractType, extractArgs(sym, args))
        }

      case Some(lhs) => extractType(lhs) match {
        case ct: xt.ClassType =>
          if (sym is ParamAccessor) {
            xt.ClassSelector(extractTree(lhs), symbols.getIdentifier(sym))
          } else {
            xt.MethodInvocation(extractTree(lhs), symbols.getIdentifier(sym), tps map extractType, extractArgs(sym, args))
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
          case (xt.SetType(b), "-", Seq(rhs)) => xt.SetDifference(extractTree(lhs), xt.FiniteSet(Seq(extractTree(rhs)), b).setPos(tr.pos))

          case (xt.BagType(_), "+",   Seq(rhs)) => xt.BagAdd(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "++",  Seq(rhs)) => xt.BagUnion(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "&",   Seq(rhs)) => xt.BagIntersection(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "--",  Seq(rhs)) => xt.BagDifference(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "get", Seq(rhs)) => xt.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

          case (xt.ArrayType(_), "apply",   Seq(rhs))          => xt.ArraySelect(extractTree(lhs), extractTree(rhs))
          case (xt.ArrayType(_), "length",  Seq())             => xt.ArrayLength(extractTree(lhs))
          case (xt.ArrayType(_), "updated", Seq(index, value)) => xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))
          case (xt.ArrayType(_), "update",  Seq(index, value)) => xt.ArrayUpdate(extractTree(lhs), extractTree(index), extractTree(value))
          case (xt.ArrayType(_), "clone",   Seq())             => extractTree(lhs)

          case (xt.MapType(_, _), "get", Seq(rhs)) =>
            xt.MapApply(extractTree(lhs), extractTree(rhs))

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "apply", Seq(rhs)) =>
            val (l, r) = (extractTree(lhs), extractTree(rhs))
            val someTpe = xt.ClassType(symbols.getIdentifier(someSymbol), Seq(to)).setPos(tr.pos)
            xt.Assert(
              xt.IsInstanceOf(xt.MapApply(l, r).setPos(tr.pos), someTpe).setPos(tr.pos),
              Some("Map undefined at this index"),
              xt.ClassSelector(
                xt.AsInstanceOf(xt.MapApply(l, r).setPos(tr.pos), someTpe).setPos(tr.pos),
                symbols.getIdentifier(someSymbol.info.decl(termName("v")).symbol)
              ).setPos(tr.pos)
            )

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "isDefinedAt" | "contains", Seq(rhs)) =>
            xt.Not(xt.Equals(
              xt.MapApply(extractTree(lhs), extractTree(rhs)).setPos(tr.pos),
              xt.ClassConstructor(
                xt.ClassType(symbols.getIdentifier(noneSymbol).setPos(tr.pos), Seq(to)).setPos(tr.pos),
                Seq()
              ).setPos(tr.pos)
            ).setPos(tr.pos))

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "updated" | "+", Seq(key, value)) =>
            xt.MapUpdated(
              extractTree(lhs), extractTree(key),
              xt.ClassConstructor(
                xt.ClassType(symbols.getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                Seq(extractTree(value))
              ).setPos(tr.pos)
            )

          case (xt.MapType(from, xt.ClassType(_, Seq(to))), "+", Seq(rhs)) =>
            val vd = xt.ValDef(FreshIdentifier("x", true), xt.TupleType(Seq(from, to)).setPos(tr.pos)).setPos(tr.pos)
            xt.Let(vd, extractTree(rhs), xt.MapUpdated(
              extractTree(lhs), xt.TupleSelect(vd.toVariable, 1).setPos(tr.pos),
              xt.ClassConstructor(
                xt.ClassType(symbols.getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                Seq(xt.TupleSelect(vd.toVariable, 2).setPos(tr.pos))
              ).setPos(tr.pos)
            ).setPos(tr.pos))

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "++", Seq(rhs)) =>
            extractTree(rhs) match {
              case xt.FiniteMap(pairs, default, keyType, valueType) =>
                pairs.foldLeft(extractTree(lhs)) { case (map, (k, v)) =>
                  xt.MapUpdated(map, k, v).setPos(tr.pos)
                }

              case _ => outOfSubsetError(tr, "Can't extract map union with non-finite map")
            }

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "getOrElse", Seq(key, orElse)) =>
            xt.MethodInvocation(
              xt.MapApply(extractTree(lhs), extractTree(key)).setPos(tr.pos),
              symbols.getIdentifier(optionSymbol.info.decl(termName("getOrElse")).symbol),
              Seq.empty,
              Seq(xt.Lambda(Seq(), extractTree(orElse)).setPos(tr.pos))
            )

          case (_, "-",   Seq(rhs)) => injectCasts(xt.Minus)(lhs, rhs)
          case (_, "*",   Seq(rhs)) => injectCasts(xt.Times)(lhs, rhs)
          case (_, "%",   Seq(rhs)) => injectCasts(xt.Remainder)(lhs, rhs)
          case (_, "mod", Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
          case (_, "/",   Seq(rhs)) => injectCasts(xt.Division)(lhs, rhs)
          case (_, ">",   Seq(rhs)) => injectCasts(xt.GreaterThan)(lhs, rhs)
          case (_, ">=",  Seq(rhs)) => injectCasts(xt.GreaterEquals)(lhs, rhs)
          case (_, "<",   Seq(rhs)) => injectCasts(xt.LessThan)(lhs, rhs)
          case (_, "<=",  Seq(rhs)) => injectCasts(xt.LessEquals)(lhs, rhs)

          case (_, "|",   Seq(rhs)) => injectCasts(xt.BVOr)(lhs, rhs)
          case (_, "&",   Seq(rhs)) => injectCasts(xt.BVAnd)(lhs, rhs)
          case (_, "^",   Seq(rhs)) => injectCasts(xt.BVXor)(lhs, rhs)
          case (_, "<<",  Seq(rhs)) => injectCastsForShift(xt.BVShiftLeft)(lhs, rhs)
          case (_, ">>",  Seq(rhs)) => injectCastsForShift(xt.BVAShiftRight)(lhs, rhs)
          case (_, ">>>", Seq(rhs)) => injectCastsForShift(xt.BVLShiftRight)(lhs, rhs)

          case (_, "&&",  Seq(rhs)) => xt.And(extractTree(lhs), extractTree(rhs))
          case (_, "||",  Seq(rhs)) => xt.Or(extractTree(lhs), extractTree(rhs))

          // FIXME 'toByte' and so on are apparently different with dotty...
          case (tpe, "toByte", Seq()) => tpe match {
            case xt.BVType(8) => extractTree(lhs)
            case xt.BVType(16 | 32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(8))
            case tpe => outOfSubsetError(tr, "Unexpected cast .toByte from $tpe")
          }

          case (tpe, "toShort", Seq()) => tpe match {
            case xt.BVType(8) => xt.BVWideningCast(extractTree(lhs), xt.BVType(16))
            case xt.BVType(16) => extractTree(lhs)
            case xt.BVType(32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(16))
            case tpe => outOfSubsetError(tr, "Unexpected cast .toShort from $tpe")
          }

          case (tpe, "toInt", Seq()) => tpe match {
            case xt.BVType(8 | 16) => xt.BVWideningCast(extractTree(lhs), xt.BVType(32))
            case xt.BVType(32) => extractTree(lhs)
            case xt.BVType(64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(32))
            case tpe => outOfSubsetError(tr, "Unexpected cast .toInt from $tpe")
          }

          case (tpe, "toLong", Seq()) => tpe match {
            case xt.BVType(8 | 16 | 32 ) => xt.BVWideningCast(extractTree(lhs), xt.BVType(64))
            case xt.BVType(64) => extractTree(lhs)
            case tpe => outOfSubsetError(tr, "Unexpected cast .toLong from $tpe")
          }

          case (tpe, name, args) =>
            outOfSubsetError(tr, "Unknown call to " + name +
              s" on $lhs (${extractType(lhs)}) with arguments $args of type ${args.map(a => extractType(a))}")
        }
      }
    }

    // default behaviour is to complain :)
    case _ => outOfSubsetError(tr, "Could not extract tree " + tr + " ("+tr.getClass+")")
  }).setPos(tr.pos)


  /** Inject implicit widening casts according to the Java semantics (5.6.2. Binary Numeric Promotion) */
  private def injectCasts(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                         (lhs0: tpd.Tree, rhs0: tpd.Tree)
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
                                 (lhs0: tpd.Tree, rhs0: tpd.Tree)
                                 (implicit dctx: DefContext): xt.Expr = {
    injectCastsImpl(ctor)(lhs0, rhs0, true)
  }

  private def injectCastsImpl(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                             (lhs0: tpd.Tree, rhs0: tpd.Tree, shift: Boolean)
                             (implicit dctx: DefContext): xt.Expr = {
    def checkBits(tr: tpd.Tree, tpe: xt.Type) = tpe match {
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
  private def injectCast(ctor: xt.Expr => xt.Expr)(e0: tpd.Tree)(implicit dctx: DefContext): xt.Expr = {
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

  private def extractType(t: tpd.Tree)(implicit dctx: DefContext): xt.Type = {
    extractType(t.tpe)(dctx, t.pos)
  }

  private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = (tpt match {
    case tpe if tpe.typeSymbol == defn.CharClass    => xt.CharType
    case tpe if tpe.typeSymbol == defn.ByteClass    => xt.Int8Type
    case tpe if tpe.typeSymbol == defn.ShortClass   => xt.Int16Type
    case tpe if tpe.typeSymbol == defn.IntClass     => xt.Int32Type
    case tpe if tpe.typeSymbol == defn.LongClass    => xt.Int64Type
    case tpe if tpe.typeSymbol == defn.BooleanClass => xt.BooleanType
    case tpe if tpe.typeSymbol == defn.UnitClass    => xt.UnitType

    case tpe if isBigIntSym(tpe.typeSymbol) => xt.IntegerType
    case tpe if isRealSym(tpe.typeSymbol)   => xt.RealType
    case tpe if isStringSym(tpe.typeSymbol) => xt.StringType

    case ct: ConstantType => extractType(ct.value.tpe)

    case tr: TypeRef if dctx.tparams.isDefinedAt(tr.symbol) => dctx.tparams(tr.symbol)

    case tt @ TypeRef(_, _) if tt != tt.dealias =>
      extractType(tt.dealias)

    case tt @ TypeRef(prefix: TermRef, name) if prefix.underlying.classSymbol.typeParams.exists(_.name == name) =>
      extractType(TypeRef(prefix.widenTermRefExpr, name))

    case tt @ TypeRef(prefix, name) if prefix.classSymbol.typeParams.exists(_.name == name) =>
      val idx = prefix.classSymbol.typeParams.indexWhere(_.name == name)
      (extractType(prefix), idx) match {
        case (xt.MapType(from, ct @ xt.ClassType(id, Seq(to))), 1) => to
        case (tp @ xt.typeOps.Deconstructor(tps, _), _) => tps(idx)
      }

    case tr: TypeRef if isScalaSetSym(tr.symbol) =>
      outOfSubsetError(pos, "Scala's Set API is no longer extracted. Make sure you import leon.lang.Set that defines supported Set operations.")
    case tr: TypeRef if isScalaMapSym(tr.symbol) =>
      outOfSubsetError(pos, "Scala's Map API is no longer extracted. Make sure you import leon.lang.Map that defines supported Map operations.")

    case tr: TypeRef if isSetSym(tr.symbol) =>
      val Seq(tp) = tr.classSymbol.typeParams.map(extractTypeParam)
      xt.SetType(tp)

    case tr: TypeRef if isBagSym(tr.symbol) =>
      val Seq(tp) = tr.classSymbol.typeParams.map(extractTypeParam)
      xt.BagType(tp)

    case tr: TypeRef if isMapSym(tr.symbol) =>
      val Seq(from, to) = tr.classSymbol.typeParams.map(extractTypeParam)
      xt.MapType(from, xt.ClassType(symbols.getIdentifier(optionSymbol), Seq(to)).setPos(pos))

    case tr: TypeRef if TupleSymbol.unapply(tr.classSymbol).isDefined =>
      xt.TupleType(tr.classSymbol.typeParams.map(extractTypeParam))

    case tr: TypeRef if isArrayClassSym(tr.symbol) =>
      val Seq(tp) = tr.classSymbol.typeParams.map(extractTypeParam)
      xt.ArrayType(tp)

    case _ if defn.isFunctionClass(tpt.typeSymbol) && tpt.dealias.argInfos.isEmpty =>
      xt.FunctionType(Seq(), xt.UnitType)

    case defn.FunctionOf(from, to, _) =>
      xt.FunctionType(from map extractType, extractType(to))

    case tt @ ThisType(tr) =>
      extractType(tr)

    case RefinedType(p, name, tpe) =>
      val bt = extractType(p)
      val idx = p.classSymbol.typeParams.indexWhere(_.name == name)
      (extractType(p), idx) match {
        case (xt.MapType(from, ct @ xt.ClassType(id, Seq(to))), 1) =>
          xt.MapType(from, xt.ClassType(id, Seq(extractType(tpe))).copiedFrom(ct))
        case (xt.typeOps.Deconstructor(tps, recons), _) =>
          recons(tps.updated(idx, extractType(tpe)))
      }

    case tt @ TypeRef(_, _) if tt.classSymbol.exists =>
      val sym = tt.classSymbol
      xt.ClassType(symbols.getIdentifier(sym), sym.typeParams.map {
        sym => xt.TypeParameter(symbols.getIdentifier(sym), Set.empty)
      })

    case tt @ TermRef(_, _) => extractType(tt.widenTermRefExpr)

    case ta @ TypeAlias(tp) => extractType(tp)

    case tb @ TypeBounds(lo, hi) => extractType(hi)

    case AndType(tp, prod) if prod.typeSymbol == defn.ProductClass => extractType(tp)
    case AndType(prod, tp) if prod.typeSymbol == defn.ProductClass => extractType(tp)
    case ot: OrType => extractType(ot.join)

    case pp @ TypeParamRef(binder, num) =>
      dctx.tparams.collectFirst { case (k, v) if k.name == pp.paramName => v }.getOrElse {
        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract "+tpt+" with context " + dctx.tparams)
      }

    case tp: TypeVar => extractType(tp.stripTypeVar)

    case AnnotatedType(tpe, _) => extractType(tpe)

    // @nv: we want this case to be close to the end as it otherwise interferes with other cases
    case tpe if tpe.typeSymbol == defn.NothingClass => xt.NothingType

    case _ =>
      if (tpt ne null) {
        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type: "+tpt+" ("+tpt.getClass+")")
      } else {
        outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
      }
  }).setPos(pos)
}
