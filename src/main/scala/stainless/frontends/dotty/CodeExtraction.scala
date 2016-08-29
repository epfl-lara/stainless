/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotty

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Phases._
import core.Contexts._
import core.Constants._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._
import util.Positions._

import inox.ast.{Identifier, FreshIdentifier}
import xlang.{trees => xt}

import scala.collection.mutable.{Map => MutableMap}
import scala.util.matching.Regex

import scala.language.implicitConversions

class CodeExtraction(inoxCtx: inox.InoxContext)(implicit val ctx: Context) extends ASTExtractors {
  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  lazy val reporter = inoxCtx.reporter

  implicit def dottyPosToInoxPos(p: Position): inox.utils.Position = {
    if (!p.exists) {
      inox.utils.NoPosition
    } else if (p.start != p.end) {
      val start = ctx.source.atPos(p.startPos)
      val end   = ctx.source.atPos(p.endPos)
      inox.utils.RangePosition(start.line, start.column, start.point,
                               end.line, end.column, end.point,
                               ctx.source.file.file)
    } else {
      val sp = ctx.source.atPos(p)
      inox.utils.OffsetPosition(sp.line, sp.column, sp.point,
                                ctx.source.file.file)
    }
  }

  private def annotationsOf(sym: Symbol): Set[xt.Annotation] = sym.annotations.map { annot =>
    xt.Annotation(annot.symbol.fullName.toString, annot.arguments.map(tree => try {
      Some(extractTree(tree)(DefContext()))
    } catch {
      case ex: ImpureCodeEncounteredException =>
        reporter.warning(tree.pos, "Could not extract annotation argument: " + tree)
        None
    }))
  }.toSet

  /** An exception thrown when non-stainless compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(pos: Position, msg: String, ot: Option[tpd.Tree]) extends Exception(msg)

  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: tpd.Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }

  private case class DefContext(
    tparams: Map[Symbol, xt.TypeParameter] = Map(),
    vars: Map[Symbol, () => xt.Variable] = Map(),
    mutableVars: Map[Symbol, () => xt.Variable] = Map(),
    lazyVars: Set[Symbol] = Set(),
    isExtern: Boolean = false
  ) {
    def union(that: DefContext) = {
      copy(this.tparams ++ that.tparams,
           this.vars ++ that.vars,
           this.mutableVars ++ that.mutableVars,
           this.lazyVars ++ that.lazyVars,
           this.isExtern || that.isExtern)
    }

    def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)

    def withNewVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
      copy(vars = vars ++ nvars)
    }

    def withNewVar(nvar: (Symbol, () => xt.Variable)) = {
      copy(vars = vars + nvar)
    }

    def withNewMutableVar(nvar: (Symbol, () => xt.Variable)) = {
      copy(mutableVars = mutableVars + nvar)
    }

    def withNewMutableVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
      copy(mutableVars = mutableVars ++ nvars)
    }

    def isLazy(s: Symbol): Boolean = lazyVars(s)
  }

  private var symbolToIdentifier = Map[Symbol, Identifier]()
  def getIdentifier(sym: Symbol): Identifier = symbolToIdentifier.get(sym) match {
    case Some(id) => id
    case None =>
      val id = FreshIdentifier(sym.name.toString)
      symbolToIdentifier += sym -> id
      id
  }

  // This one never fails, on error, it returns Untyped
  def stainlessType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = {
    try {
      extractType(tpt)
    } catch {
      case e: ImpureCodeEncounteredException =>
        xt.Untyped
    }
  }

  private def extractImports(i: tpd.Import): Seq[xlang.Import] = {
    def selectorChain(t: tpd.Tree): Seq[String] = t match {
      case Select(t2, name) => selectorChain(t2) :+ name.toString
      case Ident(name) => Seq(name.toString)
      case tpd.EmptyTree => Seq.empty
      case _ => outOfSubsetError(t, "Unexpected import selector: " + t)
    }

    val prefix = selectorChain(i.expr)
    val imports = i.selectors.map {
      case Ident(name) => prefix :+ name.toString
      case Pair(Ident(name), _) => prefix :+ name.toString
    }

    imports.map {
      case path :+ "_" => xlang.Import(path, true)
      case p => xlang.Import(p, false)
    }
  }

  def extractPackage(pd: tpd.PackageDef): xlang.PackageDef = {
    var classes: Seq[xt.ClassDef]  = Seq.empty
    var functions: Seq[xt.FunDef]  = Seq.empty
    var imports: Seq[xlang.Import] = Seq.empty
    var subs: Seq[xlang.DefSet]    = Seq.empty

    for (t <- pd.stats) t match {
      case tpd.EmptyTree =>
        // ignore

      case t if annotationsOf(t.symbol) contains xt.Ignore =>
        // ignore

      case vd @ ValDef(_, _, _) if vd.symbol is Module =>
        // ignore

      case i @ Import(_, _) =>
        imports ++= extractImports(i)

      case td @ ExObjectDef() =>
        subs :+= extractObject(td)

      case cd @ ExClassDef() =>
        val (xcd, funs) = extractClass(cd)
        classes :+= xcd
        functions ++= funs

      case p @ PackageDef(_, _) =>
        val xlang.PackageDef(pClasses, pFunctions, pImports, pSubs) = extractPackage(p)
        // TODO: use name??
        classes ++= pClasses
        functions ++= pFunctions
        imports ++= pImports
        subs ++= pSubs

      case other =>
        reporter.warning(other.pos, "Could not extract tree in package: " + other)
    }

    xlang.PackageDef(classes, functions, imports, subs).setPos(pd.pos)
  }

  private def extractObject(td: tpd.TypeDef): xlang.ModuleDef = {
    var classes: Seq[xt.ClassDef]  = Seq.empty
    var functions: Seq[xt.FunDef]  = Seq.empty
    var imports: Seq[xlang.Import] = Seq.empty
    var subs: Seq[xlang.DefSet]    = Seq.empty

    for (d <- td.rhs.asInstanceOf[tpd.Template].body) d match {
      case tpd.EmptyTree =>
        // ignore

      case t if annotationsOf(t.symbol) contains xt.Ignore =>
        // ignore

      case vd @ ValDef(_, _, _) if vd.symbol is Module =>
        // ignore

      case td @ TypeDef(_, _) if td.symbol is Synthetic =>
        // ignore

      case t @ ExSymbol("stainless", "annotation", "package$", "ignore") if t.isInstanceOf[tpd.TypeDef] =>
        // don't extract the `ignore` annotation class

      case i @ Import(_, _) =>
        imports ++= extractImports(i)

      case td @ ExObjectDef() =>
        subs :+= extractObject(td)

      case cd @ ExClassDef() =>
        val (xcd, funs) = extractClass(cd)
        classes :+= xcd
        functions ++= funs

      // Normal function
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        functions :+= extractFunction(fsym, tparams, vparams, rhs)(DefContext(), dd.pos)

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        functions :+= extractFunction(fsym, Seq(), Seq(), rhs)(DefContext(), t.pos)

      // Lazy fields
      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        functions +:= extractFunction(fsym, Seq(), Seq(), rhs)(DefContext(), t.pos)
        // TODO: can't be executed!?

      case other =>
        reporter.warning(other.pos, "Could not extract tree in module: " + other)
    }

    xlang.ModuleDef(classes, functions, imports, subs).setPos(td.pos)
  }

  private def extractClass(td: tpd.TypeDef): (xt.ClassDef, Seq[xt.FunDef]) = {
    val sym = td.symbol
    val id = getIdentifier(sym)

    val tparamsMap = sym.asClass.typeParams.map { sym =>
      sym -> xt.TypeParameter.fresh(sym.showName)
    }

    val parent = sym.info.parents.headOption match {
      case Some(tp @ TypeRef(_, _)) => Some(getIdentifier(tp.symbol))
      case _ => None
    }

    // TODO: checks!!
    /*
      if seenClasses contains parentSym =>
        getClassDef(parentSym, sym.pos) match {
          case acd: AbstractClassDef =>
            val defCtx = DefContext(tparamsMap.toMap)
            val newTps = tps.map(extractType(_)(defCtx, sym.pos))
            val zip = (newTps zip tparamsMap.map(_._2))
            if (newTps.size != tparamsMap.size) {
              outOfSubsetError(sym.pos, "Child classes should have the same number of type parameters as their parent")
              None
            } else if (zip.exists {
              case (TypeParameter(_), _) => false
              case _ => true
            }) {
              outOfSubsetError(sym.pos, "Child class type params should have a simple mapping to parent params")
              None
            } else if (zip.exists {
              case (TypeParameter(id), ctp) => id.name != ctp.id.name
              case _ => false
            }) {
              outOfSubsetError(sym.pos, "Child type params should be identical to parent class's (e.g. C[T1,T2] extends P[T1,T2])")
              None
            } else {
              Some(acd.typed -> acd.tparams)
            }

          case cd =>
            outOfSubsetError(sym.pos, s"Class $id cannot extend ${cd.id}")
            None
        }

      case p =>
        None
    }
    */

    val tparams = tparamsMap.map(t => xt.TypeParameterDef(t._2))
    val tpCtx = DefContext((tparamsMap.map(_._1) zip tparams.map(_.tp)).toMap)

    val flags = annotationsOf(sym).toSet ++ (if (sym is Abstract) Some(xt.IsAbstract) else None)

    val template = td.rhs.asInstanceOf[tpd.Template]
    val args = template.constr.vparamss.flatten
    val fields = args.map { vd =>
      val tpe = stainlessType(vd.tpe)(tpCtx, vd.pos)
      val id = cachedWithOverrides(vd.symbol)
      if (vd.symbol is Mutable) xt.VarDef(id, tpe).setPos(sym.pos)
      else xt.ValDef(id, tpe).setPos(sym.pos)
    }

    // TODO: check!!
    /*
        // checks whether this type definition could lead to an infinite type
        def computeChains(tpe: LeonType): Map[TypeParameterDef, Set[LeonClassDef]] = {
          var seen: Set[LeonClassDef] = Set.empty
          var chains: Map[TypeParameterDef, Set[LeonClassDef]] = Map.empty

          def rec(tpe: LeonType): Set[LeonClassDef] = tpe match {
            case ct: ClassType =>
              val root = ct.classDef.root
              if (!seen(ct.classDef.root)) {
                seen += ct.classDef.root
                for (cct <- ct.root.knownCCDescendants;
                     (tp, tpe) <- cct.classDef.tparams zip cct.tps) {
                  val relevant = rec(tpe)
                  chains += tp -> (chains.getOrElse(tp, Set.empty) ++ relevant)
                  for (cd <- relevant; vd <- cd.fields) {
                    rec(vd.getType)
                  }
                }
              }
              Set(root)

            case Types.NAryType(tpes, _) =>
              tpes.flatMap(rec).toSet
          }

          rec(tpe)
          chains
        }

        val chains = computeChains(ccd.typed)

        def check(tp: TypeParameterDef, seen: Set[LeonClassDef]): Unit = chains.get(tp) match {
          case Some(classDefs) =>
            if ((seen intersect classDefs).nonEmpty) {
              outOfSubsetError(sym.pos, "Infinite types are not allowed")
            } else {
              for (cd <- classDefs; tp <- cd.tparams) check(tp, seen + cd)
            }
          case None =>
        }

        for (tp <- ccd.tparams) check(tp, Set.empty)

      case _ =>
    }
    */

    //println(s"Body of $sym")
    val defCtx = tpCtx.withNewVars((args.map(_.symbol) zip fields.map(vd => () => vd.toVariable)).toMap)

    var invariants: Seq[xt.Expr] = Seq.empty
    var methods: Seq[xt.FunDef] = Seq.empty

    // We collect the methods and fields
    for (d <- template.body) d match {
      case tpd.EmptyTree =>
        // ignore

      case t if (annotationsOf(t.symbol) contains xt.Ignore) || (t.symbol is Synthetic) =>
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

      // Normal methods
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx, dd.pos)

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)

      // Lazy fields
      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)
        // TODO: can't be executed!?

      // Mutable fields
      case t @ ExMutableFieldDef(fsym, _, rhs) =>
        // TODO: is this even allowed!?
        methods :+= extractFunction(fsym, Seq(), Seq(), rhs)(defCtx, t.pos)

      case other =>
        reporter.warning(other.pos, "Could not extract tree in class: " + other)
    }

    val optInv = if (invariants.isEmpty) None else Some {
      new xt.FunDef(FreshIdentifier("inv"), Seq.empty, Seq.empty, xt.BooleanType,
        if (invariants.size == 1) invariants.head else xt.And(invariants),
        Set(xt.IsInvariant)
      )
    }

    val allMethods = methods ++ optInv

    (new xt.ClassDef(
      id,
      tparams,
      parent,
      fields,
      allMethods.map(_.id),
      flags
    ).setPos(sym.pos), allMethods)
  }

  // Returns the parent's method Identifier if sym overrides a symbol, otherwise a fresh Identifier

  private val funOrFieldSymsToIds: MutableMap[Symbol, Identifier] = MutableMap.empty

  private def cachedWithOverrides(sym: Symbol): Identifier = {
    var top = sym
    val cursor = new transform.OverridingPairs.Cursor(sym.owner)
    while (cursor.hasNext) {
      if (cursor.overridden == top) top = cursor.overriding
      cursor.next()
    }

    funOrFieldSymsToIds.getOrElseUpdate(top, {
      FreshIdentifier(sym.name.toString.trim) //trim because sometimes Scala names end with a trailing space, looks nicer without the space
    })
  }

  private def extractFunction(sym: Symbol, tdefs: Seq[tpd.TypeDef], vdefs: Seq[tpd.ValDef], rhs: tpd.Tree)
                             (implicit dctx: DefContext, pos: Position): xt.FunDef = {

    // Type params of the function itself
    val tparams = tdefs.flatMap(td => td.tpe match {
      case tp @ TypeRef(_, _) =>
        val sym = tp.symbol
        Some(sym -> xt.TypeParameter.fresh(sym.name.toString))
      case t =>
        outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
        None
    })

    val tparamsDef = tparams.map(t => xt.TypeParameterDef(t._2))

    val nctx = dctx.copy(tparams = dctx.tparams ++ tparams.toMap)

    val (newParams, fctx) = vdefs.foldLeft((Seq.empty[xt.ValDef], nctx)) { case ((params, dctx), param) =>
      val vd = xt.ValDef(FreshIdentifier(sym.name.toString), stainlessType(param.tpe)(dctx, param.pos)).setPos(sym.pos)
      val expr = () => vd.toVariable /* TODO param match {
        case ByNameTypeTree(_) => () => xt.Application(vd.toVariable, Seq.empty)
        case _ => () => vd.toVariable
      }*/

      (params :+ vd, dctx.withNewVar(param.symbol -> expr))
    }

    val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

    // @mk: We type the identifiers of methods during code extraction because
    // a possible implementing/overriding field will use this same Identifier
    val functionType = {
      val argTypes = newParams map { _.tpe }
      if (argTypes.nonEmpty) xt.FunctionType(argTypes, returnType)
      else returnType
    }

    var flags = annotationsOf(sym).toSet ++ (if (sym is Implicit) Some(xt.IsInlined) else None)

    val id = getIdentifier(sym)

    // If this is a lazy field definition, drop the assignment/ accessing
    val body = if (!(flags contains xt.IsField(true))) rhs else (rhs match {
      case Block(List(Assign(_, realBody)),_ ) => realBody
      case _ => outOfSubsetError(rhs, "Wrong form of lazy accessor")
    })

    val finalBody = try {
      xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
    } catch {
      case e: ImpureCodeEncounteredException =>
        //val pos = if (body0.pos == NoPosition) NoPosition else leonPosToScalaPos(body0.pos.source, funDef.getPos)
        /* TODO
        if (inoxCtx.options.findOptionOrDefault(ExtractionPhase.optStrictCompilation)) {
          reporter.error(pos, "Function "+id.name+" could not be extracted. The function likely uses features not supported by Leon.")
        } else {
          reporter.warning(pos, "Function "+id.name+" is not fully available to Leon.")
        }
        */

        flags += xt.IsAbstract
        xt.NoTree(returnType)
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
      tparamsDef,
      newParams,
      returnType,
      fullBody,
      flags)

    fd.setPos(sym.pos)

    fd
  }

  private def extractTypeParams(tps: Seq[Type]): Seq[(Symbol, xt.TypeParameter)] = tps.flatMap {
    case tp @ TypeRef(_, _) =>
      val sym = tp.symbol
      Some(sym -> xt.TypeParameter.fresh(sym.name.toString))
    case t =>
      outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
      None
  }

  private def extractPattern(p: tpd.Tree, binder: Option[xt.ValDef] = None)(implicit dctx: DefContext): (xt.Pattern, DefContext) = p match {
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

    case s @ Select(_, b) if s.tpe.typeSymbol is (Case | Module) =>
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

    case UnApply(ExSelected("stainless", "lang", "package", "BigInt", "unapply"), _, Seq(Literal(n))) =>
      val lit = xt.IntegerLiteral(BigInt(n.stringValue))
      (xt.LiteralPattern(binder, lit), dctx)

    case ExInt32Literal(i)   => (xt.LiteralPattern(binder, xt.IntLiteral(i)),     dctx)
    case ExBooleanLiteral(b) => (xt.LiteralPattern(binder, xt.BooleanLiteral(b)), dctx)
    case ExUnitLiteral()     => (xt.LiteralPattern(binder, xt.UnitLiteral()),     dctx)
    case ExStringLiteral(s)  => (xt.LiteralPattern(binder, xt.StringLiteral(s)),  dctx)

    case up @ UnApply(s, _, args) =>
      val sym = s.symbol
      val id = getIdentifier(sym)
      val (sub, ctxs) = args.map (extractPattern(_)).unzip

      // TODO: type parameters
      val tps = Seq.empty[xt.Type]

      (xt.UnapplyPattern(binder, id, tps, sub).setPos(up.pos), ctxs.foldLeft(dctx)(_ union _))

    case _ =>
      outOfSubsetError(p, "Unsupported pattern: "+p.getClass)
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

  private def extractTree(tr: tpd.Tree)(implicit dctx: DefContext): xt.Expr = {
    val (current, tmpRest) = tr match {
      case Block(Block(e :: es1, l1) :: es2, l2) =>
        (e, Some(Block(es1 ++ Seq(l1) ++ es2, l2)))
      case Block(e :: Nil, last) =>
        (e, Some(last))
      case Block(e :: es, last) =>
        (e, Some(Block(es, last)))
      case Block(Nil, last) =>
        (last, None)
      case e =>
        (e, None)
    }

    var rest = tmpRest

    val res = current match {
      case ExEnsuring(body, contract) =>
        val post = extractTree(contract)

        val b = extractTreeOrNoTree(body)
        val tpe = extractType(body)

        val closure = post match {
          case l: xt.Lambda => l
          case other =>
            val vd = xt.ValDef(FreshIdentifier("res"), tpe).setPos(post)
            xt.Lambda(Seq(vd), xt.Application(other, Seq(vd.toVariable))).setPos(post)
        }

        xt.Ensuring(b, closure)

      case t @ Apply(ExHolds(body), Seq(proof)) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType).setPos(current.pos)
        val post = xt.Lambda(Seq(vd),
          xt.And(Seq(extractTree(proof), vd.toVariable)).setPos(current.pos)
        ).setPos(current.pos)
        xt.Ensuring(extractTreeOrNoTree(body), post)

      // an optionnal "because" is allowed
      case t @ Apply(ExHolds(body), Seq(Apply(ExSelected("stainless", "lang", "package", "because"), Seq(proof)))) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType).setPos(current.pos)
        val post = xt.Lambda(Seq(vd),
          xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(current.pos)
        ).setPos(current.pos)
        xt.Ensuring(extractTreeOrNoTree(body), post)

      case t @ ExHolds(body) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType).setPos(current.pos)
        val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(current.pos)
        xt.Ensuring(extractTreeOrNoTree(body), post)

      // If the because statement encompasses a holds statement
      case t @ ExBecause(ExHolds(body), proof) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType).setPos(current.pos)
        val post = xt.Lambda(Seq(vd),
          xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(current.pos)
        ).setPos(current.pos)
        xt.Ensuring(extractTreeOrNoTree(body), post)

      case t @ ExComputes(body, expected) =>
        val tpe = extractType(body)
        val vd = xt.ValDef(FreshIdentifier("holds"), tpe).setPos(current.pos)
        val post = xt.Lambda(Seq(vd),
          xt.Equals(vd.toVariable, extractTreeOrNoTree(expected)).setPos(current.pos)
        ).setPos(current.pos)
        xt.Ensuring(extractTreeOrNoTree(body), post)

      /* TODO: By example stuff...
      case t @ ExByExampleExpression(input, output) =>
        val input_expr  =  extractTreeOrNoTree(input).setPos(input.pos)
        val output_expr  =  extractTreeOrNoTree(output).setPos(output.pos)
        Passes(input_expr, output_expr, MatchCase(WildcardPattern(None), Some(BooleanLiteral(false)), NoTree(output_expr.getType))::Nil)

      case t @ ExAskExpression(input, output) =>
        val input_expr  =  extractTreeOrNoTree(input).setPos(input.pos)
        val output_expr = extractTreeOrNoTree(output).setPos(output.pos)

        val resId = FreshIdentifier("res", output_expr.getType).setPos(current.pos)
        val post = Lambda(Seq(xt.ValDef(resId)),
            Passes(input_expr, Variable(resId), MatchCase(WildcardPattern(None), Some(BooleanLiteral(false)), NoTree(output_expr.getType))::Nil)).setPos(current.pos)

        Ensuring(output_expr, post)
      */

      case t @ Apply(Select(
        Apply(ExSelected("stainless", "lang", "package", "StringDecorations"), Seq(str)),
        ExNamed("bigLength")), Seq()
      ) => xt.StringLength(extractTree(str).setPos(str.pos))

      case t @ Apply(Select(
        Apply(ExSelected("stainless", "lang", "package", "StringDecorations"), Seq(str)),
        ExNamed("bigSubstring")
      ), startTree :: rest) =>
        val start = extractTree(startTree).setPos(startTree.pos)
        rest match {
          case Seq() =>
            val vd = xt.ValDef(FreshIdentifier("s"), xt.StringType).setPos(str.pos)
            xt.Let(vd, extractTreeOrNoTree(str),
              xt.SubString(vd.toVariable, start,
                xt.StringLength(vd.toVariable).setPos(t.pos)
              ).setPos(t.pos))
          case Seq(endTree) =>
            xt.SubString(extractTreeOrNoTree(str), start, extractTreeOrNoTree(endTree))
          case _ => outOfSubsetError(t, "Unknown \"bigSubstring\" call: " + t)
        }

      case ExAssert(contract, oerr) =>
        val const = extractTree(contract)
        val b     = rest.map(extractTreeOrNoTree).getOrElse(xt.UnitLiteral().setPos(current.pos))

        rest = None

        xt.Assert(const, oerr, b)

      case ExRequire(contract) =>
        val pre = extractTree(contract)
        val b   = rest.map(extractTreeOrNoTree).getOrElse(xt.UnitLiteral().setPos(current.pos))

        rest = None

        xt.Require(pre, b)

      /* TODO: passes stuff...
      case ExPasses(in, out, cases) =>
        val ine = extractTree(in)
        val oute = extractTree(out)
        val rc = cases.map(extractMatchCase)

        // @mk: FIXME: this whole sanity checking is very dodgy at best.
        val ines = unwrapTuple(ine, ine.isInstanceOf[Tuple]) // @mk We untuple all tuples
        ines foreach {
          case v @ Variable(_) if currentFunDef.params.map{ _.toVariable } contains v =>
          case LeonThis(_) =>
          case other => ctx.reporter.fatalError(other.getPos, "Only i/o variables are allowed in i/o examples")
        }
        oute match {
          case Variable(_) => // FIXME: this is not strict enough, we need the bound variable of enclosing Ensuring
          case other => ctx.reporter.fatalError(other.getPos, "Only i/o variables are allowed in i/o examples")
        }
        passes(ine, oute, rc)
        */

      case Apply(TypeApply(ExSelected("scala", "Array", "apply"), Seq(tpt)), args) =>
        xt.FiniteArray(args.map(extractTree), extractType(tpt))

      case s @ Select(_, _) if s.tpe.typeSymbol is ModuleClass =>
        extractType(s) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, Seq.empty)
          case tpe => outOfSubsetError(tr, "Unexepected class constructor type: " + tpe)
        }

      case ExTuple(args) =>
        xt.Tuple(args.map(extractTree))

      case Apply(TypeApply(ExSelected("stainless", "lang", "error"), Seq(tpt)), Seq(Literal(cnst))) =>
        xt.Error(extractType(tpt), cnst.stringValue)

      case ExTupleSelect(tuple, i) =>
        xt.TupleSelect(extractTree(tuple), i)

      case v @ ValDef(name, tpt, _) =>
        val vd = if (!v.symbol.is(Mutable)) {
          xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)).setPos(v.pos)
        } else {
          xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)).setPos(v.pos)
        }

        val restTree = rest.map(rst => extractTree(rst) {
          if (!v.symbol.is(Mutable)) {
            dctx.withNewVar(v.symbol -> (() => vd.toVariable))
          } else {
            dctx.withNewMutableVar(v.symbol -> (() => vd.toVariable))
          }
        }).getOrElse(xt.UnitLiteral().setPos(current.pos))

        rest = None

        xt.Let(vd, extractTree(v.rhs), restTree)

      /* TODO: LetDefs
      case d @ ExFunctionDef(sym, tparams, params, ret, b) =>
        val fd = defineFunDef(sym)

        val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

        fd.addFlags(annotationsOf(d.symbol).map { case (name, args) => FunctionFlag.fromName(name, args) }.toSet)

        val newDctx = dctx.copy(tparams = dctx.tparams ++ tparamsMap)

        val restTree = rest match {
          case Some(rst) => extractTree(rst)
          case None => UnitLiteral()
        }
        rest = None

        val oldCurrentFunDef = currentFunDef

        val funDefWithBody = extractFunction(fd, params, b)(newDctx)

        currentFunDef = oldCurrentFunDef

        val (other_fds, block) = restTree match {
          case LetDef(fds, block) =>
            (fds, block)
          case _ =>
            (Nil, restTree)
        }
        letDef(funDefWithBody +: other_fds, block)
        */

      // FIXME case ExDefaultValueFunction

      /**
       * XLang Extractors
       */

      case a @ Assign(id @ Ident(_), rhs) =>
        dctx.mutableVars.get(id.symbol) match {
          case Some(fun) =>
            xt.Assignment(fun().setPos(id.pos), extractTree(rhs))

          case None =>
            outOfSubsetError(a, "Undeclared variable.")
        }

      case ExWhile(cond, body) => xt.While(extractTree(cond),
        xt.Block(body.map(extractTree), xt.UnitLiteral().setPos(current.pos)).setPos(current.pos),
        None
      )

      case Apply(Select(
        Apply(ExSelected("stainless", "lang", "while2Invariant"), Seq(w @ ExWhile(cond, body))),
        ExNamed("invariant")
      ), Seq(pred)) => xt.While(extractTree(cond),
        xt.Block(body.map(extractTree), xt.UnitLiteral().setPos(w.pos)).setPos(w.pos),
        Some(extractTree(pred))
      )

      /* TODO: epsilons
      case epsi @ ExEpsilonExpression(tpt, varSym, predBody) =>
        val pstpe = extractType(tpt)
        val nctx = dctx.withNewVar(varSym -> (() => EpsilonVariable(epsi.pos, pstpe)))
        val c1 = extractTree(predBody)(nctx)
        if(containsEpsilon(c1)) {
          outOfSubsetError(epsi, "Usage of nested epsilon is not allowed")
        }
        Epsilon(c1, pstpe)
      */

      case Apply(Select(lhs @ ExSymbol("scala", "Array"), ExNamed("update")), Seq(index, value)) =>
        xt.ArrayUpdate(extractTree(lhs), extractTree(index), extractTree(value))

      case ExBigIntLiteral(Literal(cnst)) =>
        xt.IntegerLiteral(BigInt(cnst.stringValue))

      case Apply(ExSelected("math", "BigInt", "int2bigInt"), Seq(t)) => extractTree(t) match {
        case xt.IntLiteral(n) => xt.IntegerLiteral(BigInt(n))
        case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
      }

      case ExRealLiteral(args) => args.map(extractTree) match {
        case Seq(xt.IntegerLiteral(n), xt.IntegerLiteral(d)) => xt.FractionLiteral(n, d)
        case Seq(xt.IntegerLiteral(n)) => xt.FractionLiteral(n, 1)
        case _ => outOfSubsetError(tr, "Real not built from literals")
      }

      case ExInt32Literal(v) =>
        xt.IntLiteral(v)

      case ExBooleanLiteral(v) =>
        xt.BooleanLiteral(v)

      case ExUnitLiteral() =>
        xt.UnitLiteral()

      case Apply(TypeApply(ExSelected("scala", "Predef", "locally"), _), Seq(body)) =>
        extractTree(body)

      case Typed(e, _) =>
        // TODO: refine type here?
        extractTree(e)

      case ex @ ExIdentifier(sym, tpt) =>
        dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
          case Some(builder) =>
            builder().setPos(ex.pos)
          case None =>
            xt.FunctionInvocation(getIdentifier(sym), Seq.empty, Seq.empty)
        }

      /* TODO: holes
      case hole @ ExHoleExpression(tpt, exprs) =>
        Hole(extractType(tpt), exprs.map(extractTree))

      case ops @ ExWithOracleExpression(oracles, body) =>
        val newOracles = oracles map { case (tpt, sym) =>
          val aTpe  = extractType(tpt)
          val oTpe  = oracleType(ops.pos, aTpe)
          val newID = FreshIdentifier(sym.name.toString, oTpe)
          newID
        }

        val newVars = (oracles zip newOracles).map {
          case ((_, sym), id) =>
            sym -> (() => Variable(id))
        }

        val cBody = extractTree(body)(dctx.withNewVars(newVars))

        WithOracle(newOracles, cBody)
      */

      case Apply(TypeApply(ExSelected("stainless", "lang", "synthesis", "choose"), Seq(tpt)), Seq(pred)) =>
        extractTree(pred) match {
          case xt.Lambda(Seq(vd), body) => xt.Choose(vd, body)
          case e => extractType(tpt) match {
            case xt.FunctionType(Seq(argType), xt.BooleanType) =>
              val vd = xt.ValDef(FreshIdentifier("x", true), argType).setPos(pred.pos)
              xt.Choose(vd, xt.Application(e, Seq(vd.toVariable)).setPos(pred.pos))
            case _ => outOfSubsetError(tr, "Expected choose to take a function-typed predicate")
          }
        }

      case Block(Seq(dd @ DefDef(_, _, Seq(vparams), _, _)), Closure(Nil, call, targetTpt)) if call.symbol == dd.symbol =>
        val vds = vparams map (vd => xt.ValDef(
          FreshIdentifier(vd.symbol.name.toString),
          extractType(vd.tpt)
        ).setPos(vd.pos))

        xt.Lambda(vds, extractTree(dd.rhs)(dctx.withNewVars((vparams zip vds).map {
          case (v, vd) => v.symbol -> (() => vd.toVariable)
        })))

      case Apply(TypeApply(ExSelected("stainless", "lang", "forall"), types), Seq(fun)) =>
        extractTree(fun) match {
          case xt.Lambda(vds, body) => xt.Forall(vds, body)
          case _ => outOfSubsetError(tr, "Expected forall to take a lambda predicate")
        }

      case Apply(TypeApply(
        ExSelected("Map", "apply") | ExSelected("stainless", "lang", "Map", "apply"),
        Seq(tptFrom, tptTo)
      ), args) =>
        val to = extractType(tptTo)
        val pairs = args map {
          case ExTuple(Seq(from, to)) =>
            (extractTree(from), extractTree(to))
          case e =>
            val ex = extractTree(e)
            (xt.TupleSelect(ex, 1).setPos(e.pos), xt.TupleSelect(ex, 2).setPos(e.pos))
        }

        val somePairs = pairs.map { case (key, value) =>
          key -> xt.ClassConstructor(
            xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(value),
            Seq(value)
          ).setPos(value)
        }

        val dflt = xt.ClassConstructor(
          xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(current.pos),
          Seq.empty
        ).setPos(current.pos)

        xt.FiniteMap(somePairs, dflt, extractType(tptFrom))

      case Apply(TypeApply(
        ExSelected("Set", "apply") | ExSelected("stainless", "lang", "Set", "apply"),
        Seq(tpt)
      ), args) => xt.FiniteSet(args.map(extractTree), extractType(tpt))

      case Apply(TypeApply(
        ExSelected("Bag", "apply") | ExSelected("stainless", "lang", "Bag", "apply"),
        Seq(tpt)
      ), args) => xt.FiniteBag(args.map {
        case ExTuple(Seq(key, value)) =>
          (extractTree(key), extractTree(value))
        case e =>
          val ex = extractTree(e)
          (xt.TupleSelect(ex, 1).setPos(e.pos), xt.TupleSelect(ex, 2).setPos(e.pos))
      }, extractType(tpt))

      case Apply(Select(New(tpt), nme.CONSTRUCTOR), args) =>
        extractType(tpt) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, args.map(extractTree))
          case _ => outOfSubsetError(tr, "Construction of a non-class type")
        }

      case Select(e, nme.UNARY_!) => xt.Not(extractTree(e))
      case Select(e, nme.UNARY_-) => xt.UMinus(extractTree(e))
      case Select(e, nme.UNARY_~) => xt.BVNot(extractTree(e))

      case Apply(Select(l, nme.NE), Seq(r)) => xt.Not(
        xt.Equals(extractTree(l), extractTree(r)).setPos(current.pos)
      )

      case Apply(Select(l, nme.EQ), Seq(r)) => xt.Equals(extractTree(l), extractTree(r))

      case Apply(Apply(Apply(TypeApply(
        ExSelected("scala", "Array", "fill"),
        Seq(baseType)
      ), Seq(length)), Seq(dflt)), _) =>
        xt.LargeArray(Map.empty, extractTree(dflt), extractTree(length))

      case If(t1,t2,t3) =>
        xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

      case TypeApply(s @ Select(t, _), Seq(tpt)) if s.symbol == defn.Any_asInstanceOf =>
        extractType(tpt) match {
          case ct: xt.ClassType => xt.AsInstanceOf(extractTree(t), ct)
          case _ => outOfSubsetError(tr, "asInstanceOf can only cast to class types")
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
        TypeApply(Select(Apply(ExSelected("scala", "Predef", s), Seq(lhs)), ExNamed("updated")), _),
        Seq(index, value)
      ), Seq(Apply(_, _))) if s.toString contains "Array" =>
        xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))

      case Apply(TypeApply(ExSelected("stainless", "collection", "List", "apply"), Seq(tpt)), args) =>
        val tpe = extractType(tpt)
        val cons = xt.ClassType(getIdentifier(consSymbol), Seq(tpe))
        val nil  = xt.ClassType(getIdentifier(nilSymbol),  Seq(tpe))
        args.foldRight(xt.ClassConstructor(nil, Seq.empty).setPos(current.pos)) {
          case (e, ls) => xt.ClassConstructor(cons, Seq(extractTree(e), ls)).setPos(e.pos)
        }

      case ExCharLiteral(c) => xt.CharLiteral(c)
      case ExStringLiteral(s) => xt.StringLiteral(s)

      case Apply(Select(
        Apply(ExSelected("stainless", "lang", "package", "BooleanDecorations"), Seq(lhs)),
        ExNamed("$eq$eq$greater")
      ), Seq(rhs)) => xt.Implies(extractTree(lhs), extractTree(rhs))

      case Apply(tree, args) if defn.isFunctionType(tree.tpe) =>
        xt.Application(extractTree(tree), args map extractTree)

      case ExCall(rec, sym, tps, args) => rec match {
        case None =>
          xt.FunctionInvocation(getIdentifier(sym), tps.map(extractType), args.map(extractTree))

        case Some(lhs) => extractType(lhs) match {
          case ct: xt.ClassType =>
            if (sym.is(Method)) {
              xt.MethodInvocation(extractTree(lhs), getIdentifier(sym), tps map extractType, args map extractTree)
            } else (args match {
              case Seq() => xt.ClassSelector(extractTree(lhs), getIdentifier(sym))
              case Seq(rhs) => xt.FieldAssignment(extractTree(lhs), getIdentifier(sym), extractTree(rhs))
              case _ => outOfSubsetError(tr, "Unexpected call")
            })

          case tpe => (tpe, sym.name.decode.toString, args) match {
            // TODO: string converters, concat, and stuff...
            case (xt.StringType, "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
            case (xt.IntegerType | xt.BVType(_) | xt.RealType, "+", Seq(rhs)) => xt.Plus(extractTree(lhs), extractTree(rhs))

            case (xt.SetType(_), "+",  Seq(rhs)) => xt.SetAdd(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "++", Seq(rhs)) => xt.SetUnion(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "&",  Seq(rhs)) => xt.SetIntersection(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "--", Seq(rhs)) => xt.SetDifference(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "subsetOf", Seq(rhs)) => xt.SubsetOf(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "contains", Seq(rhs)) => xt.ElementOfSet(extractTree(rhs), extractTree(lhs))

            case (xt.BagType(_), "+",   Seq(rhs)) => xt.BagAdd(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "++",  Seq(rhs)) => xt.BagUnion(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "&",   Seq(rhs)) => xt.BagIntersection(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "--",  Seq(rhs)) => xt.BagDifference(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "get", Seq(rhs)) => xt.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

            case (xt.ArrayType(_), "apply",   Seq(rhs))          => xt.ArraySelect(extractTree(lhs), extractTree(rhs))
            case (xt.ArrayType(_), "length",  Seq())             => xt.ArrayLength(extractTree(lhs))
            case (xt.ArrayType(_), "updated", Seq(index, value)) => xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))
            case (xt.ArrayType(_), "clone",   Seq())             => extractTree(lhs)

            // TODO: maps ??

            case (_, "-",   Seq(rhs)) => xt.Minus(extractTree(lhs), extractTree(rhs))
            case (_, "*",   Seq(rhs)) => xt.Times(extractTree(lhs), extractTree(rhs))
            case (_, "%",   Seq(rhs)) => xt.Remainder(extractTree(lhs), extractTree(rhs))
            case (_, "mod", Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
            case (_, "/",   Seq(rhs)) => xt.Division(extractTree(lhs), extractTree(rhs))
            case (_, ">",   Seq(rhs)) => xt.GreaterThan(extractTree(lhs), extractTree(rhs))
            case (_, ">=",  Seq(rhs)) => xt.GreaterEquals(extractTree(lhs), extractTree(rhs))
            case (_, "<",   Seq(rhs)) => xt.LessThan(extractTree(lhs), extractTree(rhs))
            case (_, "<=",  Seq(rhs)) => xt.LessEquals(extractTree(lhs), extractTree(rhs))

            case (_, "|",   Seq(rhs)) => xt.BVOr(extractTree(lhs), extractTree(rhs))
            case (_, "&",   Seq(rhs)) => xt.BVAnd(extractTree(lhs), extractTree(rhs))
            case (_, "^",   Seq(rhs)) => xt.BVXor(extractTree(lhs), extractTree(rhs))
            case (_, "<<",  Seq(rhs)) => xt.BVShiftLeft(extractTree(lhs), extractTree(rhs))
            case (_, ">>",  Seq(rhs)) => xt.BVAShiftRight(extractTree(lhs), extractTree(rhs))
            case (_, ">>>", Seq(rhs)) => xt.BVLShiftRight(extractTree(lhs), extractTree(rhs))

            case (_, "&&",  Seq(rhs)) => xt.And(extractTree(lhs), extractTree(rhs))
            case (_, "||",  Seq(rhs)) => xt.Or(extractTree(lhs), extractTree(rhs))

            case (tpe, name, args) =>
              outOfSubsetError(tr, "Unknown call to " + name +
                s" on $lhs (${extractType(lhs)}) with arguments $args of type ${args.map(a => extractType(a))}")
          }
        }
      }

      // default behaviour is to complain :)
      case _ =>
        outOfSubsetError(tr, "Could not extract as PureScala (Scala tree of type "+tr.getClass+")")
    }

    res.setPos(current.pos)

    rest match {
      case Some(r) =>
        xt.exprOps.flattenBlocks(xt.Block(Seq(res), extractTree(r)).setPos(current.pos))
      case None =>
        res
    }
  }

  private def extractType(t: tpd.Tree)(implicit dctx: DefContext): xt.Type = {
    extractType(t.tpe)(dctx, t.pos)
  }

  private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = tpt match {
    case tpe if tpe == defn.CharType    => xt.CharType
    case tpe if tpe == defn.IntType     => xt.Int32Type
    case tpe if tpe == defn.BooleanType => xt.BooleanType
    case tpe if tpe == defn.UnitType    => xt.UnitType
    case tpe if tpe == defn.NothingType => xt.Untyped

    case tpe if isBigIntSym(tpe.typeSymbol) => xt.IntegerType
    case tpe if isRealSym(tpe.typeSymbol)   => xt.RealType
    case tpe if isStringSym(tpe.typeSymbol) => xt.StringType

    case ct: ConstantType => extractType(ct.value.tpe)

    /*
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
    */

    case defn.FunctionOf(from, to) if from.size >= 1 =>
      xt.FunctionType(from map extractType, extractType(to))

    /*
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
    */

    case AnnotatedType(tpe, _) => extractType(tpe)

    case _ =>
      if (tpt ne null) {
        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type as PureScala: "+tpt+" ("+tpt.getClass+")")
      } else {
        outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
      }
  }
}
