/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import dotty.tools.dotc.transform.SymUtils._
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

import scala.collection.mutable.{ Map => MutableMap }
import scala.collection.immutable.ListMap
import scala.language.implicitConversions

class CodeExtraction(inoxCtx: inox.Context, cache: SymbolsContext)(using override val ctx: Context)
  extends ASTExtractors {

  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  lazy val reporter = inoxCtx.reporter

  given givenDebugSection: inox.DebugSection = frontend.DebugSectionExtraction

  implicit def dottyPosToInoxPos(p: Position): inox.utils.Position = scala.util.Try({
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
  }).toOption.getOrElse(inox.utils.NoPosition)

  private def getParam(sym: Symbol): SymbolIdentifier = cache fetchParam sym

  private def getIdentifier(sym: Symbol): SymbolIdentifier = cache fetch sym

  private def annotationsOf(sym: Symbol, ignoreOwner: Boolean = false): Seq[xt.Flag] = {
    getAnnotations(sym, ignoreOwner = ignoreOwner)
      .filter { case (name, _) => !name.startsWith("isabelle") }
      .map { case (name, args) =>
        xt.extractFlag(name, args.map(extractTree(_)(DefContext())))
    }
  }

  def outOfSubsetError(pos: Position, msg: String): Nothing =
    throw new frontend.UnsupportedCodeException(dottyPosToInoxPos(pos), msg)

  def outOfSubsetError(t: tpd.Tree, msg: String): Nothing = outOfSubsetError(t.pos, msg)

  private case class DefContext(
    tparams: ListMap[Symbol, xt.TypeParameter] = ListMap(),
    vars: Map[Symbol, () => xt.Expr] = Map(),
    mutableVars: Map[Symbol, () => xt.Variable] = Map(),
    localFuns: Map[Symbol, (Identifier, Seq[xt.TypeParameterDef], xt.FunctionType)] = Map(),
    localClasses: Map[Identifier, xt.LocalClassDef] = Map(),
    depParams: Map[TermName, xt.ValDef] = Map(),
    isExtern: Boolean = false,
    resolveTypes: Boolean = false,
    wrappingArithmetic: Boolean = false,
  ) {
    def union(that: DefContext) = {
      copy(
        this.tparams ++ that.tparams,
        this.vars ++ that.vars,
        this.mutableVars ++ that.mutableVars,
        this.localFuns ++ that.localFuns,
        this.localClasses ++ that.localClasses,
        this.depParams ++ that.depParams,
        this.isExtern || that.isExtern,
        this.resolveTypes || that.resolveTypes,
        this.wrappingArithmetic || that.wrappingArithmetic,
      )
    }

    def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)

    def withNewTypeParams(ntparams: Traversable[(Symbol, xt.TypeParameter)]) = {
      copy(tparams = tparams ++ ntparams)
    }

    def withNewTypeParam(tparam: (Symbol, xt.TypeParameter)) = {
      copy(tparams = tparams + tparam)
    }

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

    def withLocalFun(sym: Symbol, id: Identifier, tparams: Seq[xt.TypeParameterDef], tpe: xt.FunctionType) = {
      copy(localFuns = this.localFuns + (sym -> ((id, tparams, tpe))))
    }

    def withLocalClass(lcd: xt.LocalClassDef) = {
      copy(localClasses = this.localClasses + (lcd.id -> lcd))
    }

    def withDepParams(dps: Traversable[(TermName, xt.ValDef)]) = {
      copy(depParams = depParams ++ dps)
    }

    def setResolveTypes(resolveTypes: Boolean) = {
      copy(resolveTypes = resolveTypes)
    }

    def setWrappingArithmetic(wrappingArithmetic: Boolean) = {
      copy(wrappingArithmetic = wrappingArithmetic)
    }

    def withExtern(extern: Boolean) = {
      copy(isExtern = isExtern || extern)
    }
  }

  // This one never fails, on error, it returns Untyped
  private def stainlessType(tpt: Type)(using DefContext, Position): xt.Type = {
    try {
      extractType(tpt)
    } catch {
      case e: frontend.UnsupportedCodeException =>
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
    Seq[Identifier],
    Seq[xt.ModuleDef],
    Seq[xt.ClassDef],
    Seq[xt.FunDef],
    Seq[xt.TypeDef],
  ) = {
    given DefContext = DefContext()

    var imports   : Seq[xt.Import]    = Seq.empty
    var classes   : Seq[Identifier]   = Seq.empty
    var functions : Seq[Identifier]   = Seq.empty
    var typeDefs  : Seq[Identifier]   = Seq.empty
    var subs      : Seq[xt.ModuleDef] = Seq.empty

    var allClasses   : Seq[xt.ClassDef] = Seq.empty
    var allFunctions : Seq[xt.FunDef]   = Seq.empty
    var allTypeDefs  : Seq[xt.TypeDef]  = Seq.empty

    for (d <- stats) d match {
      case tpd.EmptyTree =>
        // ignore

      case t if (
        annotationsOf(t.symbol).contains(xt.Ignore) ||
        (t.symbol.is(Synthetic) && !canExtractSynthetic(t.symbol))
      ) =>
        // ignore

      case vd @ ValDef(_, _, _) if vd.symbol is Module =>
        // ignore

      case t @ ExSymbol("stainless", "annotation", "ignore") if t.isInstanceOf[tpd.TypeDef] =>
        // don't extract the `ignore` annotation class

      case i @ Import(_, _) =>
        imports ++= extractImports(i)

      case pd @ PackageDef(ref, stats) =>
        val (imports, classes, functions, typeDefs, modules, newClasses, newFunctions, newTypeDefs) = extractStatic(stats)
        subs :+= xt.ModuleDef(extractRef(ref), imports, classes, functions, typeDefs, modules)
        allClasses ++= newClasses
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case td @ ExObjectDef() =>
        val (obj, newClasses, newFunctions, newTypeDefs) = extractObject(td)
        subs :+= obj
        allClasses ++= newClasses
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case cd @ ExClassDef() =>
        val (xcd, newFunctions, newTypeDefs) = extractClass(cd)
        classes :+= xcd.id
        allClasses :+= xcd
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      // Normal function
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        val fd = extractFunction(fsym, dd, tparams, vparams, rhs)
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExMutableFieldDef(fsym, _, _) if annotationsOf(fsym).contains(xt.Extern) =>
        // Ignore @extern variables in static context

      case t @ ExMutableFieldDef(fsym, _, _) =>
        outOfSubsetError(t, "Non-@extern variables are only allowed within functions and constructor parameters")

      // Normal fields
      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, t, Seq(), Seq(), rhs)
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExTypeDef() =>
        val td = extractTypeDef(t)
        typeDefs :+= td.id
        allTypeDefs :+= td

      case t if t.symbol is Synthetic =>
        // ignore

      case td: tpd.TypeDef =>
        // ignore

      case t @ ExMutableFieldDef(_, _, _) =>
        outOfSubsetError(t, "Mutable fields in static containers such as objects are not supported")

      case other =>
        reporter.warning(other.pos, s"Stainless does not support the following tree in static containers:\n$other")
    }

    (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs)
  }

  private def extractTypeDef(td: tpd.TypeDef)(using dctx: DefContext): xt.TypeDef = {
    val sym = td.symbol
    val id = getIdentifier(sym)
    val flags = annotationsOf(sym)

    val (tparams, body, isAbstract) = td.rhs match {
      case LambdaTypeTree(tparams, body) =>
        val typeParamsSymbols = typeParamSymbols(tparams)
        val typeParams = extractTypeParams(typeParamsSymbols)
        val tpCtx = dctx.withNewTypeParams(typeParamsSymbols zip typeParams)
        val typeBody = extractType(body)(using tpCtx)
        (typeParams, typeBody, false)

      case TypeBoundsTree(lo, hi) =>
        val (loType, hiType) = (extractType(lo), extractType(hi))
        (Seq.empty, xt.TypeBounds(loType, hiType, Seq.empty), true)

      case tpt =>
        val tpe =
          if (tpt.symbol is Opaque)
            tpt.symbol.typeRef.translucentSuperType
          else
            tpt.tpe

        (Seq.empty, extractType(tpt, tpe), false)
    }

    // Opaque types are referenced from their opaque right-hand side for some reason.
    val realId = if (td.rhs.symbol is Opaque) getIdentifier(td.rhs.symbol) else id

    new xt.TypeDef(
      realId,
      tparams.map(xt.TypeParameterDef(_)),
      body,
      flags ++ (if (isAbstract) Seq(xt.IsAbstract) else Seq.empty)
    )
  }

  private def extractObject(td: tpd.TypeDef): (xt.ModuleDef, Seq[xt.ClassDef], Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val template = td.rhs.asInstanceOf[tpd.Template]
    if (template.parents.exists(isValidParent(_))) {
      outOfSubsetError(td, "Objects cannot extend classes or implement traits, use a case object instead")
    }

    val (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs) = extractStatic(template.body)

    val module = xt.ModuleDef(
      getIdentifier(td.symbol),
      imports,
      classes,
      functions,
      typeDefs,
      subs
    ).setPos(td.pos)

    (module, allClasses, allFunctions, allTypeDefs)
  }

  private def isValidParentType(parent: Type, inLibrary: Boolean = false): Boolean = parent match {
    case tpe if tpe.typeSymbol == defn.AnyClass => false
    case tpe if tpe.typeSymbol == defn.AnyValClass => false
    case tpe if tpe.typeSymbol == defn.ObjectClass => false
    case tpe if tpe.typeSymbol == defn.ThrowableClass && inLibrary => false
    // case tpe if tpe.typeSymbol == defn.EnumClass => false
    case tpe if defn.isProductClass(tpe.classSymbol) => false
    case tpe if defn.isProductSubType(tpe) => false
    case tpe if defn.isProductClass(tpe.typeSymbol) => false
    case tpe if defn.isFunctionClass(tpe.typeSymbol) => false
    case tpe => true
  }

  private def isValidParent(parent: tpd.Tree, inLibrary: Boolean = false): Boolean =
    isValidParentType(parent.tpe, inLibrary)

  private def extractClass(td: tpd.TypeDef)(using dctx: DefContext): (xt.ClassDef, Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val sym = td.symbol
    val id = getIdentifier(sym)
    val template = td.rhs.asInstanceOf[tpd.Template]

    val isValueClass = template.parents.exists(_.tpe.typeSymbol == defn.AnyValClass)

    val annots = annotationsOf(sym)
    val flags = annots ++
      (if (isValueClass) Some(xt.ValueClass) else None) ++
      (if ((sym is Abstract) || (sym is Trait)) Some(xt.IsAbstract) else None) ++
      (if (sym is Sealed) Some(xt.IsSealed) else None) ++
      (if ((sym is ModuleClass) && (sym is Case)) Some(xt.IsCaseObject) else None)

    val extparams = extractTypeParams(sym.asClass.typeParams)(DefContext())
    val defCtx = dctx.copy(tparams = dctx.tparams ++ (sym.asClass.typeParams zip extparams))

    val classType = xt.ClassType(id, extparams)

    val inLibrary = flags exists (_.name == "library")
    val parents = template.parents
      .filter(isValidParent(_, inLibrary))
      .map(p => extractType(p.tpe)(defCtx.setResolveTypes(true), p.pos))
      .map {
        case ct: xt.ClassType => ct
        case lct: xt.LocalClassType => lct.toClassType
      }

    if (parents.length > 1) {
       outOfSubsetError(td.pos, s"Stainless supports only simple type hierarchies: Classes can only inherit from a single class/trait")
     }

    def isField(vd: tpd.ValDef) = {
      !vd.symbol.is(Accessor) && vd.symbol.is(ParamAccessor)
    }

    val vdTpts = template.constr.vparamss.flatten.map(_.tpt).toVector

    val vds = template.body
      .collect {
        case vd: tpd.ValDef if isField(vd) => vd
      }
      .zipWithIndex
      .map { case (vd, i) => (vd, vdTpts(i)) }

    val fields = vds map { case (vd, tpt) =>
      val vdSym = vd.symbol
      val id = getIdentifier(vdSym)
      val tpe = extractType(tpt, vd.tpe)(defCtx)
      val flags = annotationsOf(vdSym, ignoreOwner = true)

      val (isExtern, isPure) = (flags contains xt.Extern, flags contains xt.IsPure)
      val isMutable = (vdSym is Mutable) || isExtern && !isPure

      isMutable match {
        case true  => xt.VarDef(id, tpe, flags).setPos(vd.pos)
        case false => xt.ValDef(id, tpe, flags).setPos(vd.pos)
      }
    }

    val fieldsMap = vds.zip(fields).map {
      case ((vd, _), field) => (vd.symbol, field.tpe)
    }.toMap

    val hasExternFields = fields.exists(_.flags.contains(xt.Extern))

    var invariants: Seq[xt.Expr] = Seq.empty
    var methods: Seq[xt.FunDef] = Seq.empty
    var typeMembers: Seq[xt.TypeDef] = Seq.empty

    // We collect the methods and fields
    for ((d, i) <- template.body.zipWithIndex) d match {
      case tpd.EmptyTree =>
        // ignore

      case i: tpd.Import =>
        // ignore

      case t if t.symbol.is(Synthetic) && !canExtractSynthetic(t.symbol) =>
        // ignore

      case t if annotationsOf(t.symbol).contains(xt.Ignore) && !(t.symbol is CaseAccessor) =>
        // ignore

      case t @ ExMutableFieldDef(_, _, rhs) if rhs != tpd.EmptyTree =>
        outOfSubsetError(t, "Mutable fields in traits cannot have a default value")

      case vd @ ValDef(_, _, _) if (
        (vd.symbol is Mutable) && !(vd.symbol is CaseAccessor) &&
        !(vd.symbol.owner is Abstract) && !(vd.symbol.owner is Trait)
      ) =>
        outOfSubsetError(vd.pos, "Vars are not allowed in class bodies in Stainless.")

      case vd @ ValDef(_, _, _) if (
        (vd.symbol is Mutable) && !(vd.symbol is CaseAccessor) &&
        ((vd.symbol.owner is Abstract) || (vd.symbol.owner is Trait))
      ) =>
        methods :+= extractFunction(vd.symbol, vd, Seq.empty, Seq.empty, tpd.EmptyTree)(defCtx)

      case dd @ DefDef(nme.CONSTRUCTOR, _, _, _, _) =>
        // ignore

      case td @ TypeDef(_, _) if td.symbol is Param =>
        // ignore

      case cd @ ExClassDef() =>
        outOfSubsetError(cd.pos, "Classes can only be defined at the top-level, within objects, or within methods")

      // Class invariants
      case ExRequire(body, isStatic) =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
        invariants :+= wrap(extractTree(body)(defCtx))

      // We cannot extract copy method if the class has extern fields as
      // the type of copy and the getters mention what might be a type we
      // cannot extract.
      case t @ ExFunctionDef(fsym, _, _, _, _)
        if hasExternFields && (isCopyMethod(fsym) || isDefaultGetter(fsym)) =>
          () // ignore

      // Normal methods
      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        methods :+= extractFunction(fsym, dd, tparams, vparams, rhs)(defCtx)

      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, t, Seq.empty, Seq.empty, rhs)(defCtx)
        // this case split doesn't appear to be necessary in scalac extraction (always false?)
        if (fsym is Lazy)
          methods :+= fd.copy(flags = fd.flags)
        else
          methods :+= fd.copy(flags = fd.flags :+ xt.FieldDefPosition(i))

      case t @ ExFieldAccessorFunction(fsym, _, vparams, rhs) if flags.contains(xt.IsAbstract) =>
        methods :+= extractFunction(fsym, t, Seq.empty, vparams, rhs)(defCtx)

      case t @ ExFieldAccessorFunction(fsym, _, vparams, rhs) =>
        val fieldTpe = fieldsMap(fsym.accessedFieldOrGetter)
        methods :+= extractFieldAccessor(fsym, fieldTpe, classType, vparams)(defCtx)

      case t @ ExLazyFieldAccessorFunction(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, t, Seq.empty, Seq.empty, rhs)(defCtx)

      case vd @ ValDef(_, _, _) if isField(vd) =>
        val fieldTpe = fieldsMap(vd.symbol)
        methods :+= extractFieldAccessor(vd.symbol, fieldTpe, classType, Seq.empty)(defCtx)

      case td @ TypeDef(_, _) if !td.isClassDef =>
        typeMembers :+= extractTypeDef(td)(defCtx)

      case d if d.symbol is Synthetic =>
        // ignore

      case d if d.symbol is Mutable =>
        // ignore

      case other =>
        reporter.warning(other.pos, s"In class $id, Stainless does not support:\n$other")
    }

    val optInv = if (invariants.isEmpty) None else Some {
      val invId = cache fetchInvIdForClass sym
      val pos = inox.utils.Position.between(invariants.map(_.getPos).min, invariants.map(_.getPos).max)
      new xt.FunDef(invId, Seq.empty, Seq.empty, xt.BooleanType().setPos(pos),
        if (invariants.size == 1) invariants.head else xt.And(invariants).setPos(pos),
        (Seq(xt.IsInvariant) ++ annots.filterNot(_ == xt.IsMutable)).distinct
      ).setPos(pos)
    }

    val cd = new xt.ClassDef(
      id,
      extparams.map(xt.TypeParameterDef(_)),
      parents,
      fields,
      flags
    ).setPos(sym.pos)

    val allMethods = (methods ++ optInv).map(fd => fd.copy(flags = fd.flags :+ xt.IsMethodOf(id)))
    val allTypeMembers = typeMembers.map(td => td.copy(flags = td.flags :+ xt.IsTypeMemberOf(id)))

    (cd, allMethods, allTypeMembers)
  }

  private def extractFunction(
    sym: Symbol,
    tree: tpd.ValOrDefDef,
    tdefs: Seq[tpd.TypeDef],
    vdefs: Seq[tpd.ValDef],
    rhs: tpd.Tree,
    typeParams: Option[Seq[xt.TypeParameter]] = None
  )(using dctx: DefContext): xt.FunDef = {
    val id = getIdentifier(sym)

    // Type params of the function itself
    val extparams = typeParamSymbols(tdefs)
    val ntparams = typeParams.getOrElse(extractTypeParams(extparams))

    val isAbstract = rhs == tpd.EmptyTree

    var flags = annotationsOf(sym).filterNot(annot => annot == xt.IsMutable || annot.name == "inlineInvariant") ++
      (if ((sym is Implicit) && (sym is Synthetic)) Seq(xt.Inline, xt.Synthetic) else Seq()) ++
      (if (sym is Inline) Seq(xt.Inline) else Seq()) ++
      (if (sym is Private) Seq(xt.Private) else Seq()) ++
      (if (sym is Final) Seq(xt.Final) else Seq()) ++
      (if (!isAbstract && ((sym.isField) || (sym is Lazy))) Seq(xt.IsField(sym is Lazy)) else Seq()) ++
      (if (isDefaultGetter(sym) || isCopyMethod(sym)) Seq(xt.Synthetic, xt.Inline) else Seq()) ++
      (if ((isAbstract && sym.isField) || (!(sym is Lazy) && (sym is Accessor)))
        Seq(xt.IsAccessor(Option(getIdentifier(sym.underlyingSymbol)).filterNot(_ => isAbstract)))
      else Seq())

    val nctx = dctx.copy(
      tparams = dctx.tparams ++ (extparams zip ntparams),
      isExtern = flags contains xt.Extern,
    )

    val (newParams, fctx) = vdefs.foldLeft((Seq.empty[xt.ValDef], nctx)) { case ((params, dctx), param) =>
      val flags = annotationsOf(param.symbol, ignoreOwner = true)

      val tctx = dctx.withExtern(nctx.isExtern || flags.contains(xt.Extern))
      val tpe = stainlessType(param.tpe)(tctx, param.tpt.pos)
      val ptpe = extractType(param.tpt, param.tpe)(tctx)

      val vd = xt.ValDef(getIdentifier(param.symbol), ptpe, flags).setPos(param.pos)
      val expr = param.tpt match {
        case ByNameTypeTree(_) => () => xt.Application(vd.toVariable, Seq()).setPos(param.tpt.pos)
        case _ => () => vd.toVariable
      }

      (params :+ vd, dctx.withNewVar(param.symbol -> expr))
    }

    if (sym.name == nme.unapply) {
      val isEmptyDenot = typer.Applications.extractorMember(sym.info.finalResultType, nme.isEmpty)
      val getDenot = typer.Applications.extractorMember(sym.info.finalResultType, nme.get)
      flags :+= xt.IsUnapply(getIdentifier(isEmptyDenot.symbol), getIdentifier(getDenot.symbol))
    }

    lazy val retType = extractType(tree.tpt, sym.info.finalResultType)(fctx)

    val (finalBody, returnType) = if (isAbstract) {
      flags :+= xt.IsAbstract
      (xt.NoTree(retType).setPos(rhs.pos), retType)
    } else {
      val fullBody = xt.exprOps.flattenBlocks(extractTreeOrNoTree(rhs)(fctx))
      val localClasses = xt.exprOps.collect[xt.LocalClassDef] {
        case xt.LetClass(lcds, _) => lcds.toSet
        case _ => Set()
      } (fullBody)

      if (localClasses.isEmpty) (fullBody, retType)
      else {
        // If the function contains local classes, we need to add those to the context in order to type its body.
        val tctx = localClasses.toSeq.foldLeft(fctx)(_ withLocalClass _)
        val returnType = extractType(tree.tpt, sym.info.finalResultType)(tctx)
        val bctx = fctx.copy(localClasses = fctx.localClasses ++ tctx.localClasses)
        (xt.exprOps.flattenBlocks(extractTreeOrNoTree(rhs)(bctx)), returnType)
      }
    }

    object KeywordChecker extends xt.StainlessSelfTreeTraverser {
      override def traverse(e: xt.Expr) = {
        e match {
          case _: xt.Require =>
            reporter.warning(e.getPos, s"This require is ignored for verification because it is not at the top-level of this @extern function.")
          case _: xt.Ensuring =>
            reporter.warning(e.getPos, s"This ensuring is ignored for verification because it is not at the top-level of this @extern function.")
          case _ =>
            ()
        }
        super.traverse(e)
      }
    }

    val fullBody = if (fctx.isExtern) {
      xt.exprOps.withoutSpecs(finalBody) foreach { KeywordChecker.traverse }
      xt.exprOps.withBody(finalBody, xt.NoTree(returnType).setPos(rhs.pos))
    } else {
      finalBody
    }

    new xt.FunDef(
      id,
      ntparams.map(tp => xt.TypeParameterDef(tp)),
      newParams,
      returnType,
      fullBody,
      flags.distinct
    ).setPos(sym.pos)
  }

  private def extractFieldAccessor(
    sym: Symbol,
    fieldTpe: xt.Type,
    classType: xt.ClassType,
    vdefs: Seq[tpd.ValDef]
  )(using dctx: DefContext): xt.FunDef = {
    val field = getIdentifier(sym.accessedFieldOrGetter)
    val thiss = xt.This(classType).setPos(sym.pos)

    val args = vdefs map { vd =>
      val id = getIdentifier(vd.symbol)
      val flags = annotationsOf(vd.symbol, ignoreOwner = true)
      xt.ValDef(id, fieldTpe, flags).setPos(vd.pos)
    }

    val (id, returnType, body) = if (sym.isSetter) {
      assert(args.length == 1)

      (
        getIdentifier(sym),
        xt.UnitType().setPos(sym.pos),
        xt.FieldAssignment(thiss, field, args.head.toVariable).setPos(sym.pos)
      )
    } else { // getter
      assert(args.isEmpty)

      (
        getParam(sym),
        fieldTpe,
        xt.ClassSelector(thiss, field).setPos(sym.pos)
      )
    }

    val flags = annotationsOf(sym).filterNot(_ == xt.IsMutable) ++
      (if (sym is Private) Seq(xt.Private) else Seq()) ++
      (if (sym is Final) Seq(xt.Final) else Seq()) ++
      (if (sym is Synthetic) Seq(xt.Synthetic) else Seq()) ++
      Seq(xt.IsAccessor(Some(field)))

    val bodyOrEmpty = if (flags.contains(xt.Extern)) {
      xt.exprOps.withBody(body, xt.NoTree(returnType).setPos(sym.pos))
    } else {
      body
    }

    new xt.FunDef(
      id,
      Seq.empty,
      args,
      returnType,
      bodyOrEmpty,
      flags.distinct
    ).setPos(sym.pos)
  }

  private def typeParamSymbols(tdefs: Seq[tpd.TypeDef]): Seq[Symbol] = tdefs.flatMap(_.tpe match {
    case tp @ TypeRef(_, _) =>
      Some(tp.symbol)
    case t =>
      outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
      None
  })

  private def extractTypeParams(syms: Seq[Symbol])(using dctx: DefContext): Seq[xt.TypeParameter] = {
    syms.foldLeft((dctx, Seq[xt.TypeParameter]())) { case ((dctx, tparams), sym) =>
      val variance =
        if (sym is Covariant) Some(xt.Variance(true))
        else if (sym is Contravariant) Some(xt.Variance(false))
        else None

      val bounds = sym.info match {
        case TypeBounds(lo, hi) =>
          val (loType, hiType) = (extractType(lo)(dctx, sym.pos), extractType(hi)(dctx, sym.pos))
          if (loType != xt.NothingType() || hiType != xt.AnyType()) Some(xt.Bounds(loType, hiType))
          else None
        case _ => None
      }

      val flags = annotationsOf(sym, ignoreOwner = true)
      val tp = xt.TypeParameter(getIdentifier(sym), flags ++ variance.toSeq ++ bounds).setPos(sym.pos)
      (dctx.copy(tparams = dctx.tparams + (sym -> tp)), tparams :+ tp)
    }._2
  }

  private def extractPattern(p: tpd.Tree, binder: Option[xt.ValDef] = None)(using dctx: DefContext): (xt.Pattern, DefContext) = p match {
    case b @ Bind(name, t @ Typed(pat, tpt)) =>
      val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(b.symbol)).setPos(b.pos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(t, Some(vd))(pctx)

    case b @ Bind(name, pat) =>
      val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(b), annotationsOf(b.symbol)).setPos(b.pos)
      val pctx = dctx.withNewVar(b.symbol -> (() => vd.toVariable))
      extractPattern(pat, Some(vd))(pctx)

    case t @ Typed(Ident(nme.WILDCARD), tpt) =>
      extractType(tpt)(dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          (xt.InstanceOfPattern(binder, ct).setPos(p.pos), dctx)

        case lt =>
          outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
      }

    case Ident(nme.WILDCARD) =>
      (xt.WildcardPattern(binder).setPos(p.pos), dctx)

    case s @ Select(_, b) if s.tpe.widenDealias.typeSymbol is (Case | Module) =>
      // case Obj =>
      extractType(s)(dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
        case _ =>
          outOfSubsetError(s, "Invalid instance pattern: "+s)
      }

    case id @ Ident(_) if id.symbol is (Case | Module) =>
      extractType(id)(dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
        case _ =>
          outOfSubsetError(id, "Invalid instance pattern: "+id)
      }

    case a @ Apply(fn, args) =>
      extractType(a)(dctx.setResolveTypes(true)) match {
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
        val id = getIdentifier(sym)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.UnapplyPattern(binder, Seq(), id, tps, subPatterns).setPos(t.pos), nctx)
      }

    case UnApply(f, _, pats) =>
      val (subPatterns, subDctx) = pats.map(extractPattern(_)).unzip
      val nctx = subDctx.foldLeft(dctx)(_ union _)

      val sym = f.symbol
      if (sym.owner.exists && TupleSymbol.unapply(sym.owner.companionClass).isDefined) {
        (xt.TuplePattern(binder, subPatterns), nctx)
      } else if (sym.owner.exists && sym.owner.is(Synthetic) &&
          sym.owner.companionClass.exists && sym.owner.companionClass.is(Case)) {
        val id = getIdentifier(sym.owner.companionClass)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.ClassPattern(binder, xt.ClassType(id, tps).setPos(p.pos), subPatterns).setPos(p.pos), nctx)
      } else {
        val id = getIdentifier(sym)
        val tps = f match { case TypeApply(un, tps) => tps map extractType case _ => Seq.empty }
        (xt.UnapplyPattern(binder, Seq(), id, tps, subPatterns).setPos(p.pos), nctx)
      }

    case _ =>
      outOfSubsetError(p, "Unsupported pattern: "+p)
  }

  private def extractMatchCase(cd: tpd.CaseDef)(using dctx: DefContext): xt.MatchCase = {
    val (recPattern, ndctx) = extractPattern(cd.pat)
    val recBody             = extractTree(cd.body)(ndctx)

    if (cd.guard == tpd.EmptyTree) {
      xt.MatchCase(recPattern, None, recBody).setPos(cd.pos)
    } else {
      val recGuard = extractTree(cd.guard)(ndctx)
      xt.MatchCase(recPattern, Some(recGuard), recBody).setPos(cd.pos)
    }
  }

  private def extractTreeOrNoTree(tr: tpd.Tree)(using dctx: DefContext): xt.Expr = {
    try {
      extractTree(tr)
    } catch {
      case e: frontend.UnsupportedCodeException =>
        if (dctx.isExtern) {
          xt.NoTree(extractType(tr)).setPos(tr.pos)
        } else {
          throw e
        }
    }
  }

  private def extractSeq(args: Seq[tpd.Tree])(using dctx: DefContext): Seq[xt.Expr] = args match {
    case Seq(SeqLiteral(es, _)) =>
      es.map(extractTree)
    case Seq(Typed(SeqLiteral(es, _), tpt)) if tpt.tpe.typeSymbol == defn.RepeatedParamClass =>
      es.map(extractTree)
    case _ =>
      args.map(extractTree)
  }

  private def extractBlock(es: List[tpd.Tree])(using dctx: DefContext): xt.Expr = {
    val fctx = es.collect {
      case ExFunctionDef(sym, tparams, vparams, tpt, rhs) => (sym, tparams, vparams)
    }.foldLeft(dctx) { case (dctx, (sym, tparams, vparams)) =>
      val extparams = typeParamSymbols(tparams)
      val ntparams = extractTypeParams(extparams)(dctx)
      val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams))

      val tparamDefs = ntparams.map(tp => xt.TypeParameterDef(tp).copiedFrom(tp))

      val tpe = xt.FunctionType(
        vparams.map { param =>
          val tpe = stainlessType(param.tpe)(nctx, param.tpt.pos)
          param.tpt match {
            case ByNameTypeTree(_) => xt.FunctionType(Seq(), tpe).setPos(param.tpt.pos)
            case _ => tpe
          }
        },
        stainlessType(sym.info.finalResultType)(nctx, sym.pos)
      ).setPos(sym.pos)

      dctx.withLocalFun(sym, getIdentifier(sym), tparamDefs, tpe)
    }

    val (vds, vctx) = es.collect {
      case v @ ValDef(name, tpt, _) => (v.symbol, name, tpt)
    }.foldLeft((Map.empty[Symbol, xt.ValDef], fctx)) { case ((vds, dctx), (sym, name, tpt)) =>
      if (sym is Mutable) {
        val vd = xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
        (vds + (sym -> vd), dctx.withNewMutableVar((sym, () => vd.toVariable)))
      } else {
        val laziness = if (sym is Lazy) Some(xt.Lazy) else None
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true) ++ laziness).setPos(sym.pos)
        (vds + (sym -> vd), dctx.withNewVar((sym, () => vd.toVariable)))
      }
    }

    val (lcds, cctx) = es.collect {
      case cd @ ExClassDef() => cd
    }.foldLeft((Map.empty[Symbol, xt.LocalClassDef], vctx)) { case ((lcds, dctx), cd) =>
      val (xcd, methods, typeDefs) = extractClass(cd)(dctx)
      val lcd = xt.LocalClassDef(xcd, methods, typeDefs)
      (lcds + (cd.symbol -> lcd), dctx.withLocalClass(lcd))
    }

    def rec(es: List[tpd.Tree]): xt.Expr = es match {
      case Nil => xt.UnitLiteral()

      case (i: tpd.Import) :: xs => rec(xs)

      case (e @ ExAssert(contract, oerr, isStatic)) :: xs =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

        val const = extractTree(contract)(cctx)
        val b     = rec(xs)
        xt.Assert(wrap(const), oerr, b).setPos(e.pos)

      case (e @ ExRequire(contract, isStatic)) :: xs =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

        val pre = extractTree(contract)(cctx)
        val b   = rec(xs)
        xt.Require(wrap(pre), b).setPos(e.pos)

      case (e @ ExDecreases(ranks)) :: xs =>
        val measure = xt.tupleWrap(ranks.map(extractTree(_)(cctx)))
        val b       = rec(xs)
        xt.Decreases(measure, b).setPos(e.pos)

      case (d @ ExFunctionDef(sym, tparams, params, ret, b)) :: xs =>
        val (id, tdefs, _) = cctx.localFuns(sym)
        val fd = extractFunction(sym, d, tparams, params, b, typeParams = Some(tdefs.map(_.tp)))(cctx)
        val letRec = xt.LocalFunDef(id, tdefs, fd.params, fd.returnType, fd.fullBody, fd.flags).setPos(d.pos)

        rec(xs) match {
          case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body).setPos(d.pos)
          case other => xt.LetRec(Seq(letRec), other).setPos(d.pos)
        }

      case (cd @ ExClassDef()) :: xs =>
        val lcd = lcds(cd.symbol)

        // Drop companion object and/or synthetic modules Dotty inserts after local class declarations
        val rest = xs.dropWhile(x => x.symbol.is(Synthetic) && x.symbol.is(Module))
        rec(rest) match {
          case xt.LetClass(defs, body) => xt.LetClass(lcd +: defs, body).setPos(cd.pos)
          case other => xt.LetClass(Seq(lcd), other).setPos(cd.pos)
        }

      case (v @ ValDef(name, tpt, _)) :: xs =>
        if (v.symbol is Mutable) {
          xt.LetVar(vds(v.symbol), extractTree(v.rhs)(cctx), rec(xs)).setPos(v.pos)
        } else {
          xt.Let(vds(v.symbol), extractTree(v.rhs)(cctx), rec(xs)).setPos(v.pos)
        }

      case ExWhileWithInvariant(cond, body, pred) :: xs =>
        val wh = xt.While(extractTree(cond)(cctx), extractTree(body)(cctx), Some(extractTree(pred)(cctx))).setPos(es.head.pos)
        rec(xs) match {
          case xt.Block(elems, last) => xt.Block(wh +: elems, last).setPos(es.head.pos)
          case e => xt.Block(Seq(wh), e).setPos(es.head.pos)
        }

      case ExWhile(cond, body) :: xs =>
        val wh = xt.While(extractTree(cond)(cctx), extractTree(body)(cctx), None).setPos(es.head.pos)
        rec(xs) match {
          case xt.Block(elems, last) => xt.Block(wh +: elems, last).setPos(es.head.pos)
          case e => xt.Block(Seq(wh), e).setPos(es.head.pos)
        }

      case x :: Nil =>
        extractTree(x)(cctx)

      case (x @ Block(_, _)) :: rest =>
        val re = rec(rest)
        val (elems, last) = re match {
          case xt.Block(elems, last) => (elems, last)
          case e => (Seq(), e)
        }

        extractTree(x)(cctx) match {
          case xt.Decreases(m, b) => xt.Decreases(m, xt.Block(b +: elems, last).setPos(re)).setPos(x.pos)
          case xt.Require(pre, b) => xt.Require(pre, xt.Block(b +: elems, last).setPos(re)).setPos(x.pos)
          case b => xt.Block(b +: elems, last).setPos(x.pos)
        }

      case x :: rest =>
        rec(rest) match {
          case xt.Block(elems, last) =>
            xt.Block(extractTree(x)(cctx) +: elems, last).setPos(x.pos)
          case e =>
            xt.Block(Seq(extractTree(x)(cctx)), e).setPos(x.pos)
        }
    }

    rec(es)
  }

  private def extractArgs(sym: Symbol, args: Seq[tpd.Tree])(using dctx: DefContext): Seq[xt.Expr] = {
    (args zip sym.info.paramInfoss.flatten) map {
      case (arg, ExprType(_)) => xt.Lambda(Seq(), extractTree(arg)).setPos(arg.pos)
      case (arg, _) => extractTree(arg)
    }
  }

  private def extractTree(tr: tpd.Tree)(using dctx: DefContext): xt.Expr = (tr match {
    case SingletonTypeTree(tree) => extractTree(tree)

    case ExLambda(vparams, rhs) =>
      val vds = vparams map (vd => xt.ValDef(
        FreshIdentifier(vd.symbol.name.toString),
        extractType(vd.tpt),
        annotationsOf(vd.symbol)
      ).setPos(vd.pos))

      xt.Lambda(vds, extractTree(rhs)(dctx.withNewVars((vparams zip vds).map {
        case (v, vd) => v.symbol -> (() => vd.toVariable)
      })))

    case Block(es, e) =>
      val b = extractBlock(es :+ e)
      xt.exprOps.flattenBlocks(b)

    case Try(body, cses, fin) =>
      val rb = extractTree(body)
      val rc = cses.map(extractMatchCase)
      xt.Try(rb, rc, if (fin == tpd.EmptyTree) None else Some(extractTree(fin)))

    case Apply(ex, Seq(arg)) if ex.symbol == defn.throwMethod =>
      xt.Throw(extractTree(arg))

    case Ident(_) if tr.tpe.signature.resSig.toString startsWith "scala.collection.immutable.Nil" =>
      outOfSubsetError(tr.pos, "Scala's List API is not directly supported, please use `stainless.lang.collection.List that defines supported List operations.")

    case ExIdentity(body) =>
      extractTree(body)

    case w @ ExWhileWithInvariant(cond, body, pred) =>
      xt.While(extractTree(cond), extractTree(body), Some(extractTree(pred))).setPos(w.pos)

    case w @ ExWhile(cond, body) =>
      xt.While(extractTree(cond), extractTree(body), None).setPos(w.pos)

    case ExAssert(contract, oerr, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
      xt.Assert(wrap(extractTree(contract)), oerr, xt.UnitLiteral().setPos(tr.pos))

    case ExRequire(contract, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
      xt.Require(wrap(extractTree(contract)), xt.UnitLiteral().setPos(tr.pos))

    case ExUnwrapped(tree) if tree ne tr => extractTree(tree)

    case ExEnsuring(body, contract, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

      val post = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      xt.Ensuring(b, post match {
        case l: xt.Lambda => l.copy(body = wrap(l.body)).copiedFrom(l)
        case other =>
          val tpe = extractType(tr)
          val vd = xt.ValDef.fresh("res", tpe).setPos(post)
          xt.Lambda(Seq(vd), wrap(extractType(contract) match {
            case xt.BooleanType() => post
            case _ => xt.Application(other, Seq(vd.toVariable)).setPos(post)
          })).setPos(post)
      })

    case ExThrowing(body, contract) =>
      val pred = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      xt.Throwing(b, pred match {
        case l: xt.Lambda => l
        case other =>
          val tpe = extractType(exceptionSym.info)(dctx, contract.pos)
          val vd = xt.ValDef.fresh("res", tpe).setPos(other)
          xt.Lambda(Seq(vd), xt.Application(other, Seq(vd.toVariable)).setPos(other)).setPos(other)
      })

    case t @ ExHoldsBecause(body, proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case t @ ExHolds(body, proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case t @ ExHolds(body) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    // If the because statement encompasses a holds statement
    case t @ ExBecause(ExHolds(body), proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.And(Seq(extractTreeOrNoTree(proof), vd.toVariable)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case t @ ExComputes(body, expected) =>
      val tpe = extractType(body)
      val vd = xt.ValDef.fresh("holds", tpe).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd),
        xt.Equals(vd.toVariable, extractTreeOrNoTree(expected)).setPos(tr.pos)
      ).setPos(tr.pos)
      xt.Ensuring(extractTreeOrNoTree(body), post).setPos(post)

    case ExPasses(in, out, cases) =>
      val ine = extractTree(in)
      val oute = extractTree(out)
      val rc = cases.map(extractMatchCase)

      xt.Passes(ine, oute, rc)

    case ExError(str, tpt) => xt.Error(extractType(tpt), str)

    case ExOld(e) => xt.Old(extractTree(e))

    case ExSnapshot(e) => xt.Snapshot(extractTree(e))

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
          val vd = xt.ValDef.fresh("s", xt.StringType().setPos(str.pos)).setPos(str.pos)
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

    /**
     * XLang Extractors
     */

    case a @ Assign(id @ Ident(_), rhs) =>
      dctx.mutableVars.get(id.symbol) match {
        case Some(fun) =>
          xt.Assignment(fun().setPos(id.pos), extractTree(rhs))

        case None => id.tpe match {
          case TermRef(tt: ThisType, _) =>
            val thiss = extractType(tt)(dctx, id.pos) match {
              case ct: xt.ClassType => xt.This(ct)
              case lct: xt.LocalClassType => xt.LocalThis(lct)
            }
            xt.FieldAssignment(thiss.setPos(id.pos), getIdentifier(id.symbol), extractTree(rhs))

          case _ =>
            outOfSubsetError(a, "Undeclared variable.")
        }
      }

    case a @ ExFieldAssign(sym, lhs, rhs) =>
      import dotty.tools.dotc.core.NameOps._
      val fieldName = sym.underlyingSymbol.name.asTermName.setterName
      val d = sym.owner.info.decl(fieldName)
      def setter = d.suchThat(_.info.firstParamTypes.nonEmpty).symbol

      extractType(lhs)(dctx.setResolveTypes(true)) match {
        case ct: xt.ClassType =>
          xt.MethodInvocation(extractTree(lhs), getIdentifier(setter), Seq.empty, Seq(extractTree(rhs))).setPos(a.pos)

        case lct: xt.LocalClassType =>
          val lcd = dctx.localClasses(lct.id)
          val id = getIdentifier(setter)
          val funType = xt.FunctionType(Seq(extractType(rhs)), xt.UnitType())
          xt.LocalMethodInvocation(
            extractTree(lhs),
            xt.ValDef(id, funType).toVariable,
            Seq.empty,
            Seq.empty,
            Seq(extractTree(rhs))
          ).setPos(a.pos)
      }

    case ExBigIntLiteral(Literal(cnst)) =>
      xt.IntegerLiteral(BigInt(cnst.stringValue))

    case ExBigIntLiteral(_) => outOfSubsetError(tr, "Only literal arguments are allowed for BigInt.")

    case Apply(ExSymbol("scala", "math", "BigInt$", "int2bigInt"), Seq(t)) => extractTree(t) match {
      case xt.Int32Literal(n) => xt.IntegerLiteral(BigInt(n))
      case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
    }

    case ExWrapping(tree) =>
      val body = extractTree(tree)(dctx.setWrappingArithmetic(true))
      xt.Annotated(body, Seq(xt.Wrapping))

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

    case ExTyped(ExSymbol("scala", "Predef$", "$qmark$qmark$qmark" | "???"), tpe) =>
      xt.NoTree(extractType(tpe))

    case Typed(e, _) =>
      extractTree(e)

    case Inlined(call, members, body) =>
      def rec(expr: xt.Expr): xt.Expr = expr match {
        case xt.Let(vd, e, b) => xt.Let(vd, e, rec(b)).copiedFrom(expr)
        case xt.LetRec(fds, b) => xt.LetRec(fds, rec(b)).copiedFrom(expr)
        case xt.Decreases(_, _) =>
          outOfSubsetError(tr, "No measure should be specified on inlined functions")
        case xt.Require(pre, b) =>
          xt.Assert(pre, Some("Inlined precondition"), rec(b)).copiedFrom(expr)
        case xt.Ensuring(b, xt.Lambda(Seq(vd), post)) =>
          xt.Let(vd, rec(b), xt.Assume(post, vd.toVariable).copiedFrom(expr)).copiedFrom(expr)
        case xt.NoTree(_) =>
          outOfSubsetError(tr, "Can't inline empty body")
        case _ =>
          xt.annotated(expr, xt.Unchecked)
      }

      rec(extractBlock(members :+ body))

    case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "choose"), Seq(tpt)), Seq(pred)) =>
      extractTree(pred) match {
        case xt.Lambda(Seq(vd), body) => xt.Choose(vd, body)
        case e => extractType(tpt) match {
          case xt.FunctionType(Seq(argType), xt.BooleanType()) =>
            val vd = xt.ValDef.fresh("x", argType, true).setPos(pred.pos)
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
          xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(value),
          Seq(value)
        ).setPos(value)
      }

      val dflt = xt.ClassConstructor(
        xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
        Seq.empty
      ).setPos(tr.pos)

      val optTo = xt.ClassType(getIdentifier(optionSymbol), Seq(to))
      xt.FiniteMap(somePairs, dflt, extractType(tptFrom), optTo)

    case Apply(TypeApply(
      ExSymbol("stainless", "lang", "Set$", "apply"),
      Seq(tpt)
    ), args) => xt.FiniteSet(extractSeq(args), extractType(tpt))

    case Apply(TypeApply(
      ExSymbol("stainless", "lang", "MutableMap$", "withDefaultValue"),
      Seq(tptFrom, tptTo)
    ), Seq(default)) =>
      xt.MutableMapWithDefault(extractType(tptFrom), extractType(tptTo), extractTree(default))

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
      case (lit @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit), e)
      case (e, xt.IntegerType(), lit @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit))
      case _ => injectCasts(xt.Equals)(l, r)
    }).setPos(tr.pos))

    case Apply(Select(l, nme.EQ), Seq(r)) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (lit @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit), e)
      case (e, xt.IntegerType(), lit @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(lit.toBigInt).copiedFrom(lit))
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
        case lct: xt.LocalClassType => xt.LocalThis(lct)
        case _ => outOfSubsetError(t, "Invalid usage of `this`")
      }

    case s @ Super(_, _) =>
      extractType(s) match {
        case ct: xt.ClassType => xt.Super(ct)
        case lct: xt.LocalClassType => xt.Super(lct.toClassType)
        case _ => outOfSubsetError(s, s"Invalid usage of `super`")
      }

    case Apply(Apply(
      TypeApply(Select(Apply(ExSymbol("scala", "Predef$", s), Seq(lhs)), ExNamed("updated")), _),
      Seq(index, value)
    ), Seq(Apply(_, _))) if s.toString contains "Array" =>
      xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))

    case Select(Apply(ExSymbol("scala", "Predef$", s), Seq(lhs)), ExNamed("size"))
         if s.toString contains "Array" =>
      xt.ArrayLength(extractTree(lhs))

    case Apply(TypeApply(ExSymbol("stainless", "collection", "List$", "apply"), Seq(tpt)), args) =>
      val tpe = extractType(tpt)
      val cons = xt.ClassType(getIdentifier(consSymbol), Seq(tpe))
      val nil  = xt.ClassType(getIdentifier(nilSymbol),  Seq(tpe))
      extractSeq(args).foldRight(xt.ClassConstructor(nil, Seq.empty).setPos(tr.pos)) {
        case (e, ls) => xt.ClassConstructor(cons, Seq(e, ls)).setPos(e)
      }

    case ExCharLiteral(c) => xt.CharLiteral(c)
    case ExStringLiteral(s) => xt.StringLiteral(s)

    case Apply(Select(
      lhs @ ExSymbol("stainless", "lang", "package$", "BooleanDecorations"),
      ExNamed("==>") | ExNamed("$eq$eq$greater")
    ), Seq(rhs)) => xt.Implies(extractTree(lhs), extractTree(rhs))

    case app @ Apply(tree, args) if defn.isFunctionType(tree.tpe) =>
      xt.Application(extractTree(tree), args map extractTree).setPos(app.pos)

    case NamedArg(name, arg) => extractTree(arg)

    case ExConstructor(tpe, args) => extractType(tpe)(dctx, tr.pos) match {
      case lct: xt.LocalClassType => xt.LocalClassConstructor(lct, args map extractTree)
      case ct: xt.ClassType => xt.ClassConstructor(ct, args map extractTree)
      case tt: xt.TupleType => xt.Tuple(args map extractTree)
      case _ => outOfSubsetError(tr, "Unexpected constructor " + tr)
    }

    case ex @ ExIdentifier(sym, tpt) if dctx.vars contains sym => dctx.vars(sym)().setPos(ex.pos)
    case ex @ ExIdentifier(sym, tpt) if dctx.mutableVars contains sym => dctx.mutableVars(sym)().setPos(ex.pos)

    case ExSymbol("scala", "Predef$", "$qmark$qmark$qmark" | "???") => xt.NoTree(extractType(tr))

    case ExThisCall(tt, sym, tps, args) =>
      val id = if (sym is ParamAccessor) getParam(sym) else getIdentifier(sym)

      extractType(tt)(dctx, tr.pos) match {
        case ct: xt.ClassType =>
          val thiss = xt.This(ct).setPos(tr.pos)
          xt.MethodInvocation(thiss, id, tps map extractType, extractArgs(sym, args)).setPos(tr.pos)

        case lct: xt.LocalClassType =>
          val thiss = xt.LocalThis(lct).setPos(tr.pos)
          val lcd = dctx.localClasses(lct.id)
          val fd = lcd.methods.find(_.id == id).get
          xt.LocalMethodInvocation(
            thiss,
            xt.ValDef(id, xt.FunctionType(fd.params.map(_.tpe), fd.returnType)).toVariable.setPos(tr.pos),
            fd.tparams.map(_.tp),
            tps.map(extractType),
            extractArgs(sym, args)
          ).setPos(tr.pos)
      }

    case ExCastCall(expr, from, to) =>
      // Double check that we are dealing with regular integer types
      val xt.BVType(true, size) = extractType(from)(dctx, NoPosition)
      val newType @ xt.BVType(true, newSize) = extractType(to)(dctx, NoPosition)
      if (size > newSize) xt.BVNarrowingCast(extractTree(expr), newType)
      else                xt.BVWideningCast(extractTree(expr), newType)

    case ExCall(rec, sym, tps, args) => rec match {
      case Some(Select(rec @ Super(_, _), m)) if (sym is Abstract) && m != nme.CONSTRUCTOR =>
        outOfSubsetError(tr.pos, "Cannot issue a super call to an abstract method.")

      case None if (sym.owner is ModuleClass) && (sym.owner is Case) =>
        val ct = extractType(sym.owner.thisType)(dctx, tr.pos).asInstanceOf[xt.ClassType]
        xt.MethodInvocation(
          xt.This(ct).setPos(tr.pos),
          getIdentifier(sym),
          tps map extractType,
          args map extractTree
        ).setPos(tr.pos)

      case None =>
        dctx.localFuns.get(sym) match {
          case None =>
            xt.FunctionInvocation(getIdentifier(sym), tps map extractType, extractArgs(sym, args)).setPos(tr.pos)
          case Some((id, tparams, tpe)) =>
            xt.ApplyLetRec(id, tparams.map(_.tp), tpe, tps map extractType, extractArgs(sym, args)).setPos(tr.pos)
        }

      case Some(lhs) => xt.exprOps.stripAnnotations(extractType(lhs)(dctx.setResolveTypes(true))) match {
        case ct: xt.ClassType =>
          val id = if (sym is ParamAccessor) getParam(sym) else getIdentifier(sym)
          xt.MethodInvocation(extractTree(lhs), id, tps map extractType, extractArgs(sym, args)).setPos(tr.pos)

        case lct: xt.LocalClassType =>
          val lcd = dctx.localClasses(lct.id)

          val id = if (sym is ParamAccessor) getParam(sym) else getIdentifier(sym)
          val fd = lcd.methods.find(_.id == id).get

          xt.LocalMethodInvocation(
            extractTree(lhs),
            xt.ValDef(id, xt.FunctionType(fd.params.map(_.tpe), fd.returnType)).toVariable,
            fd.tparams.map(_.tp),
            tps.map(extractType),
            extractArgs(sym, args)
          ).setPos(tr.pos)

        case ft: xt.FunctionType =>
          xt.Application(extractTree(lhs), args.map(extractTree)).setPos(ft)

        case pi: xt.PiType =>
          xt.Application(extractTree(lhs), args.map(extractTree)).setPos(pi)

        case tpe => (tpe, sym.name.decode.toString, args) match {
          case (xt.StringType(), "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
          case (xt.IntegerType() | xt.BVType(_,_) | xt.RealType(), "+", Seq(rhs)) => injectCasts(xt.Plus)(lhs, rhs)

          case (xt.SetType(_), "+",  Seq(rhs)) => xt.SetAdd(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "++", Seq(rhs)) => xt.SetUnion(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "&",  Seq(rhs)) => xt.SetIntersection(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "--", Seq(rhs)) => xt.SetDifference(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "subsetOf", Seq(rhs)) => xt.SubsetOf(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "contains", Seq(rhs)) => xt.ElementOfSet(extractTree(rhs), extractTree(lhs))
          case (xt.SetType(b), "isEmpty", Seq()) => xt.Equals(extractTree(lhs), xt.FiniteSet(Seq(), b))
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

          case (xt.MutableMapType(_, _), "apply", Seq(rhs)) =>
            xt.MutableMapApply(extractTree(lhs), extractTree(rhs))

          case (xt.MutableMapType(_, _), "update", Seq(key, value)) =>
            xt.MutableMapUpdate(extractTree(lhs), extractTree(key), extractTree(value))

          case (xt.MutableMapType(_, _), "updated", Seq(key, value)) =>
            xt.MutableMapUpdated(extractTree(lhs), extractTree(key), extractTree(value))

          case (xt.MutableMapType(_, _), "duplicate", Seq()) =>
            xt.MutableMapDuplicate(extractTree(lhs))

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
                getIdentifier(someSymbol.info.decl(termName("v")).symbol)
              ).setPos(tr.pos)
            )

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "isDefinedAt" | "contains", Seq(rhs)) =>
            xt.Not(xt.Equals(
              xt.MapApply(extractTree(lhs), extractTree(rhs)).setPos(tr.pos),
              xt.ClassConstructor(
                xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
                Seq.empty
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

          case (xt.MapType(from, xt.ClassType(_, Seq(to))), "+", Seq(rhs)) =>
            val vd = xt.ValDef(FreshIdentifier("x", true), xt.TupleType(Seq(from, to)).setPos(tr.pos)).setPos(tr.pos)
            xt.Let(vd, extractTree(rhs), xt.MapUpdated(
              extractTree(lhs), xt.TupleSelect(vd.toVariable, 1).setPos(tr.pos),
              xt.ClassConstructor(
                xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                Seq(xt.TupleSelect(vd.toVariable, 2).setPos(tr.pos))
              ).setPos(tr.pos)
            ).setPos(tr.pos))

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "removed" | "-", Seq(key)) =>
            xt.MapUpdated(
              extractTree(lhs), extractTree(key),
              xt.ClassConstructor(
                xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
                Seq.empty
              ).setPos(tr.pos)
            )

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "++", Seq(rhs)) =>
            extractTree(rhs) match {
              case xt.FiniteMap(pairs, default, keyType, valueType) =>
                pairs.foldLeft(extractTree(lhs)) { case (map, (k, v)) =>
                  xt.MapUpdated(map, k, v).setPos(tr.pos)
                }

              case _ => outOfSubsetError(tr, "Can't extract map union with non-finite map")
            }

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "--", Seq(rhs)) =>
            extractTree(rhs) match {
              case xt.FiniteSet(els, _) =>
                val none = xt.ClassConstructor(
                  xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
                  Seq.empty
                ).setPos(tr.pos)

                els.foldLeft(extractTree(lhs)) { case (map, k) =>
                  xt.MapUpdated(map, k, none).setPos(tr.pos)
                }

              case _ => outOfSubsetError(tr, "Can't extract map diff with non-finite map")
            }


          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "getOrElse", Seq(key, orElse)) =>
            xt.MethodInvocation(
              xt.MapApply(extractTree(lhs), extractTree(key)).setPos(tr.pos),
              getIdentifier(optionSymbol.info.decl(termName("getOrElse")).symbol),
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

          case (xt.BooleanType(), "|",   Seq(rhs)) => xt.BoolBitwiseOr(extractTree(lhs), extractTree(rhs))
          case (xt.BooleanType(), "&",   Seq(rhs)) => xt.BoolBitwiseAnd(extractTree(lhs), extractTree(rhs))
          case (xt.BooleanType(), "^",   Seq(rhs)) => xt.BoolBitwiseXor(extractTree(lhs), extractTree(rhs))

          case (xt.BVType(_,_), "|",   Seq(rhs)) => injectCasts(xt.BVOr)(lhs, rhs)
          case (xt.BVType(_,_), "&",   Seq(rhs)) => injectCasts(xt.BVAnd)(lhs, rhs)
          case (xt.BVType(_,_), "^",   Seq(rhs)) => injectCasts(xt.BVXor)(lhs, rhs)
          case (xt.BVType(_,_), "<<",  Seq(rhs)) => injectCastsForShift(xt.BVShiftLeft)(lhs, rhs)
          case (xt.BVType(_,_), ">>",  Seq(rhs)) => injectCastsForShift(xt.BVAShiftRight)(lhs, rhs)
          case (xt.BVType(_,_), ">>>", Seq(rhs)) => injectCastsForShift(xt.BVLShiftRight)(lhs, rhs)

          case (_, "&&",  Seq(rhs)) => xt.And(extractTree(lhs), extractTree(rhs))
          case (_, "||",  Seq(rhs)) => xt.Or(extractTree(lhs), extractTree(rhs))

          case (tpe, "toByte", Seq()) => tpe match {
            case xt.BVType(true, 8) => extractTree(lhs)
            case xt.BVType(true, 16 | 32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(true, 8))
            case tpe => outOfSubsetError(tr, s"Unexpected cast .toByte from $tpe")
          }

          case (tpe, "toShort", Seq()) => tpe match {
            case xt.BVType(true, 8) => xt.BVWideningCast(extractTree(lhs), xt.BVType(true, 16))
            case xt.BVType(true, 16) => extractTree(lhs)
            case xt.BVType(true, 32 | 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(true, 16))
            case tpe => outOfSubsetError(tr, s"Unexpected cast .toShort from $tpe")
          }

          case (tpe, "toInt", Seq()) => tpe match {
            case xt.BVType(true, 8 | 16) => xt.BVWideningCast(extractTree(lhs), xt.BVType(true, 32))
            case xt.BVType(true, 32) => extractTree(lhs)
            case xt.BVType(true, 64) => xt.BVNarrowingCast(extractTree(lhs), xt.BVType(true, 32))
            case tpe => outOfSubsetError(tr, s"Unexpected cast .toInt from $tpe")
          }

          case (tpe, "toLong", Seq()) => tpe match {
            case xt.BVType(true, 8 | 16 | 32 ) => xt.BVWideningCast(extractTree(lhs), xt.BVType(true, 64))
            case xt.BVType(true, 64) => extractTree(lhs)
            case tpe => outOfSubsetError(tr, s"Unexpected cast .toLong from $tpe")
          }

          case (tpe, name, args) =>
            outOfSubsetError(tr,
              s"Unknown call to $name on $lhs of type $tpe (${lhs.tpe}) with " +
              s"arguments ${args mkString ", "} of type " +
              s"${args.map(a => extractType(a)(dctx.setResolveTypes(true))).mkString(", ")}"
            )
        }
      }
    }

    // default behaviour is to complain :)
    case _ => outOfSubsetError(tr, s"Stainless does not support expression: `$tr`")
  }).ensurePos(tr.pos)


  /** Inject implicit widening casts according to the Java semantics (5.6.2. Binary Numeric Promotion) */
  private def injectCasts(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                         (lhs0: tpd.Tree, rhs0: tpd.Tree)
                         (using dctx: DefContext): xt.Expr = {
    injectCastsImpl(ctor)(lhs0, rhs0, shift = false)
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
                                 (using dctx: DefContext): xt.Expr = {
    injectCastsImpl(ctor)(lhs0, rhs0, shift = true)
  }

  private def injectCastsImpl(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                             (lhs0: tpd.Tree, rhs0: tpd.Tree, shift: Boolean)
                             (using dctx: DefContext): xt.Expr = {
    def checkBits(tr: tpd.Tree, tpe: xt.Type) = tpe match {
      case xt.BVType(_, 8 | 16 | 32 | 64) => // Byte, Short, Int or Long are ok
      case xt.BVType(_, s) => outOfSubsetError(tr, s"Unexpected integer of $s bits")
      case _ => // non-bitvector types are ok too
    }

    val lhs = extractTree(lhs0)
    val rhs = extractTree(rhs0)

    val ltpe = extractType(lhs0)(dctx.setResolveTypes(true))
    checkBits(lhs0, ltpe)
    val rtpe = extractType(rhs0)(dctx.setResolveTypes(true))
    checkBits(rhs0, rtpe)

    val id = { (e: xt.Expr) => e }
    val widen32 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.BVType(true, 32).copiedFrom(e)).copiedFrom(e) }
    val widen64 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.BVType(true, 64).copiedFrom(e)).copiedFrom(e) }

    val (lctor, rctor) = (ltpe, rtpe) match {
      case (xt.BVType(true, 64), xt.BVType(true, 64))          => (id, id)
      case (xt.BVType(true, 64), xt.BVType(true, _))           => (id, widen64)
      case (xt.BVType(true, _),  xt.BVType(true, 64)) if shift => outOfSubsetError(rhs0, s"Unsupported shift")
      case (xt.BVType(true, _),  xt.BVType(true, 64))          => (widen64, id)
      case (xt.BVType(true, 32), xt.BVType(true, 32))          => (id, id)
      case (xt.BVType(true, 32), xt.BVType(true, _))           => (id, widen32)
      case (xt.BVType(true, _),  xt.BVType(true, 32))          => (widen32, id)
      case (xt.BVType(true, _),  xt.BVType(true, _))           => (widen32, widen32)

      case (xt.BVType(_,_), _) | (_, xt.BVType(_,_)) =>
        outOfSubsetError(lhs0, s"Unexpected combination of types: $ltpe and $rtpe")

      case (_, _) => (id, id)
    }

    ctor(lctor(lhs), rctor(rhs))
  }

  /** Inject implicit widening cast according to the Java semantics (5.6.1. Unary Numeric Promotion) */
  private def injectCast(ctor: xt.Expr => xt.Expr)(e0: tpd.Tree)(using dctx: DefContext): xt.Expr = {
    val e = extractTree(e0)
    val etpe = extractType(e0)(dctx.setResolveTypes(true))

    val id = { e: xt.Expr => e }
    val widen32 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.Int32Type().copiedFrom(e)).copiedFrom(e) }

    val ector = etpe match {
      case xt.BVType(true, 8 | 16) => widen32
      case xt.BVType(true, 32 | 64) => id
      case xt.BVType(_, s) => outOfSubsetError(e0, s"Unexpected integer type of $s bits")
      case _ => id
    }

    ctor(ector(e))
  }

  // TODO: Recursively traverse type tree
  private def extractTypeTree(tpt: tpd.Tree)(using dctx: DefContext): Option[xt.Type] = {
    tpt match {
      case ByNameTypeTree(tpe) =>
        val result = xt.FunctionType(Seq(), extractType(tpe, tpe.tpe)).setPos(tpt.pos)
        Some(result)

      case PredicateTypeTree(vd, pred) =>
        val subject = xt.ValDef(getIdentifier(vd.symbol), extractType(vd.tpt, vd.tpe)).setPos(vd.pos)
        val nctx = dctx.withNewVar(vd.symbol -> (() => subject.toVariable))
        val predExpr = extractTree(pred)(nctx)
        val result = xt.RefinementType(subject, predExpr).setPos(tpt.pos)
        Some(result)

      case Select(prefix, name) if !(prefix.symbol.is(ModuleClass) || prefix.symbol.is(Module)) =>
        val path = extractTreeOrNoTree(prefix)
        val id = getIdentifier(tpt.symbol)
        val result = xt.TypeApply(xt.TypeSelect(Some(path).filterNot(_ == xt.NoTree), id), Seq())
        Some(result)

      case _ => None
    }
  }

  private def extractLocalClassType(tr: TypeRef, cid: Identifier, tps: List[xt.Type])
                                   (using dctx: DefContext, pos: Position): xt.LocalClassType = {

    val sym = tr.classSymbol
    val tparamsSyms = sym.typeParams.map(_.paramRef.typeSymbol)
    val tparams = extractTypeParams(tparamsSyms)

    val tpCtx = dctx.copy(tparams = dctx.tparams ++ (tparamsSyms zip tparams).toMap)
    val parents = tr.parents.filter(isValidParentType(_)).map(extractType(_)(tpCtx, pos))

    xt.LocalClassType(cid, tparams.map(xt.TypeParameterDef(_)), tps, parents)
  }

  private def extractType(tpt: tpd.Tree, tpe: Type)(using dctx: DefContext): xt.Type =
    extractTypeTree(tpt).getOrElse(stainlessType(tpe)(dctx, tpt.pos))

  private def extractType(t: tpd.Tree)(using dctx: DefContext): xt.Type = {
    extractType(t.tpe)(dctx, t.pos)
  }

  private val etCache = MutableMap[(Type, DefContext), xt.Type]()

  private def extractType(tpt: Type)(using dctx: DefContext, pos: Position): xt.Type = etCache.getOrElseUpdate((tpt -> dctx), {
    val res = (tpt match {
      case NoType => xt.Untyped

      case tpe if tpe.typeSymbol == defn.CharClass    => xt.CharType()
      case tpe if tpe.typeSymbol == defn.ByteClass    => xt.Int8Type()
      case tpe if tpe.typeSymbol == defn.ShortClass   => xt.Int16Type()
      case tpe if tpe.typeSymbol == defn.IntClass     => xt.Int32Type()
      case tpe if tpe.typeSymbol == defn.LongClass    => xt.Int64Type()
      case tpe if tpe.typeSymbol == defn.BooleanClass => xt.BooleanType()
      case tpe if tpe.typeSymbol == defn.UnitClass    => xt.UnitType()
      case tpe if tpe.typeSymbol == defn.NothingClass => xt.NothingType()

      // `isRef` seems to be needed here instead of `==`, as the latter
      // seems to be too lax, and makes the whole test suite fail. - @romac
      case tpe if tpe.isRef(defn.AnyClass) => xt.AnyType()

      case tpe if isBigIntSym(tpe.typeSymbol) => xt.IntegerType()
      case tpe if isRealSym(tpe.typeSymbol)   => xt.RealType()
      case tpe if isStringSym(tpe.typeSymbol) => xt.StringType()

      case ct: ConstantType => extractType(ct.value.tpe)
      case cet: CachedExprType => extractType(cet.resultType)

      case tr @ TypeRef(ref: TermParamRef, _) if dctx.depParams contains ref.paramName =>
        val vd = dctx.depParams(ref.paramName).setPos(pos)
        val selector = getIdentifier(tr.symbol)
        xt.TypeApply(xt.TypeSelect(Some(vd.toVariable), selector).setPos(pos), Seq.empty)

      case tr @ TypeRef(ref: TermRef, name) if !dctx.resolveTypes && (tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueHelper) =>
        val path = if ((ref.symbol is Module) || (ref.symbol is ModuleClass)) {
          None
        } else {
          val id = SymbolIdentifier(ref.name.mangledString)
          val vd = xt.ValDef(id, extractType(ref.underlying), Seq.empty).setPos(pos)
          Some(vd.toVariable)
        }

        val selector = getIdentifier(tr.symbol)
        xt.TypeApply(xt.TypeSelect(path, selector).setPos(pos), Seq.empty)

      case tr @ TypeRef(NoPrefix | _: ThisType, _) if dctx.tparams contains tr.symbol =>
        dctx.tparams.get(tr.symbol).getOrElse {
          outOfSubsetError(tpt.typeSymbol.pos, s"Stainless does not support type $tpt in context ${dctx.tparams}")
        }

      case tr: TypeRef if tr.symbol.isAbstractOrAliasType && dctx.resolveTypes =>
        extractType(tr.widenDealias)(dctx.setResolveTypes(tr != tr.widenDealias), pos)

      case tr: TypeRef if tr.symbol.isOpaqueHelper && dctx.resolveTypes =>
        extractType(tr.translucentSuperType)

      case tr @ TypeRef(thisRef: ThisType, _) if tr.symbol.isAbstractOrAliasType || tr.symbol.isOpaqueHelper =>
        val thiss =
          if (thisRef.tref.symbol is ModuleClass)
            None
          else
            extractType(thisRef) match {
              case ct: xt.ClassType => Some(xt.This(ct).setPos(pos))
              case lct: xt.LocalClassType => Some(xt.LocalThis(lct).setPos(pos))
            }

        val selector = getIdentifier(tr.symbol)
        xt.TypeApply(xt.TypeSelect(thiss, selector).setPos(pos), Seq.empty).setPos(pos)

      case tt @ TypeRef(prefix: TermRef, name) if prefix.underlying.classSymbol.typeParams.exists(_.name == name) =>
        extractType(TypeRef(prefix.widenTermRefExpr, name))

      case tt @ TypeRef(prefix, name) if prefix.classSymbol.typeParams.exists(_.name == name) =>
        val idx = prefix.classSymbol.typeParams.indexWhere(_.name == name)
        (extractType(prefix), idx) match {
          case (xt.MapType(from, ct @ xt.ClassType(id, Seq(to))), 1) => to
          case (tp @ xt.NAryType(tps, _), _) => tps(idx)
        }

      case AppliedType(tr: TypeRef, _) if !dctx.isExtern && isScalaSetSym(tr.symbol) =>
        outOfSubsetError(pos, "Scala's Set API is not directly supported, please use `stainless.lang.Set` instead.")
      case tr: TypeRef if !dctx.isExtern && isScalaSetSym(tr.symbol) =>
        outOfSubsetError(pos, "Scala's Set API is not directly supported, please use `stainless.lang.Set` instead.")

      case AppliedType(tr: TypeRef, _) if !dctx.isExtern && isScalaListSym(tr.symbol) =>
        outOfSubsetError(pos, "Scala's List API is not directly supported, please use `stainless.lang.collection.List` instead.")
      case tr: TypeRef if !dctx.isExtern && isScalaListSym(tr.symbol) =>
        outOfSubsetError(pos, "Scala's List API is not directly supported, please use `stainless.lang.collection.List` instead.")

      case AppliedType(tr: TypeRef, _) if !dctx.isExtern && isScalaMapSym(tr.symbol) =>
        outOfSubsetError(pos, "Scala's Map API is not directly supported, please use `stainless.lang.Map` instead.")
      case tr: TypeRef if !dctx.isExtern && isScalaMapSym(tr.symbol) =>
        outOfSubsetError(pos, "Scala's Map API is not directly supported, please use `stainless.lang.Map` instead.")

      case AppliedType(tr: TypeRef, Seq(tp)) if isSetSym(tr.symbol) =>
        xt.SetType(extractType(tp))

      case tr: TypeRef if isSetSym(tr.symbol) =>
        val Seq(tp) = extractTypeParams(tr.classSymbol.typeParams)
        xt.SetType(tp)

      case AppliedType(tr: TypeRef, Seq(tp)) if isBagSym(tr.symbol) =>
        xt.BagType(extractType(tp))

      case tr: TypeRef if isBagSym(tr.symbol) =>
        val Seq(tp) = extractTypeParams(tr.classSymbol.typeParams)
        xt.BagType(tp)

      case AppliedType(tr: TypeRef, tps) if isMapSym(tr.symbol) =>
        val Seq(from, to) = tps map extractType
        xt.MapType(from, xt.ClassType(getIdentifier(optionSymbol), Seq(to)).setPos(pos))

      case tr: TypeRef if isMapSym(tr.symbol) =>
        val Seq(from, to) = extractTypeParams(tr.classSymbol.typeParams)
        xt.MapType(from, xt.ClassType(getIdentifier(optionSymbol), Seq(to)).setPos(pos))

      case AppliedType(tr: TypeRef, tps) if TupleSymbol.unapply(tr.classSymbol).isDefined =>
        xt.TupleType(tps map extractType)

      case AppliedType(tr: TypeRef, tps) if isMutableMapSym(tr.symbol) =>
        val Seq(from, to) = tps map extractType
        xt.MutableMapType(from, to)

      case tr: TypeRef if isMutableMapSym(tr.symbol) =>
        val Seq(from, to) = extractTypeParams(tr.classSymbol.typeParams)
        xt.MutableMapType(from, to)

      case tr: TypeRef if TupleSymbol.unapply(tr.classSymbol).isDefined =>
        xt.TupleType(extractTypeParams(tr.classSymbol.typeParams))

      case AppliedType(tr: TypeRef, Seq(tp)) if isArrayClassSym(tr.symbol) =>
        xt.ArrayType(extractType(tp))

      case tr: TypeRef if isArrayClassSym(tr.symbol) =>
        val Seq(tp) = extractTypeParams(tr.classSymbol.typeParams)
        xt.ArrayType(tp)

      case tp: RefinedType if defn.isFunctionType(tp) =>
        val mt = tp.refinedInfo.asInstanceOf[MethodType]

        val vds = (mt.paramNames zip mt.paramInfos) map { case (name, tpe) =>
          xt.ValDef(SymbolIdentifier(name.mangledString), extractType(tpe), Seq.empty)
        }

        val rctx = dctx.withDepParams(mt.paramNames zip vds)
        val resultType = extractType(mt.resultType)(rctx, pos)

        xt.PiType(vds, resultType)

      case tp if defn.isFunctionClass(tp.typeSymbol) && tp.dealias.argInfos.isEmpty =>
        xt.FunctionType(Seq(), xt.UnitType())

      case fo @ defn.FunctionOf(from, to, _, _) =>
        xt.FunctionType(from map extractType, extractType(to))

      case tt @ ThisType(tr) =>
        extractType(tr)

      case st @ SuperType(thisTpe, superTpe) =>
        extractType(superTpe)

      case RefinedType(p, name, tpe) =>
        val idx = p.classSymbol.typeParams.indexWhere(_.name == name)
        (extractType(p), idx) match {
          case (xt.MapType(from, ct @ xt.ClassType(id, Seq(to))), 1) =>
            xt.MapType(from, xt.ClassType(id, Seq(extractType(tpe))).copiedFrom(ct))
          case (xt.NAryType(tps, recons), _) =>
            recons(tps.updated(idx, extractType(tpe)))
        }

      case at @ AppliedType(tr: TypeRef, args) if tr.symbol.info.isTypeAlias && dctx.resolveTypes =>
        extractType(at.widenDealias)

      case at @ AppliedType(tr: TypeRef, args) if tr.symbol.info.isTypeAlias =>
        xt.TypeApply(xt.TypeSelect(None, getIdentifier(tr.symbol)), args map extractType)

      case at @ AppliedType(tycon: TypeRef, args) =>
        val sym = at.classSymbol
        val id = getIdentifier(sym)
        val tps = args map extractType


        dctx.localClasses.get(id) match {
          case Some(lcd) => extractLocalClassType(tycon, lcd.id, tps)
          case None => xt.ClassType(id, tps)
        }

      case tt @ TypeRef(_, _) if tt.classSymbol.exists && tt.classSymbol != defn.AnyClass =>
        val sym = tt.classSymbol
        val id = getIdentifier(sym)
        val tparams = sym.typeParams.map { sym =>
          xt.TypeParameter(getIdentifier(sym), Seq())
        }

        dctx.localClasses.get(id) match {
          case Some(lcd) => extractLocalClassType(tt, lcd.id, tparams)
          case None => xt.ClassType(id, tparams)
        }

      case tt @ TermRef(_, _) if dctx.resolveTypes =>
        extractType(tt.widenDealias)

      case tt @ TermRef(_, _) =>
        extractType(tt.widenTermRefExpr)

      case tb @ TypeBounds(lo, hi) => extractType(hi)

      case AndType(tp, prod) if prod.typeSymbol == defn.ProductClass => extractType(tp)
      case AndType(prod, tp) if prod.typeSymbol == defn.ProductClass => extractType(tp)
      case AndType(tp, prod) if defn.isProductClass(prod.typeSymbol) => extractType(tp)
      case AndType(prod, tp) if defn.isProductClass(prod.typeSymbol) => extractType(tp)

      case ot: OrType => extractType(ot.join)

      case pp @ TypeParamRef(binder, num) =>
        dctx.tparams.collect { case (k, v) if k.name == pp.paramName => v }.lastOption.getOrElse {
          outOfSubsetError(tpt.typeSymbol.pos, s"Stainless does not support type $tpt in context ${dctx.tparams}")
        }

      case tp: TypeVar => extractType(tp.stripTypeVar)

      case AnnotatedType(tpe, ExIndexedAt(n)) =>
        xt.AnnotatedType(extractType(tpe), Seq(xt.IndexedAt(extractTree(n))))

      case AnnotatedType(tpe, _) => extractType(tpe)

      case _ =>
        if (tpt ne null) {
          outOfSubsetError(tpt.typeSymbol.pos, s"Stainless does not support type $tpt")
        } else {
          outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
        }
    }).setPos(pos)

    res
  })

}
