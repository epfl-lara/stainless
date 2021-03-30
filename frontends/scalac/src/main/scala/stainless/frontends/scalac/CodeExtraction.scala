/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.scalac

import ast.SymbolIdentifier
import frontend.UnsupportedCodeException
import extraction.xlang.{trees => xt}

import scala.reflect.internal.util._
import scala.collection.mutable.{Map => MutableMap, ListBuffer}

import scala.language.implicitConversions

/**
 * Extract Scalac Trees into Stainless Trees.
 *
 * This trait builds a mapping between (scalac) symbols and (stainless/inox) identifiers
 * to avoid generating two different identifiers for the same object/function/type/...
 * when extracting each compilation unit on its own. See [[cache]] below.
 *
 * However, if an object/function/type/... is modified and recompiled, the produced identifier
 * will be different in order to support incremental compilation.
 */
trait CodeExtraction extends ASTExtractors {
  self: StainlessExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import scala.collection.immutable.Set

  lazy val ignoredClasses = Set(
    ObjectClass.tpe,
    SerializableClass.tpe,
    JavaSerializableClass.tpe,
    ProductRootClass.tpe,
    AnyRefClass.tpe,
    AnyValClass.tpe,
  )

  /** Extract the classes and functions from the given compilation unit. */
  def extractUnit(u: CompilationUnit): (xt.UnitDef, Seq[xt.ClassDef], Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val (id, stats) = u.body match {
      // package object
      case PackageDef(refTree, List(pd @ PackageDef(inner, body))) =>
        (FreshIdentifier(extractRef(inner).mkString("$")), pd.stats)

      case pd @ PackageDef(refTree, lst) =>
        (FreshIdentifier(u.source.file.name.replaceFirst("[.][^.]+$", "")), pd.stats)

      case _ =>
        (FreshIdentifier(u.source.file.name.replaceFirst("[.][^.]+$", "")), List.empty)
    }

    val (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs) = extractStatic(stats)
    assert(functions.isEmpty, "Packages shouldn't contain functions")
    assert(typeDefs.isEmpty, "Packages shouldn't contain type defintions")

    val unit = xt.UnitDef(
      id,
      imports,
      classes,
      subs,
      !(Main.libraryFiles contains u.source.file.absolute.path)
    ).setPos(u.body.pos)

    (unit, allClasses, allFunctions, allTypeDefs)
  }

  private lazy val reporter = self.ctx.reporter
  implicit val debugSection = frontend.DebugSectionExtraction

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

  private def outOfSubsetError(pos: Position, msg: String) = {
    throw new UnsupportedCodeException(pos, msg)
  }

  private def outOfSubsetError(t: Tree, msg: String) = {
    throw new UnsupportedCodeException(t.pos, msg)
  }


  /**
   * Mapping from input symbols to output symbols/identifiers.
   *
   * In order to reuse the same stainless/inox identifiers, the [[cache]]
   * need to be re-used between different runs of the compiler. Because
   * different instances of the compiler (and [[Global]]) are used for
   * each runs, the [[cache]] need to be stored outside the compiler.
   */
  protected val cache: SymbolMapping
  private def getIdentifier(sym: Symbol): SymbolIdentifier = cache fetch sym

  private def annotationsOf(sym: Symbol, ignoreOwner: Boolean = false): Seq[xt.Flag] = {
    getAnnotations(sym, ignoreOwner)
      .filter { case (name, _) => !name.startsWith("isabelle") }
      .map { case (name, args) =>
        xt.extractFlag(name, args.map(extractTree(_)(DefContext())))
      }
  }

  private case class DefContext(
    tparams: Map[Symbol, xt.TypeParameter] = Map(),
    vars: Map[Symbol, () => xt.Expr] = Map(),
    mutableVars: Map[Symbol, () => xt.Variable] = Map(),
    localFuns: Map[Symbol, (Identifier, Seq[xt.TypeParameterDef], xt.FunctionType)] = Map(),
    localClasses: Map[Identifier, xt.LocalClassDef] = Map(),
    isExtern: Boolean = false,
    resolveTypes: Boolean = false,
    wrappingArithmetic: Boolean = false,
  ){
    def union(that: DefContext) = {
      copy(this.tparams ++ that.tparams,
           this.vars ++ that.vars,
           this.mutableVars ++ that.mutableVars,
           this.localFuns ++ that.localFuns,
           this.localClasses ++ that.localClasses,
           this.isExtern || that.isExtern,
           this.resolveTypes || that.resolveTypes,
           this.wrappingArithmetic || that.wrappingArithmetic)
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

    def withNewVar(s: Symbol, v: () => xt.Variable) = {
      copy(vars = vars + (s -> v))
    }

    def withNewMutableVar(s: Symbol, v: () => xt.Variable) = {
      copy(mutableVars = mutableVars + (s -> v))
    }

    def withLocalFun(sym: Symbol, id: Identifier, tparams: Seq[xt.TypeParameterDef], tpe: xt.FunctionType) = {
      copy(localFuns = this.localFuns + (sym -> ((id, tparams, tpe))))
    }

    def withLocalClass(lcd: xt.LocalClassDef) = {
      copy(localClasses = this.localClasses + (lcd.id -> lcd))
    }

    def setResolveTypes(resolveTypes: Boolean) = {
      copy(resolveTypes = resolveTypes)
    }

    def setWrappingArithmetic(wrappingArithmetic: Boolean) = {
      copy(wrappingArithmetic = wrappingArithmetic)
    }
  }

  // This one never fails, on error, it returns Untyped
  private def stainlessType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = {
    try {
      extractType(tpt)
    } catch {
      case e: UnsupportedCodeException =>
        reporter.debug(e.pos, "[ignored] " + e.getMessage, e)
        xt.Untyped
    }
  }

  private def extractStatic(stats: List[Tree]): (
    Seq[xt.Import],
    Seq[Identifier], // classes
    Seq[Identifier], // functions
    Seq[Identifier], // typeDefs
    Seq[xt.ModuleDef],
    Seq[xt.ClassDef],
    Seq[xt.FunDef],
    Seq[xt.TypeDef]
  ) = {
    var imports   : Seq[xt.Import]    = Seq.empty
    var classes   : Seq[Identifier]   = Seq.empty
    var functions : Seq[Identifier]   = Seq.empty
    var typeDefs  : Seq[Identifier]   = Seq.empty
    var subs      : Seq[xt.ModuleDef] = Seq.empty

    var allClasses   : Seq[xt.ClassDef] = Seq.empty
    var allFunctions : Seq[xt.FunDef]   = Seq.empty
    var allTypeDefs  : Seq[xt.TypeDef]  = Seq.empty

    for (d <- stats) d match {
      case EmptyTree =>
        // ignore

      case l: Literal =>
        // top level literal are ignored

      case t if (
        (annotationsOf(t.symbol) contains xt.Ignore) ||
        (t.symbol.isSynthetic && !canExtractSynthetic(t.symbol))
      ) =>
        // ignore

      case ExtractorHelpers.ExSymbol("stainless", "annotation", "ignore") =>
        // ignore (can't be @ignored because of the dotty compiler)

      case ExConstructorDef() =>
        // ignore

      case i @ Import(_, _) =>
        imports ++= extractImports(i)

      case pd @ PackageDef(ref, stats) =>
        val (imports, classes, functions, typeDefs, modules, newClasses, newFunctions, newTypeDefs) = extractStatic(stats)
        val pid = FreshIdentifier(extractRef(ref).mkString("$"))
        subs :+= xt.ModuleDef(pid, imports, classes, functions, typeDefs, modules)
        allClasses ++= newClasses
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case td @ ExObjectDef(_, _) =>
        val (obj, newClasses, newFunctions, newTypeDefs) = extractObject(td)
        subs :+= obj
        allClasses ++= newClasses
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case md: ModuleDef if !md.symbol.isSynthetic && md.symbol.isCase =>
        val (xcd, newFunctions, newTypeDefs) = extractClass(md)(DefContext())
        classes :+= xcd.id
        allClasses :+= xcd
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case cd: ClassDef =>
        val (xcd, newFunctions, newTypeDefs) = extractClass(cd)(DefContext())
        classes :+= xcd.id
        allClasses :+= xcd
        allFunctions ++= newFunctions
        allTypeDefs ++= newTypeDefs

      case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        val fd = extractFunction(fsym, tparams, vparams, rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExMutableFieldDef(fsym, _, _) if fsym.isMutable && annotationsOf(fsym).contains(xt.Extern) =>
        // Ignore @extern variables in static context

      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExFieldAccessorFunction(fsym, _, vparams, rhs) =>
        val fd = extractFunction(fsym, Seq.empty, vparams, rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      case t @ ExLazyFieldAccessorFunction(fsym, _, rhs) =>
        val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
        functions :+= fd.id
        allFunctions :+= fd

      case t if t.symbol.isSynthetic =>
        // ignore

      case t: TypeDef if t.symbol.isAliasType =>
        val td = extractTypeDef(t)(DefContext())
        typeDefs :+= td.id
        allTypeDefs :+= td

      case t @ ExMutableFieldDef(_, _, _) =>
        outOfSubsetError(t, "Mutable fields in static containers such as objects are not supported")

      case other =>
        reporter.warning(other.pos, s"Stainless does not support the following tree in static containers:\n$other")
    }

    (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs)
  }

  private def extractTypeDef(td: TypeDef)(implicit dctx: DefContext): xt.TypeDef = {
    val sym = td.symbol
    val id = getIdentifier(sym)
    val flags = annotationsOf(sym) ++
      (if (sym.isAbstractType) Some(xt.IsAbstract) else None)

    val tparamsSyms = sym.tpe match {
      case TypeRef(_, _, tps) => typeParamSymbols(tps)
      case _ => Nil
    }

    val tparams = extractTypeParams(tparamsSyms)

    val tpCtx = dctx.withNewTypeParams(tparamsSyms zip tparams)
    val body = extractType(td.rhs)(tpCtx) match {
      case xt.TypeBounds(lo, hi, fls) => xt.TypeBounds(lo, hi, fls ++ flags.filterNot(_ == xt.IsAbstract))
      case tp => tp
    }

    new xt.TypeDef(
      id,
      tparams.map(xt.TypeParameterDef(_)),
      body,
      flags
    )
  }

  private def extractObject(obj: ModuleDef): (xt.ModuleDef, Seq[xt.ClassDef], Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val ExObjectDef(_, template) = obj

    val (imports, classes, functions, typeDefs, subs, allClasses, allFunctions, allTypeDefs) = extractStatic(template.body)

    val module = xt.ModuleDef(
      getIdentifier(obj.symbol),
      imports,
      classes,
      functions,
      typeDefs,
      subs
    ).setPos(obj.pos)

    (module, allClasses, allFunctions, allTypeDefs)
  }

  private def extractClass(cd: ImplDef)(implicit dctx: DefContext): (xt.ClassDef, Seq[xt.FunDef], Seq[xt.TypeDef]) = {
    val sym = cd.symbol
    val id = getIdentifier(sym.moduleClass.orElse(sym))

    val isValueClass = cd.impl.parents.map(_.tpe).exists(_ == AnyValClass.tpe)

    val annots = annotationsOf(sym)
    val flags = annots ++
      (if (isValueClass) Some(xt.ValueClass) else None) ++
      (if (sym.isAbstractClass) Some(xt.IsAbstract) else None) ++
      (if (sym.isSealed) Some(xt.IsSealed) else None) ++
      (if (sym.tpe.typeSymbol.isModuleClass && sym.isCase) Some(xt.IsCaseObject) else None)

    val tparamsSyms = sym.tpe match {
      case TypeRef(_, _, tps) => typeParamSymbols(tps)
      case _ => Nil
    }

    val tparams = extractTypeParams(tparamsSyms)(DefContext())

    val tpCtx = dctx.copy(tparams = dctx.tparams ++ (tparamsSyms zip tparams).toMap)

    val parents = cd.impl.parents.flatMap(p => p.tpe match {
      case tpe if ignoredClasses contains tpe => None
      case tpe if tpe =:= ThrowableTpe && (flags exists (_.name == "library")) => None
      case tp @ TypeRef(_, _, _) =>
        extractType(tp)(tpCtx, p.pos) match {
          case ct: xt.ClassType => Some(ct)
          case lct: xt.LocalClassType => Some(lct.toClassType)
          case _ => None
        }
      case _ => None
    })

    val constructorOpt = cd.impl.children.find {
      case ExConstructorDef() => true
      case _ => false
    }.asInstanceOf[Option[DefDef]]

    val vds = cd.impl.children.collect {
      case vd: ValDef if !sym.isImplicit && !vd.symbol.isAccessor && vd.symbol.isCaseAccessor && vd.symbol.isParamAccessor => vd
      case vd: ValDef if sym.isImplicit && !vd.symbol.isAccessor && vd.symbol.isParamAccessor => vd
    }

    val fields = vds map { vd =>
      val sym = vd.symbol
      val id = getIdentifier(sym)
      val flags = annotationsOf(sym, ignoreOwner = true)
      val tpe = stainlessType(vd.tpt.tpe)(tpCtx, vd.pos)
      val (isExtern, isPure) = (flags contains xt.Extern, flags contains xt.IsPure)
      val isMutable = sym.isVar || isExtern && !isPure

      (if (isMutable) xt.VarDef(id, tpe, flags) else xt.ValDef(id, tpe, flags)).setPos(sym.pos)
    }

    val hasExternFields = fields.exists(_.flags.contains(xt.Extern))

    val defCtx = tpCtx.withNewVars((vds.map(_.symbol) zip fields.map(vd => () => vd.toVariable)).toMap)

    var invariants: Seq[xt.Expr]     = Seq.empty
    var methods: Seq[xt.FunDef]      = Seq.empty
    var typeMembers: Seq[xt.TypeDef] = Seq.empty

    for ((d, i) <- cd.impl.body.zipWithIndex) d match {
      case EmptyTree =>
        // ignore

      case i: Import =>
        // ignore

      case t if annotationsOf(t.symbol).contains(xt.Ignore) && !t.symbol.isCaseAccessor =>
        // ignore

      case t if t.symbol.isSynthetic && !canExtractSynthetic(t.symbol) =>
        // ignore

      case ExCaseClassSyntheticJunk() | ExConstructorDef() =>
       // ignore

      case ExRequiredExpression(body, isStatic) =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
        invariants :+= wrap(extractTree(body)(defCtx))

      case t @ ExFunctionDef(fsym, _, _, _, _)
        if hasExternFields && (isCopyMethod(fsym) || isDefaultGetter(fsym)) =>
          // we cannot extract copy method if the class has ignored fields as
          // the type of copy and the getters mention what might be a type we
          // cannot extract.

      case t @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
        methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx)

      case t @ ExFieldDef(fsym, _, rhs) =>
        val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)
        methods :+= fd.copy(flags = fd.flags :+ xt.FieldDefPosition(i))

      case t @ ExLazyFieldDef(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)

      case t @ ExFieldAccessorFunction(fsym, _, vparams, rhs) =>
        methods :+= extractFunction(fsym, Seq.empty, vparams, rhs)(defCtx)

      case t @ ExFieldAccessorFunction(fsym, _, vparams, rhs) =>
        methods :+= extractFunction(fsym, Seq.empty, vparams, rhs)(defCtx)

      case t @ ExLazyFieldAccessorFunction(fsym, _, rhs) =>
        methods :+= extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)

      case t @ ExMutableFieldDef(_, _, rhs) if rhs != EmptyTree =>
        outOfSubsetError(t, "Mutable fields in traits cannot have a default value")

      case vd @ ExMutableFieldDef(sym, _, _) if vd.symbol.owner.isAbstract || vd.symbol.owner.isTrait =>
        methods :+= extractFunction(sym, Seq.empty, Seq.empty, EmptyTree)(defCtx)

      case t: TypeDef =>
        val td = extractTypeDef(t)(defCtx)
        typeMembers :+= td

      case ValDef(_, _, _, _) =>
        // ignore (corresponds to constructor fields)

      case d if d.symbol.isSynthetic =>
        // ignore

      case d if d.symbol.isVar =>
        // ignore

      case other =>
        reporter.warning(other.pos, s"In class $id, Stainless does not support:\n$other")
    }

    val optInv = if (invariants.isEmpty) None else Some({
      val id = cache fetchInvIdForClass sym
      val pos = inox.utils.Position.between(invariants.map(_.getPos).min, invariants.map(_.getPos).max)
      new xt.FunDef(id, Seq.empty, Seq.empty, xt.BooleanType().setPos(pos),
        if (invariants.size == 1) invariants.head else xt.And(invariants).setPos(pos),
        (Seq(xt.IsInvariant) ++ annots.filterNot(_ == xt.IsMutable)).distinct
      ).setPos(pos)
    })

    val allMethods = (methods ++ optInv).map(fd => fd.copy(flags = fd.flags :+ xt.IsMethodOf(id)))
    val allTypeMembers = typeMembers.map(td => td.copy(flags = td.flags :+ xt.IsTypeMemberOf(id)))

    val xcd = new xt.ClassDef(
      id,
      tparams.map(tp => xt.TypeParameterDef(tp)),
      parents,
      fields,
      flags
    ).setPos(sym.pos)

    (xcd, allMethods, allTypeMembers)
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

    val tctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams).toMap)

    val (newParams, nctx) = sym.info.paramss.flatten.foldLeft((Seq.empty[xt.ValDef], tctx)) {
      case ((vds, vctx), sym) =>
        val ptpe = stainlessType(sym.tpe)(vctx, sym.pos)
        val tpe = if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe).setPos(sym.pos) else ptpe
        val flags = annotationsOf(sym, ignoreOwner = true)
        val vd = xt.ValDef(getIdentifier(sym), tpe, flags).setPos(sym.pos)
        val expr = if (sym.isByNameParam) {
          () => xt.Application(vd.toVariable, Seq()).setPos(vd)
        } else {
          () => vd.toVariable
        }
        (vds :+ vd, vctx.withNewVar(sym, () => vd.toVariable))
    }

    val id = getIdentifier(sym)
    val isAbstract = rhs == EmptyTree

    var flags = annotationsOf(sym).filterNot(annot => annot == xt.IsMutable || annot.name == "inlineInvariant") ++
      (if (sym.isImplicit && sym.isSynthetic) Seq(xt.Inline, xt.Synthetic) else Seq()) ++
      (if (sym.isPrivate) Seq(xt.Private) else Seq()) ++
      (if (sym.isFinal) Seq(xt.Final) else Seq()) ++
      (if (sym.isVal || sym.isLazy) Seq(xt.IsField(sym.isLazy)) else Seq()) ++
      (if (isDefaultGetter(sym) || isCopyMethod(sym)) Seq(xt.Synthetic, xt.Inline) else Seq()) ++
      (if (!sym.isLazy && sym.isAccessor)
        Seq(xt.IsAccessor(Option(getIdentifier(sym.accessedOrSelf)).filterNot(_ => isAbstract)))
      else Seq())

    if (sym.name == nme.unapply) {
      def matchesParams(member: Symbol) = member.paramss match {
        case Nil        => true
        case ps :: rest => (rest.isEmpty || isImplicitParamss(rest)) && (ps corresponds Seq())(_.tpe =:= _)
      }
      val isEmptySym = sym.info.finalResultType member nme.isEmpty filter matchesParams
      val getSym = sym.info.finalResultType member nme.get filter matchesParams
      flags :+= xt.IsUnapply(getIdentifier(isEmptySym), getIdentifier(getSym))
    }

    val body = rhs

    val paramsMap = (vparams.map(_.symbol) zip newParams).map { case (s, vd) =>
      s -> (if (s.isByNameParam) () => xt.Application(vd.toVariable, Seq()).setPos(vd.toVariable) else () => vd.toVariable)
    }.toMap

    val fctx = nctx
      .withNewVars(paramsMap)
      .copy(tparams = dctx.tparams ++ (tparams zip ntparams))
      .copy(isExtern = dctx.isExtern || (flags contains xt.Extern))

    lazy val retType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

    val (finalBody, returnType) = if (isAbstract) {
      flags :+= xt.IsAbstract
      (xt.NoTree(retType).setPos(sym.pos), retType)
    } else {
      val fullBody = xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
      val localClasses = xt.exprOps.collect[xt.LocalClassDef] {
        case xt.LetClass(lcds, _) => lcds.toSet
        case _ => Set()
      } (fullBody)

      if (localClasses.isEmpty) (fullBody, retType)
      else {
        // If the function contains local classes, we need to add those to the
        // context in order to type its body.
        val tctx = localClasses.toSeq.foldLeft(nctx)(_ withLocalClass _)

        val returnType = stainlessType(sym.info.finalResultType)(tctx, sym.pos)
        val bctx = fctx.copy(localClasses = fctx.localClasses ++ tctx.localClasses)
        // FIXME: `flattenBlocks` should not change the positions that appear in `ntparams`
        (xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(bctx)), returnType)
      }
    }

    object KeywordChecker extends xt.SelfTreeTraverser {
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
      val specced = xt.exprOps.BodyWithSpecs(finalBody)
      specced.bodyOpt foreach { KeywordChecker.traverse }
      specced.withBody(xt.NoTree(returnType)).reconstructed.setPos(body.pos)
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

  private def typeParamSymbols(tps: Seq[Type]): Seq[Symbol] = tps.flatMap {
    case TypeRef(_, sym, Nil) =>
      Some(sym)
    case t =>
      outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
      None
  }

  private def extractTypeParams(syms: Seq[Symbol])(implicit dctx: DefContext): Seq[xt.TypeParameter] = {
    syms.foldLeft((dctx, Seq[xt.TypeParameter]())) { case ((dctx, tparams), sym) =>
      val variance =
        if (sym.isCovariant) Some(xt.Variance(true))
        else if (sym.isContravariant) Some(xt.Variance(false))
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
          outOfSubsetError(s, "Invalid instance pattern: " + s)
      }

    case id @ Ident(_) if id.tpe.typeSymbol.isCase =>
      extractType(id) match {
        case ct: xt.ClassType =>
          (xt.ClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
        case _ =>
          outOfSubsetError(id, "Invalid instance pattern: " + id)
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

      (xt.UnapplyPattern(binder, Seq(), id, tps, sub).setPos(up.pos), ctx.foldLeft(dctx)(_ union _))

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
      case e: UnsupportedCodeException =>
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
      val tparams = extractTypeParams(extparams)(dctx)
      val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip tparams).toMap)

      val tparamDefs = tparams.map(tp => xt.TypeParameterDef(tp).copiedFrom(tp))

      val tpe = xt.FunctionType(
        sym.info.paramss.flatten.map { sym =>
          val ptpe = stainlessType(sym.tpe)(nctx, sym.pos)
          if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe).setPos(sym.pos) else ptpe
        },
        stainlessType(sym.info.finalResultType)(nctx, sym.pos)
      ).setPos(sym.pos)

      dctx.withLocalFun(sym, getIdentifier(sym), tparamDefs, tpe)
    }

    val (vds, vctx) = es.collect {
      case v @ ValDef(_, name, tpt, _) => (v.symbol, name, tpt)
    }.foldLeft((Map.empty[Symbol, xt.ValDef], fctx)) { case ((vds, dctx), (sym, name, tpt)) =>
      if (!sym.isMutable) {
        val laziness = if (sym.isLazy) Some(xt.Lazy) else None
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true) ++ laziness).setPos(sym.pos)
        (vds + (sym -> vd), dctx.withNewVar(sym, () => vd.toVariable))
      } else {
        val vd = xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
        (vds + (sym -> vd), dctx.withNewMutableVar(sym, () => vd.toVariable))
      }
    }

    val (lcds, cctx) = es.collect {
      case cd: ClassDef => cd
    }.foldLeft((Map.empty[Symbol, xt.LocalClassDef], vctx)) { case ((lcds, dctx), cd) =>
      val (xcd, methods, typeDefs) = extractClass(cd)(dctx)
      val lcd = xt.LocalClassDef(xcd, methods, typeDefs).setPos(xcd)
      (lcds + (cd.symbol -> lcd), dctx.withLocalClass(lcd))
    }

    def rec(es: List[Tree]): xt.Expr = es match {
      case Nil => xt.UnitLiteral()

      case (i: Import) :: xs => rec(xs)

      case (e @ ExAssertExpression(contract, oerr, isStatic)) :: xs =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
        val const = extractTree(contract)(cctx)
        val b     = rec(xs)
        xt.Assert(wrap(const), oerr, b).setPos(e.pos)

      case (e @ ExRequiredExpression(contract, isStatic)) :: xs =>
        def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
        val pre = extractTree(contract)(cctx)
        val b   = rec(xs)
        xt.Require(wrap(pre), b).setPos(e.pos)

      case (e @ ExDecreasesExpression(ranks)) :: xs =>
        val rs = ranks.map(extractTree(_)(cctx))
        val b = rec(xs)
        xt.Decreases(xt.tupleWrap(rs), b).setPos(e.pos)

      case (d @ ExFunctionDef(sym, tparams, vparams, tpt, rhs)) :: xs =>
        val (id, tdefs, tpe) = cctx.localFuns(sym)
        val fd = extractFunction(sym, tparams, vparams, rhs, typeParams = Some(tdefs.map(_.tp)))(cctx)
        val letRec = xt.LocalFunDef(id, tdefs, fd.params, fd.returnType, fd.fullBody, fd.flags).setPos(d.pos)

        rec(xs) match {
          case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body).setPos(d.pos)
          case other => xt.LetRec(Seq(letRec), other).setPos(d.pos)
        }

      case (cd: ClassDef) :: xs =>
        val lcd = lcds(cd.symbol)

        // Drop companion object and/or synthetic modules Scalac inserts after local class declarations
        val rest = xs dropWhile (x => x.symbol.isSynthetic && x.symbol.isModule)
        rec(rest) match {
          case xt.LetClass(defs, body) => xt.LetClass(lcd +: defs, body).setPos(cd.pos)
          case other => xt.LetClass(Seq(lcd), other).setPos(cd.pos)
        }

      case (v @ ValDef(mods, name, tpt, _)) :: xs =>
        if (mods.isMutable) {
          xt.LetVar(vds(v.symbol), extractTree(v.rhs)(cctx), rec(xs)).setPos(v.pos)
        } else {
          xt.Let(vds(v.symbol), extractTree(v.rhs)(cctx), rec(xs)).setPos(v.pos)
        }

      case x :: Nil =>
        extractTree(x)(cctx)

      case (x @ Block(_, _)) :: rest =>
        val re = rec(rest)
        val (elems, last) = re match {
          case xt.Block(elems, last) => (elems, last)
          case e => (Seq(), e)
        }

        extractTree(x)(vctx) match {
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

  private def extractArgs(sym: Symbol, args: Seq[Tree])(implicit dctx: DefContext): Seq[xt.Expr] = {
    (sym.paramLists.flatten zip args.map(extractTree)).map {
      case (sym, e) => if (sym.isByNameParam) xt.Lambda(Seq.empty, e).setPos(e) else e
    }
  }

  def stripAnnotationsExceptStrictBV(tpe: xt.Type): xt.Type = tpe match {
    case xt.AnnotatedType(tp, flags) if flags.contains(xt.StrictBV) =>
      xt.AnnotatedType(stripAnnotationsExceptStrictBV(tp), Seq(xt.StrictBV))
    case xt.AnnotatedType(tp, _) =>
      stripAnnotationsExceptStrictBV(tp)
    case _ => tpe
  }

  private def extractTree(tr: Tree)(implicit dctx: DefContext): xt.Expr = (tr match {
    case ExObjectDef(_, _) => xt.UnitLiteral()
    case ExCaseClassSyntheticJunk() => xt.UnitLiteral()
    case md: ModuleDef if md.symbol.isSynthetic => xt.UnitLiteral()

    case Block(es, e) =>
      val b = extractBlock(es :+ e)
      xt.exprOps.flattenBlocks(b)

    case Try(body, cses, fin) =>
      val rb = extractTree(body)
      val rc = cses.map(extractMatchCase)
      xt.Try(rb, rc, if (fin == EmptyTree) None else Some(extractTree(fin)))

    case Return(e) => xt.Return(extractTree(e))

    case Throw(ex) =>
      xt.Throw(extractTree(ex))

    case ExAssertExpression(e, oerr, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
      xt.Assert(wrap(extractTree(e)), oerr, xt.UnitLiteral().setPos(tr.pos))

    case ExRequiredExpression(body, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x
      xt.Require(wrap(extractTree(body)), xt.UnitLiteral().setPos(tr.pos))

    case ExEnsuredExpression(body, contract, isStatic) =>
      def wrap(x: xt.Expr) = if (isStatic) xt.Annotated(x, Seq(xt.Ghost)).setPos(x) else x

      val post = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      xt.Ensuring(b, post match {
        case l: xt.Lambda => l.copy(body = wrap(l.body)).copiedFrom(l)
        case other =>
          val tpe = extractType(body)
          val vd = xt.ValDef.fresh("res", tpe).setPos(other)
          xt.Lambda(Seq(vd), wrap(extractType(contract) match {
            case xt.BooleanType() => post
            case _ => xt.Application(other, Seq(vd.toVariable)).setPos(post)
          })).setPos(post)
      })

    case ExThrowingExpression(body, contract) =>
      val throwing = extractTree(contract)
      val b = extractTreeOrNoTree(body)

      xt.Throwing(b, throwing match {
        case l: xt.Lambda => l
        case other =>
          val tpe = extractType(exceptionSym.info)(dctx, contract.pos)
          val vd = xt.ValDef.fresh("res", tpe).setPos(other)
          xt.Lambda(Seq(vd), xt.Application(other, Seq(vd.toVariable)).setPos(other)).setPos(other)
      })

    case t @ ExHoldsWithProofExpression(body, ExMaybeBecauseExpressionWrapper(proof)) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val p = extractTreeOrNoTree(proof)
      val and = xt.And(p, vd.toVariable).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd), and).setPos(tr.pos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)

    case t @ ExHoldsExpression(body) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.pos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)

    // If the because statement encompasses a holds statement
    case t @ ExBecauseExpression(ExHoldsExpression(body), proof) =>
      val vd = xt.ValDef.fresh("holds", xt.BooleanType().setPos(tr.pos)).setPos(tr.pos)
      val p = extractTree(proof)
      val and = xt.And(p, vd.toVariable).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd), and).setPos(tr.pos)
      val b = extractTreeOrNoTree(body)
      xt.Ensuring(b, post).setPos(post)

    case t @ ExComputesExpression(body, expected) =>
      val b = extractTreeOrNoTree(body).setPos(body.pos)
      val expectedExpr = extractTree(expected).setPos(expected.pos)
      val vd = xt.ValDef.fresh("res", extractType(body)).setPos(tr.pos)
      val post = xt.Lambda(Seq(vd), xt.Equals(vd.toVariable, expectedExpr)).setPos(tr.pos)
      xt.Ensuring(b, post).setPos(post)

    case ExPasses(in, out, cases) =>
      val ine = extractTree(in)
      val oute = extractTree(out)
      val rc = cases.map(extractMatchCase)

      xt.Passes(ine, oute, rc)

    case t @ ExBigLengthExpression(input) =>
      xt.StringLength(extractTree(input))

    case t @ ExBigSubstringExpression(input, start) =>
      val in = extractTree(input)
      val st = extractTree(start)
      val vd = xt.ValDef.fresh("s", xt.StringType().setPos(t.pos), true).setPos(t.pos)
      xt.Let(vd, in, xt.SubString(vd.toVariable, st, xt.StringLength(vd.toVariable).setPos(t.pos)).setPos(t.pos))

    case t @ ExBigSubstring2Expression(input, start, end) =>
      val in = extractTree(input)
      val st = extractTree(start)
      val en = extractTree(end)
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

    case ExOldExpression(t) => xt.Old(extractTree(t))

    case ExSnapshotExpression(t) => xt.Snapshot(extractTree(t))

    case ExErrorExpression(str, tpt) =>
      xt.Error(extractType(tpt), str)

    case ExTupleExtract(tuple, index) =>
      xt.TupleSelect(extractTree(tuple), index)

    /**
     * XLang Extractors
     */

    case a @ ExAssign(sym, rhs) =>
      // we assume type-correct code, so `sym` must be defined and in scope
      xt.Assignment(dctx.mutableVars(sym)().setPos(a.pos), extractTree(rhs))

    case a @ ExFieldAssign(sym, lhs@Select(thiss: This, _), rhs) =>
      xt.FieldAssignment(extractTree(thiss), getIdentifier(sym), extractTree(rhs))

    case wh @ ExWhile(cond, body) =>
      xt.While(extractTree(cond), extractTree(body), None)

    case wh @ ExWhileWithInvariant(cond, body, inv) =>
      xt.While(extractTree(cond), extractTree(body), Some(extractTree(inv)))

    case ExBigIntLiteral(n: Literal) =>
      xt.IntegerLiteral(BigInt(n.value.stringValue))

    case ExIntToBigInt(tree) =>
      extractTree(tree) match {
        case xt.Int32Literal(n) => xt.IntegerLiteral(BigInt(n))
        case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
      }

    case ExIntToBV(signed, size, tree) =>
      extractTree(tree) match {
        case xt.Int32Literal(n) => xt.BVLiteral(signed, BigInt(n), size)
        case _ => outOfSubsetError(tr, "`intToBV` implicit may only be used on `Int` literals")
      }

    case ExBigIntToBV(signed, size, tree) =>
      extractTree(tree) match {
        case xt.IntegerLiteral(n) => xt.BVLiteral(signed, n, size)
        case _ => outOfSubsetError(tr, "`bigIntToBV` implicit may only be used on `BigInt` literals")
      }

    case ExMaxBV(signed, size) =>
      if (signed) xt.BVLiteral(signed, (BigInt(2) pow (size - 1)) - 1, size)
      else xt.BVLiteral(signed,  (BigInt(2) pow size) - 1, size)

    case ExMinBV(signed, size) =>
      if (signed) xt.BVLiteral(signed, -(BigInt(2) pow (size - 1)), size)
      else xt.BVLiteral(signed, BigInt(0), size)

    case ExWrapping(tree) =>
      val body = extractTree(tree)(dctx.setWrappingArithmetic(true))
      xt.Annotated(body, Seq(xt.Wrapping))

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

    case ExTyped(ExtractorHelpers.ExSymbol("scala", "Predef", "$qmark$qmark$qmark"), tpe) =>
      xt.NoTree(extractType(tpe))

    case ExTyped(e, _) => extractTree(e)

    // References to parameterless case objects will have the form of an `Ident`
    case ex @ ExIdentifier(sym, tpt) if sym.isModule && sym.isCase =>
      extractType(tpt) match {
        case lct: xt.LocalClassType => xt.LocalClassConstructor(lct, Seq())
        case ct: xt.ClassType => xt.ClassConstructor(ct, Seq())
        case _ => outOfSubsetError(tr, "Unexpected constructor " + tr)
      }

    case ex @ ExIdentifier(sym, tpt) =>
      dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
        case Some(builder) => builder().setPos(ex.pos)
        case None => dctx.localFuns.get(sym) match {
          case Some((id, tparams, tpe)) =>
            assert(tparams.isEmpty, "Unexpected application " + ex + " without type parameters")
            xt.ApplyLetRec(id, Seq.empty, tpe, Seq.empty, Seq.empty)
          case None => xt.FunctionInvocation(getIdentifier(sym), Seq.empty, Seq.empty).setPos(ex.pos)
        }
      }

    case ExtractorHelpers.ExSymbol("scala", "Predef", "$qmark$qmark$qmark") => xt.NoTree(extractType(tr))

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
        case l: xt.Lambda => xt.Forall(l.params, l.body).setPos(l)
        case pred => extractType(contract) match {
          case xt.FunctionType(from, to) =>
            val args = from.map(tpe => xt.ValDef(FreshIdentifier("x", true), tpe).setPos(pred))
            xt.Forall(args, xt.Application(pred, args.map(_.toVariable)).setPos(pred))
          case _ =>
            outOfSubsetError(tr, "Unsupported forall definition: " + tr)
        }
      }

    case ExMutableMapWithDefault(tptFrom, tptTo, default) =>
      xt.MutableMapWithDefault(extractType(tptFrom), extractType(tptTo), extractTree(default))

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

    case ExClassConstruction(tpe, args) =>
      extractType(tpe)(dctx, tr.pos) match {
        case lct: xt.LocalClassType =>
          xt.LocalClassConstructor(lct, args.map(extractTree))
        case ct: xt.ClassType =>
          xt.ClassConstructor(ct, args.map(extractTree))
        case _ =>
          outOfSubsetError(tr, "Construction of a non-class type.")
      }

    case ExNot(e)    => xt.Not(extractTree(e))
    case ExUMinus(e) => injectCast(xt.UMinus)(e)
    case ExBVNot(e)  => injectCast(xt.BVNot)(e)

    case ExNotEquals(l, r) => xt.Not(((extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (bi @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(bi.toBigInt).setPos(l.pos), e)
      case (e, xt.IntegerType(), bi @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(bi.toBigInt).setPos(r.pos))

      case (l2, StrictBVType(signed, size), xt.IntegerLiteral(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, value, size).setPos(r.pos))
      case (l2, StrictBVType(signed, size), xt.Int32Literal(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, BigInt(value), size).setPos(r.pos))
      case (xt.IntegerLiteral(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, value, size).setPos(l.pos), r2)
      case (xt.Int32Literal(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, BigInt(value), size).setPos(l.pos), r2)

      case (l2, StrictBVType(_, _), r2, _) => xt.Equals(l2, r2)
      case (l2, _, r2, StrictBVType(_, _)) => xt.Equals(l2, r2)

      case _ => injectCasts(xt.Equals)(l, r)
    }).setPos(tr.pos))

    case ExEquals(l, r) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
      case (bi @ xt.BVLiteral(_, _, _), _, e, xt.IntegerType()) => xt.Equals(xt.IntegerLiteral(bi.toBigInt).setPos(l.pos), e)
      case (e, xt.IntegerType(), bi @ xt.BVLiteral(_, _, _), _) => xt.Equals(e, xt.IntegerLiteral(bi.toBigInt).setPos(r.pos))

      case (l2, StrictBVType(signed, size), xt.IntegerLiteral(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, value, size).setPos(r.pos))
      case (l2, StrictBVType(signed, size), xt.Int32Literal(value), _) =>
        xt.Equals(l2, xt.BVLiteral(signed, BigInt(value), size).setPos(r.pos))
      case (xt.IntegerLiteral(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, value, size).setPos(l.pos), r2)
      case (xt.Int32Literal(value), _, r2, StrictBVType(signed, size)) =>
        xt.Equals(xt.BVLiteral(signed, BigInt(value), size).setPos(l.pos), r2)

      case (l2, StrictBVType(_, _), r2, _) => xt.Equals(l2, r2)
      case (l2, _, r2, StrictBVType(_, _)) => xt.Equals(l2, r2)

      case _ => injectCasts(xt.Equals)(l, r)
    }

    case ExIfThenElse(t1,t2,t3) =>
      xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

    case ExAsInstanceOf(expr, tt) =>
      extractType(tt) match {
        case ct: xt.ClassType => xt.AsInstanceOf(extractTree(expr), ct)
        case lct: xt.LocalClassType => xt.AsInstanceOf(extractTree(expr), lct.toClassType)
        case _ => outOfSubsetError(tr, "asInstanceOf can only cast to class types")
      }

    case ExIsInstanceOf(expr, tt) =>
      extractType(tt) match {
        case ct: xt.ClassType => xt.IsInstanceOf(extractTree(expr), ct)
        case lct: xt.LocalClassType => xt.IsInstanceOf(extractTree(expr), lct.toClassType)
        case _ => outOfSubsetError(tr, "isInstanceOf can only be used with class types")
      }

    case pm @ ExPatternMatching(sel, cses) =>
      val rs = extractTree(sel)
      val rc = cses.map(extractMatchCase)
      xt.MatchExpr(rs, rc)

    case t: This =>
      extractType(t) match {
        case ct: xt.ClassType => xt.This(ct)
        case lct: xt.LocalClassType => xt.LocalThis(lct)
        case _ => outOfSubsetError(t, "Invalid usage of `this`")
      }

    case s: Super =>
      extractType(s) match {
        case ct: xt.ClassType => xt.Super(ct)
        case lct: xt.LocalClassType => xt.Super(lct.toClassType)

        case _ => outOfSubsetError(s, s"Invalid usage of `super`")
      }

    case ExArrayFill(baseType, length, defaultValue) =>
      val lengthRec = extractTree(length)
      val defaultValueRec = extractTree(defaultValue)
      xt.LargeArray(Map.empty, extractTree(defaultValue), extractTree(length), extractType(baseType))

    case ExArrayUpdate(array, index, newValue) =>
      xt.ArrayUpdate(extractTree(array), extractTree(index), extractTree(newValue))

    case ExArrayUpdated(array, index, newValue) =>
      xt.ArrayUpdated(extractTree(array), extractTree(index), extractTree(newValue))

    case ExArrayLength(array) =>
      xt.ArrayLength(extractTree(array))

    case ExArrayApply(array, index) => xt.ArraySelect(extractTree(array), extractTree(index))

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
      case None if sym.owner.isModuleClass && sym.owner.isCase =>
        val ct = extractType(sym.owner.tpe)(dctx, c.pos).asInstanceOf[xt.ClassType]
        xt.MethodInvocation(
          xt.This(ct).setPos(tr.pos),
          getIdentifier(sym),
          tps map extractType,
          args map extractTree
        ).setPos(tr.pos)

      case None =>
        dctx.localFuns.get(sym) match {
          case None =>
            xt.FunctionInvocation(getIdentifier(sym), tps.map(extractType), extractArgs(sym, args)).setPos(c.pos)
          case Some((id, tparams, tpe)) =>
            xt.ApplyLetRec(id, tparams.map(_.tp), tpe, tps.map(extractType), extractArgs(sym, args)).setPos(c.pos)
        }

      case Some(lhs) => stripAnnotationsExceptStrictBV(extractType(lhs)(dctx.setResolveTypes(true))) match {
        case ct: xt.ClassType =>
          val isField = sym.isParamAccessor || sym.isCaseAccessor
          val isMethod = sym.isMethod || sym.isAccessor || !isField

          if (isMethod) xt.MethodInvocation(
            extractTree(lhs),
            getIdentifier(sym),
            tps.map(extractType),
            extractArgs(sym, args)
          ).setPos(c.pos) else args match {
            case Seq() if sym.isParamAccessor =>
              xt.ClassSelector(extractTree(lhs), getIdentifier(sym)).setPos(c.pos)
            case _ =>
              outOfSubsetError(tr, s"Unexpected call: $tr")
          }

        case lct: xt.LocalClassType =>
          val isField = sym.isParamAccessor || sym.isCaseAccessor
          val isMethod = sym.isMethod || sym.isAccessor || !isField

          if (isMethod) {
            val lcd = dctx.localClasses(lct.id)
            val id = getIdentifier(sym)
            val fd = lcd.methods.find(_.id == id).get
            xt.LocalMethodInvocation(
              extractTree(lhs),
              xt.ValDef(id, xt.FunctionType(fd.params.map(_.tpe), fd.returnType)).toVariable,
              fd.tparams.map(_.tp),
              tps.map(extractType),
              extractArgs(sym, args)
            )
          } else args match {
            case Seq() if sym.isParamAccessor =>
              val lcd = dctx.localClasses(lct.id)
              val id = getIdentifier(sym)
              val field = lcd.fields.collectFirst { case vd @ xt.ValDef(`id`, _, _) => vd }
              xt.LocalClassSelector(extractTree(lhs), id, field.map(_.tpe).getOrElse(xt.Untyped))
          case _ =>
            outOfSubsetError(tr, "Unexpected call")
        }

        case ft: xt.FunctionType =>
          xt.Application(extractTree(lhs), args.map(extractTree)).setPos(ft)

        case tpe => (tpe, sym.name.decode.toString, args) match {
          case (xt.StringType(), "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
          case (xt.IntegerType() | xt.BVType(_, _) | xt.RealType(), "+", Seq(rhs)) => injectCasts(xt.Plus)(lhs, rhs)

          case (xt.SetType(_), "+",  Seq(rhs)) => xt.SetAdd(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "++", Seq(rhs)) => xt.SetUnion(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "&",  Seq(rhs)) => xt.SetIntersection(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "--", Seq(rhs)) => xt.SetDifference(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "subsetOf", Seq(rhs)) => xt.SubsetOf(extractTree(lhs), extractTree(rhs))
          case (xt.SetType(_), "contains", Seq(rhs)) => xt.ElementOfSet(extractTree(rhs), extractTree(lhs))
          case (xt.SetType(b), "isEmpty", Seq()) => xt.Equals(extractTree(lhs), xt.FiniteSet(Seq(), b))
          case (xt.SetType(b), "-", Seq(rhs))  => xt.SetDifference(extractTree(lhs), xt.FiniteSet(Seq(extractTree(rhs)), b).setPos(tr.pos))

          case (xt.BagType(_), "+",   Seq(rhs)) => xt.BagAdd(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "++",  Seq(rhs)) => xt.BagUnion(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "&",   Seq(rhs)) => xt.BagIntersection(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "--",  Seq(rhs)) => xt.BagDifference(extractTree(lhs), extractTree(rhs))
          case (xt.BagType(_), "get", Seq(rhs)) => xt.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

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
                getIdentifier(someSymbol.caseFieldAccessors.head.accessedOrSelf)
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

          case (xt.MapType(_, xt.ClassType(_, Seq(to))), "+", Seq(rhs)) =>
            val value = extractTree(rhs)
            xt.MapUpdated(
              extractTree(lhs), xt.TupleSelect(value, 1).setPos(tr.pos),
              xt.ClassConstructor(
                xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                Seq(xt.TupleSelect(value, 2).setPos(tr.pos))
              ).setPos(tr.pos)
            )

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
              case xt.FiniteMap(pairs,  default, keyType, valueType) =>
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
              getIdentifier(optionSymbol.tpe.member(TermName("getOrElse"))),
              Seq.empty,
              Seq(xt.Lambda(Seq(), extractTree(orElse)).setPos(tr.pos))
            ).setPos(c.pos)

          case (StrictBVType(_, _), "unary_-",  Seq())    => xt.UMinus(extractTree(lhs))
          case (StrictBVType(_, _), "+",        Seq(rhs)) => xt.Plus(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "-",        Seq(rhs)) => xt.Minus(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "*",        Seq(rhs)) => xt.Times(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "%",        Seq(rhs)) => xt.Remainder(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "mod",      Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "/",        Seq(rhs)) => xt.Division(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), ">",        Seq(rhs)) => xt.GreaterThan(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), ">=",       Seq(rhs)) => xt.GreaterEquals(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "<",        Seq(rhs)) => xt.LessThan(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "<=",       Seq(rhs)) => xt.LessEquals(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "|",        Seq(rhs)) => xt.BVOr(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "&",        Seq(rhs)) => xt.BVAnd(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "^",        Seq(rhs)) => xt.BVXor(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), "<<",       Seq(rhs)) => xt.BVShiftLeft(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), ">>",       Seq(rhs)) => xt.BVAShiftRight(extractTree(lhs), extractTree(rhs))
          case (StrictBVType(_, _), ">>>",      Seq(rhs)) => xt.BVLShiftRight(extractTree(lhs), extractTree(rhs))

          case (StrictBVType(signed, size), "widen",  Seq()) => tps match {
            case Seq(FrontendBVType(signed2, size2)) =>
              if (signed2 != signed) outOfSubsetError(tr, "Method `widen` must be used with a bitvector type of the same sign")
              else if (size2 <= size) outOfSubsetError(tr, "Method `widen` must be used with a bitvector type of a larger size")
              else xt.BVWideningCast(extractTree(lhs), xt.BVType(signed2, size2))
          }
          case (StrictBVType(signed, size), "narrow",  Seq()) => tps match {
            case Seq(FrontendBVType(signed2, size2)) =>
              if (signed2 != signed) outOfSubsetError(tr, "Method `narrow` must be used with a bitvector type of the same sign")
              else if (size2 >= size) outOfSubsetError(tr, "Method `narrow` must be used with a bitvector type of a smaller size")
              else xt.BVNarrowingCast(extractTree(lhs), xt.BVType(signed2, size2))
          }

          case (StrictBVType(signed, size), "toSigned",  Seq()) => tps match {
            case Seq(FrontendBVType(signed2, size2)) =>
              if (signed) outOfSubsetError(tr, "Method `toSigned` must be used on unsigned bitvectors")
              else if (!signed2) outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type")
              else if (size != size2) outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type of the same size as the original bitvector")
              else xt.BVUnsignedToSigned(extractTree(lhs))
            case _ =>
              outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type of the same size as the original bitvector")
          }
          case (StrictBVType(signed, size), "toUnsigned",  Seq()) => tps match {
            case Seq(FrontendBVType(signed2, size2)) =>
              if (!signed) outOfSubsetError(tr, "Method `toUnsigned` must be used on signed bitvectors")
              else if (signed2) outOfSubsetError(tr, "Method `toUnsigned` must be instantiated with a unsigned bitvector type")
              else if (size != size2) outOfSubsetError(tr, "Method `toUnsigned` must be instantiated with a unsigned bitvector type of the same size as the original bitvector")
              else xt.BVSignedToUnsigned(extractTree(lhs))
            case _ =>
              outOfSubsetError(tr, "Method `toSigned` must be instantiated with a signed bitvector type of the same size as the original bitvector")
          }

          case (StrictBVType(signed, size), "toByte",  Seq()) =>
            if (!signed || size != 8) outOfSubsetError(tr, "Method `toByte` can only be used on a Int8")
            else extractTree(lhs)
          case (StrictBVType(signed, size), "toShort",  Seq()) =>
            if (!signed || size != 16) outOfSubsetError(tr, "Method `toShort` can only be used on a Int16")
            else extractTree(lhs)
          case (StrictBVType(signed, size), "toInt",  Seq()) =>
            if (!signed || size != 32) outOfSubsetError(tr, "Method `toShort` can only be used on a Int32")
            else extractTree(lhs)
          case (StrictBVType(signed, size), "toLong",  Seq()) =>
            if (!signed || size != 64) outOfSubsetError(tr, "Method `toShort` can only be used on a Int64")
            else extractTree(lhs)

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

          case (xt.BVType(_, _), "|",   Seq(rhs)) => injectCasts(xt.BVOr)(lhs, rhs)
          case (xt.BVType(_, _), "&",   Seq(rhs)) => injectCasts(xt.BVAnd)(lhs, rhs)
          case (xt.BVType(_, _), "^",   Seq(rhs)) => injectCasts(xt.BVXor)(lhs, rhs)
          case (xt.BVType(_, _), "<<",  Seq(rhs)) => injectCastsForShift(xt.BVShiftLeft)(lhs, rhs)
          case (xt.BVType(_, _), ">>",  Seq(rhs)) => injectCastsForShift(xt.BVAShiftRight)(lhs, rhs)
          case (xt.BVType(_, _), ">>>", Seq(rhs)) => injectCastsForShift(xt.BVLShiftRight)(lhs, rhs)

          case (xt.BooleanType(), "|", Seq(rhs)) => xt.BoolBitwiseOr(extractTree(lhs), extractTree(rhs))
          case (xt.BooleanType(), "&", Seq(rhs)) => xt.BoolBitwiseAnd(extractTree(lhs), extractTree(rhs))
          case (xt.BooleanType(), "^", Seq(rhs)) => xt.BoolBitwiseXor(extractTree(lhs), extractTree(rhs))

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
            outOfSubsetError(tr, "Unknown call to " + name +
              s" on $lhs (${extractType(lhs)}) with arguments $args of type ${args.map(a => extractType(a))}")
        }
      }
    }

    // default behaviour is to complain :)
    case _ => outOfSubsetError(tr, s"Stainless does not support expression (${tr.getClass}): `$tr`")
  }).ensurePos(tr.pos)

  /** Inject implicit widening casts according to the Java semantics (5.6.2. Binary Numeric Promotion) */
  private def injectCasts(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                         (lhs0: Tree, rhs0: Tree)
                         (implicit dctx: DefContext): xt.Expr = {
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
                                 (lhs0: Tree, rhs0: Tree)
                                 (implicit dctx: DefContext): xt.Expr = {
    injectCastsImpl(ctor)(lhs0, rhs0, shift = true)
  }

  private def injectCastsImpl(ctor: (xt.Expr, xt.Expr) => xt.Expr)
                             (lhs0: Tree, rhs0: Tree, shift: Boolean)
                             (implicit dctx: DefContext): xt.Expr = {
    def checkBits(tr: Tree, tpe: xt.Type) = tpe match {
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

    val id = { e: xt.Expr => e }
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

      case (xt.BVType(_, _), _) | (_, xt.BVType(_, _)) =>
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
    val widen32 = { (e: xt.Expr) => xt.BVWideningCast(e, xt.Int32Type().copiedFrom(e)).copiedFrom(e) }

    val ector = etpe match {
      case xt.BVType(true, 8 | 16) => widen32
      case xt.BVType(true, 32 | 64) => id
      case xt.BVType(_, s) => outOfSubsetError(e0, s"Unexpected integer type of $s bits")
      case _ => id
    }

    ctor(ector(e))
  }

  private def extractLocalClassType(sym: Symbol, cid: Identifier, tps: List[xt.Type])
                                   (implicit dctx: DefContext, pos: Position): xt.LocalClassType = {

    val tparamsSyms = typeParamSymbols(sym.tpe.typeArgs)
    val tparams = extractTypeParams(tparamsSyms)

    val tpCtx = dctx.copy(tparams = dctx.tparams ++ (tparamsSyms zip tparams).toMap)
    val parents = sym.tpe.parents.filterNot(ignoredClasses).map(extractType(_)(tpCtx, pos))

    xt.LocalClassType(cid, tparams.map(xt.TypeParameterDef(_)), tps, parents)
  }

  private def extractType(t: Tree)(implicit dctx: DefContext): xt.Type = {
    extractType(t.tpe)(dctx, t.pos)
  }

  object StrictBVType {
    def unapply(tpe: xt.Type): Option[(Boolean, Int)] = tpe match {
      case xt.AnnotatedType(xt.BVType(signed, size), flags) if flags.contains(xt.StrictBV) =>
        Some((signed , size))
      case _ => None
    }
  }

  private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = (tpt match {
    case CharTpe    => xt.CharType()
    case ByteTpe    => xt.Int8Type()
    case ShortTpe   => xt.Int16Type()
    case IntTpe     => xt.Int32Type()
    case LongTpe    => xt.Int64Type()
    case BooleanTpe => xt.BooleanType()
    case UnitTpe    => xt.UnitType()
    case AnyTpe     => xt.AnyType()
    case NothingTpe => xt.NothingType()

    case ct: ConstantType =>
      extractType(ct.value.tpe)

    case TypeBounds(lo, hi) =>
      xt.TypeBounds(extractType(lo), extractType(hi), Seq.empty)

    case TypeRef(_, sym, _) if isBigIntSym(sym) => xt.IntegerType()
    case TypeRef(_, sym, _) if isRealSym(sym)   => xt.RealType()
    case TypeRef(_, sym, _) if isStringSym(sym) => xt.StringType()

    case TypeRef(_, sym, btt :: Nil) if isSetSym(sym) =>
      xt.SetType(extractType(btt))

    case TypeRef(_, sym, btt :: Nil) if isBagSym(sym) =>
      xt.BagType(extractType(btt))

    case FrontendBVType(signed, size) =>
      xt.AnnotatedType(xt.BVType(signed, size), Seq(xt.StrictBV))

    case TypeRef(_, sym, List(ftt,ttt)) if isMapSym(sym) =>
      xt.MapType(extractType(ftt), xt.ClassType(getIdentifier(optionSymbol), Seq(extractType(ttt))).setPos(pos))

    case TypeRef(_, sym, List(ftt,ttt)) if isMutableMapSym(sym) =>
      xt.MutableMapType(extractType(ftt), extractType(ttt))

    case TypeRef(_, sym, tps) if isTuple(sym, tps.size) =>
      xt.TupleType(tps map extractType)

    case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
      xt.ArrayType(extractType(btt))

    case TypeRef(_, sym, subs) if subs.nonEmpty && isFunction(sym, subs.size - 1) =>
      val from = subs.init
      val to   = subs.last
      xt.FunctionType(from map extractType, extractType(to))

    case TypeRef(_, sym, tps) if isByNameSym(sym) =>
      extractType(tps.head)

    case TypeRef(_, sym, _) if sym.isAbstractType && (dctx.tparams contains sym) =>
      dctx.tparams(sym)

    case tr @ TypeRef(_, sym, tps) if sym.isClass =>
      val id = getIdentifier(sym)
      dctx.localClasses.get(id) match {
        case Some(lcd) => extractLocalClassType(sym, lcd.id, tps map extractType)
        case None => xt.ClassType(id, tps map extractType)
      }

    case tr @ TypeRef(_, sym, tps) if dctx.resolveTypes && (sym.isAliasType || sym.isAbstractType) =>
      if (tr != tr.dealias) extractType(tr.dealias)
      else extractType(tr)(dctx.setResolveTypes(false), pos)

    case tr @ TypeRef(prefix, sym, tps) if sym.isAbstractType || sym.isAliasType =>
      val selector = prefix match {
        case _ if prefix.typeSymbol.isModuleClass =>
          None
        case thiss: ThisType =>
          val id = getIdentifier(thiss.sym)
          dctx.localClasses.get(id) match {
            case Some(lcd) => Some(xt.LocalThis(extractType(thiss).asInstanceOf[xt.LocalClassType]))
            case None => Some(xt.This(extractType(thiss).asInstanceOf[xt.ClassType]))
          }
        case SingleType(_, sym) if dctx.vars contains sym =>
          Some(dctx.vars(sym)())
        case SingleType(_, sym) =>
          ctx.reporter.internalError(s"extractType: could not find variable $sym in context")
        case _ =>
          None
      }

      xt.TypeApply(xt.TypeSelect(selector, getIdentifier(sym)), tps map extractType)

    case tt: ThisType =>
      val id = getIdentifier(tt.sym)
      val params = tt.sym.typeParams.map(dctx.tparams)
      dctx.localClasses.get(id) match {
        case Some(lcd) => extractLocalClassType(tt.sym, lcd.id, params)
        case None => xt.ClassType(id, params)
      }

    case st @ SuperType(thisTpe, superTpe) =>
      extractType(superTpe)

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
      parents.find(ptpe => !ignoredClasses.contains(ptpe)).map(extractType) match {
        case Some(tpe) =>
          tpe

        case None =>
          outOfSubsetError(tpt.typeSymbol.pos, s"Stainless does not support type $tpt")
      }

    case AnnotatedType(Seq(ExIndexedAt(n)), tpe) =>
      xt.AnnotatedType(extractType(tpe), Seq(xt.IndexedAt(extractTree(n))))

    case AnnotatedType(_, tpe) => extractType(tpe)

    case _ =>
      if (tpt ne null) {
        outOfSubsetError(tpt.typeSymbol.pos, s"Stainless does not support type $tpt")
        throw new Exception()
      } else {
        outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
      }
  }).setPos(pos)

}

