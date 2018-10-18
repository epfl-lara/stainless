/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.language.existentials

trait Sealing extends oo.CachingPhase
  with IdentitySorts
  with MutabilityAnalyzer { self =>


  /* ====================================
   *       Context and caches setup
   * ==================================== */

  import s._
  import s.exprOps._

  protected class TransformerContext(implicit symbols: Symbols) extends MutabilityAnalysis()(symbols) {
    def mustDuplicate(fd: FunDef): Boolean = {
      !fd.isAbstract &&
      !fd.isFinal &&
      !fd.isAccessor &&
      !fd.isInvariant &&
      fd.flags.exists {
        case IsMethodOf(cid) =>
          val cd = symbols.getClass(cid)
          cd.isAbstract && !cd.isSealed
        case _ => false
      }
    }

    // Given a (non-sealed) class, we lookup in the ancestors all methods that are
    // not final and not invariants in order to override them in the dummy class
    private[this] def latestNonFinalMethods(cd: ClassDef): Set[SymbolIdentifier] =
      (cd +: cd.ancestors.map(_.cd)).reverse.foldLeft(Map[Symbol, SymbolIdentifier]()) {
        case (lnfm, cd) =>
          val methods = cd.methods
          val newMethods = methods
            .filterNot(id => symbols.getFunction(id).isFinal)
            .filterNot(id => symbols.getFunction(id).isInvariant)
            .map(id => id.symbol -> id)
          lnfm -- methods.map(_.symbol) ++ newMethods
      }.values.toSet

    val lnfm: Map[ClassDef, Set[SymbolIdentifier]] = {
      symbols.classes.map { case (cid, cd) =>
        cd -> latestNonFinalMethods(cd)
      }
    }

    // We build dummy subclasses for abstract classes that are not sealed
    def mustAddSubclass(cd: ClassDef) = !cd.isSealed && cd.isAbstract

    private[this] val extID = new utils.ConcurrentCached[Identifier, Identifier](id => FreshIdentifier(id.name + "Ext"))

    // Create a dummy subclass for a given (non-sealed) class
    def buildDummySubclass(cd: ClassDef, accessedFields: Seq[ValDef]): (ClassDef, Map[TypeParameter, TypeParameter]) = {
      val pos = cd.getPos
      val mutableFlag = cd.flags.filter(_ == IsMutable)
      val varFlag = if (mutableFlag.isEmpty) Seq() else Seq(IsVar)
      val dummyField = ValDef(FreshIdentifier("__x"), IntegerType().setPos(pos), varFlag).setPos(pos)
      val typeArgs = freshenTypeParams(cd.typeArgs)
      val tparams = typeArgs.map(TypeParameterDef(_))
      val tpSubst = (cd.typeArgs zip typeArgs).toMap
      val dummyClass =
        Substituter(tpSubst).transform(new ClassDef(
          extID(cd.id),
          tparams, // same type parameters as `cd`
          Seq(ClassType(cd.id, typeArgs)), // parent is `cd`
          Seq(dummyField) ++ accessedFields, // we add fields for the accessors
          Synthetic +: mutableFlag
        ).setPos(pos))
      (dummyClass, tpSubst)
    }

    // These are the flags that we keep when overriding a method
    private[this] def overrideKeepFlags(flag: Flag) = flag match {
      case IsPure => true
      case Annotation("library", Seq()) => true
      case _ => false
    }

    // Create an abstract method for the dummy subclass to override a non-final method
    def overrideMethod(fid: SymbolIdentifier, cid: Identifier, tpSubst: Map[TypeParameter, TypeParameter]): FunDef = {
      val fd = symbols.getFunction(fid)
      val (specs, _) = deconstructSpecs(fd.fullBody)
      Substituter(tpSubst).transform(exprOps.freshenSignature(new FunDef(
        ast.SymbolIdentifier(fid.symbol),
        fd.tparams,
        fd.params,
        fd.returnType,
        reconstructSpecs(specs, None, fd.returnType),
        fd.flags.filter(overrideKeepFlags) ++ Seq(Extern, Derived(fd.id), Synthetic, IsMethodOf(cid))
      ).setPos(fd)))
    }

    // For each accessor, we create a concrete accessor that operates on a fresh field
    def buildSetter(fid: SymbolIdentifier, ct: ClassType, field: ValDef, tpSubst: Map[TypeParameter, TypeParameter]): FunDef = {
      val fd = symbols.getFunction(fid)
      Substituter(tpSubst).transform(exprOps.freshenSignature(new FunDef(
        ast.SymbolIdentifier(fid.symbol),
        fd.tparams,
        fd.params,
        fd.returnType,
        FieldAssignment(This(ct), field.id, fd.params.head.toVariable),
        Seq(Synthetic, IsMethodOf(ct.id), Derived(fd.id), IsAccessor(Some(field.id)))
      ).copiedFrom(fd)))
    }

    // For each accessor, we create a concrete accessor that operates on a fresh field
    def buildGetter(fid: SymbolIdentifier, ct: ClassType, field: ValDef, tpSubst: Map[TypeParameter, TypeParameter]): FunDef = {
      val fd = symbols.getFunction(fid)
      Substituter(tpSubst).transform(exprOps.freshenSignature(new FunDef(
        ast.SymbolIdentifier(fid.symbol),
        fd.tparams,
        fd.params,
        fd.returnType,
        ClassSelector(This(ct), field.id),
        Seq(Synthetic, IsMethodOf(ct.id), Derived(fd.id), Final, IsAccessor(Some(field.id)))
      ).copiedFrom(fd)))
    }
  }

  override protected def getContext(syms: Symbols) = new TransformerContext()(syms)

  // For each class, we add a sealed flag, and optionally add a dummy subclass
  // with the corresponding methods
  override protected type ClassResult = (ClassDef, Option[ClassDef], Seq[FunDef])

  override protected final val classCache = new ExtractionCache[ClassDef, ClassResult]({ (cd, context) =>
    val symbols = context.symbols
    ClassKey(cd) + ValueKey(context.mustAddSubclass(cd)) + ValueKey(context.isMutable(cd)) + SetKey(
      if (context.mustAddSubclass(cd))
        context.lnfm(cd).toSet[Identifier]
      else
        Set[Identifier]()
    )(symbols)
  })

  // Each concrete method of non-sealed class is duplicated to make sure it does
  // not disappear after MethodLifting (if the original contained assertions, we
  // want to check them).
  override protected type FunctionResult = (FunDef, Option[FunDef])

  override protected final val funCache = new ExtractionCache[FunDef, FunctionResult]({ (fd, context) =>
    FunctionKey(fd) + ValueKey(context.mustDuplicate(fd))
  })


  /* ====================================
   *    Substituter of type parameters
   * ==================================== */

  case class Substituter(mapping: Map[TypeParameter, TypeParameter]) extends s.SelfTreeTransformer {
    override def transform(tpe: Type): Type = tpe match {
      case tp: TypeParameter if mapping contains tp => mapping(tp)
      case _ => super.transform(tpe)
    }
  }


  /* ====================================
   *         Extraction of classes
   * ==================================== */

  // For each non-sealed class, we create a subclass that overrides every
  // non-final method with an abstract method with no body.
  // For the getters and setters, we create fields and we create concrete
  // setters and getters that operate on those fields.
  override protected def extractClass(context: TransformerContext, cd: ClassDef): ClassResult = {
    val syms = context.symbols
    val flagsWithMutable = if (context.isMutable(cd))
      (cd.flags :+ IsMutable).distinct
    else
      cd.flags

    if (context.mustAddSubclass(cd)) {
      val newCd = cd.copy(flags = (flagsWithMutable :+ IsSealed).distinct).copiedFrom(cd)

      // We lookup the latest non-final methods, and split them in three groups:
      // normal methods, setters, and getters
      val lnfm = context.lnfm(cd).toSeq
      val (accessors, methods) = lnfm.partition(id => syms.getFunction(id).isAccessor)
      val (setters, getters) = accessors.partition(id => syms.getFunction(id).isSetter)

      // we drop the '_=' suffix to get the name of the field
      val settersNames: Map[String, SymbolIdentifier] = setters.map(fid => fid.name.dropRight(2) -> fid).toMap
      val gettersNames: Map[String, SymbolIdentifier] = getters.map(fid => fid.name -> fid).toMap

      // For symbols that are referenced by setters, we create var fields
      val varFields: Map[String, ValDef] =
        settersNames.map { case (name,fid) =>
          val setter = syms.getFunction(fid)
          val Seq(vd) = setter.params
          name -> VarDef(FreshIdentifier(name), vd.tpe, Seq())
        }.toMap

      // For symbols that are only referenced by getters, we create val fields
      val valFields: Map[String, ValDef] =
        (gettersNames -- settersNames.keySet).map { case (name,fid) =>
          val getter = syms.getFunction(fid)
          val tpe = getter.returnType
          name -> ValDef(FreshIdentifier(name), tpe, Seq())
        }.toMap

      assert((valFields.keySet & varFields.keySet).isEmpty, "valFields and varFields must be disjoint")

      val allFields = varFields ++ valFields

      // We create the new dummy class with all the fields
      val (dummyClass, tpSubst) = context.buildDummySubclass(cd, allFields.values.toSeq)
      val ct = dummyClass.typed(syms).toType

      // We build the concrete accessors to operate on the new fields
      val newSetters = varFields.map { case (name, vd) => context.buildSetter(settersNames(name), ct, vd, tpSubst) }
      // For `varFields`, we build a new getter only if there is a already a getter
      val newGetters1 = varFields.collect {
        case (name, vd) if gettersNames.contains(name) =>
          context.buildGetter(gettersNames(name), ct, vd, tpSubst)
      }
      val newGetters2 = valFields.map { case (name, vd) => context.buildGetter(gettersNames(name), ct, vd, tpSubst) }

      // For the normal methods, we create overrides with no body
      val dummyOverrides = methods.map(fid => context.overrideMethod(fid, dummyClass.id, tpSubst))

      (newCd, Some(dummyClass), dummyOverrides ++ newSetters ++ newGetters1 ++ newGetters2)
    }
    else if (context.isMutable(cd))
      (cd.copy(flags = flagsWithMutable).copiedFrom(cd), None, Seq())
    else
      (cd, None, Seq())
  }


  /* ====================================
   *         Extraction of functions
   * ==================================== */

  private[this] def duplicate(fd: FunDef): FunDef = {
    exprOps.freshenSignature(fd.copy(
      id = ast.SymbolIdentifier(fd.id.name),
      flags = fd.flags :+ Derived(fd.id)
    ).copiedFrom(fd))
  }

  // We duplicate concrete non-final/accessor/field/invariant functions of non-sealed classes
  override protected def extractFunction(context: TransformerContext, fd: FunDef): FunctionResult = {
    if (context.mustDuplicate(fd)) (fd, Some(duplicate(fd)))
    else if (fd.isFinal) (fd.copy(flags = fd.flags.filterNot(_ == Final)).copiedFrom(fd), None)
    else (fd, None)
  }


  /* ====================================
   *             Registration
   * ==================================== */

  override protected def registerClasses(syms: Symbols, results: Seq[ClassResult]): Symbols =
    syms
      .withClasses(results.flatMap(cr => cr._1 +: cr._2.toSeq))
      .withFunctions(results.flatMap(_._3))

  override protected def registerFunctions(syms: Symbols, results: Seq[FunctionResult]): Symbols =
    syms.withFunctions(results.flatMap(fr => fr._1 +: fr._2.toSeq))
}

object Sealing {
  def apply(tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = new Sealing {
    override val s: tt.type = tt
    override val t: tt.type = tt
    override val context = ctx
  }
}
