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

  private[this] val extID = new utils.ConcurrentCached[Identifier, Identifier](id => FreshIdentifier(id.name + "Ext"))

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

    // We build dummy subclasses for abstract classes that are not sealed
    def mustAddSubclass(cd: ClassDef) = !cd.isSealed && cd.isAbstract

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
   *         Extraction of classes
   * ==================================== */

  // For each non-sealed class, we create a subclass that overrides every
  // non-final method with an abstract method with no body.
  // For the getters and setters, we create fields and we create concrete
  // setters and getters that operate on those fields.
  override protected def extractClass(context: TransformerContext, cd: ClassDef): ClassResult = {
    import context.symbols

    if (context.mustAddSubclass(cd)) {
      val newCd = cd.copy(flags = (cd.flags :+ IsSealed).distinct).copiedFrom(cd)

      val typeArgs = freshenTypeParams(cd.typeArgs)
      val classSubst = (cd.typeArgs zip typeArgs).toMap

      // We lookup the latest non-final methods, and split them in three groups:
      // normal methods, setters, and getters
      val lnfm = context.lnfm(cd).toSeq
      val (accessors, methods) = lnfm.partition(id => symbols.getFunction(id).isAccessor)

      // we drop the '_=' suffix from the setter name to get the name of the field
      def fieldName(fd: FunDef): String = if (fd.isSetter) fd.id.name.dropRight(2) else fd.id.name
      val setterNames = accessors.map(symbols.getFunction(_)).filter(_.isSetter).map(fieldName).toSet

      val getters = accessors.map(symbols.getFunction(_)).filter(_.isGetter)

      // Return a type instantiator that will substitute the type parameters in the given
      // function's signature/body by the relevant types based on the new dummy class
      def getInstantiator(fd: FunDef) = new typeOps.TypeInstantiator(fd.flags.collectFirst {
        case IsMethodOf(cid) =>
          val acd = (cd.typed +: cd.ancestors).find(_.id == cid).get
          (acd.cd.typeArgs zip acd.tps).map { case (tp, tpe) =>
            tp -> typeOps.instantiateType(tpe, classSubst)
          }.toMap
      }.get)

      // These are the flags that we *discard* when overriding an accessor or a methodand creating a field
      def overrideDiscardFlag(flag: Flag) = flag match {
        case IsAbstract => true
        case IsAccessor(_) => true
        case IsMethodOf(_) => true
        case _ => false
      }

      // These are the flags that we *keep* when creating a field for an accessor
      def fieldKeepFlag(flag: Flag) = flag match {
        case Ghost => true
        case _ => false
      }

      // For symbols that are referenced by setters, we will create var fields,
      // and for symbols that are only referenced by getters, we create val fields
      val fields = getters.map { fd =>
        val id = fd.id.freshen
        val tpe = getInstantiator(fd).transform(fd.returnType)
        val flags = fd.flags.filter(fieldKeepFlag)
        if (setterNames(fd.id.name)) {
          VarDef(id, tpe, flags).copiedFrom(fd)
        } else {
          ValDef(id, tpe, flags).copiedFrom(fd)
        }
      }

      // Create a dummy subclass for the current class
      val dummyClass: ClassDef = {
        val varFlag = if (context.isMutable(cd)) Seq(IsVar) else Seq()
        val dummyField = ValDef(FreshIdentifier("__x"), IntegerType().setPos(cd), varFlag).setPos(cd)
        new ClassDef(
          extID(cd.id),
          typeArgs.map(tp => TypeParameterDef(tp).copiedFrom(tp)),
          Seq(ClassType(cd.id, typeArgs).setPos(cd)), // parent is `cd`
          Seq(dummyField) ++ fields, // we add fields for the accessors
          (cd.flags.filterNot(_ == IsAbstract) :+ Synthetic).distinct
        ).setPos(cd)
      }

      val fieldsByName: Map[String, ValDef] = fields.map(vd => vd.id.name -> vd).toMap

      // For each accessor, we create a concrete accessor that operates on the new synthetic field
      val newAccessors = accessors.map { id =>
        val fd = symbols.getFunction(id)
        val vd = fieldsByName(fieldName(fd))
        val instantiator = getInstantiator(fd)

        val ct = ClassType(dummyClass.id, cd.typeArgs).setPos(fd)
        val thiss = This(ct).setPos(fd)
        val newFlags = fd.flags.filterNot(overrideDiscardFlag) ++
          Seq(Synthetic, IsMethodOf(ct.id), Derived(id), IsAccessor(Some(vd.id)))
        instantiator.transform(exprOps.freshenSignature(if (fd.isSetter) {
          fd.copy(
            id = ast.SymbolIdentifier(id.symbol),
            fullBody = FieldAssignment(thiss, vd.id, fd.params.head.toVariable).setPos(fd),
            flags = newFlags
          )
        } else {
          fd.copy(
            id = ast.SymbolIdentifier(id.symbol),
            fullBody = ClassSelector(thiss, vd.id).setPos(fd),
            flags = newFlags
          )
        }))
      }

      // For the normal methods, we create overrides with no body
      val dummyOverrides = methods.map { id =>
        val fd = symbols.getFunction(id)
        val instantiator = getInstantiator(fd)
        val (specs, _) = deconstructSpecs(fd.fullBody)
        instantiator.transform(exprOps.freshenSignature(fd.copy(
          id = ast.SymbolIdentifier(id.symbol),
          fullBody = reconstructSpecs(specs, None, fd.returnType),
          flags = (
            fd.flags.filterNot(overrideDiscardFlag) ++
              Seq(Extern, Derived(id), Synthetic, IsMethodOf(dummyClass.id))
          ).distinct
        )))
      }

      (newCd, Some(dummyClass), dummyOverrides ++ newAccessors)
    }
    else (cd, None, Seq())
  }


  /* ====================================
   *         Extraction of functions
   * ==================================== */

  private[this] def duplicate(fd: FunDef): FunDef = {
    exprOps.freshenSignature(fd.copy(
      id = ast.SymbolIdentifier(fd.id.name),
      flags = (fd.flags :+ Derived(fd.id)).distinct
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
