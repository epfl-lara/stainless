/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

class Sealing(override val s: Trees)(override val t: s.type)
             (using override val context: inox.Context)
  extends oo.CachingPhase
     with IdentitySorts
     with oo.IdentityTypeDefs
     with MutabilityAnalyzer  { self =>


  /* ====================================
   *       Context and caches setup
   * ==================================== */

  import s._
  import s.exprOps._

  private[this] val extID = new utils.ConcurrentCached[Identifier, Identifier](id => FreshIdentifier(id.name + "Ext"))

  protected class TransformerContext(using symbols: Symbols) extends MutabilityAnalysis {
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

    // Annotate parameters of non-mutable type with `@pure`
    def addPurityAnnotations(fd: FunDef): FunDef = {
      val pureParams = fd.params
        .filter(vd => !isMutableType(vd.getType(using symbols)))
        .map(vd => vd.id -> vd.copy(flags = (vd.flags :+ IsPure).distinct).copiedFrom(vd))
        .toMap

      val (paramSubst, params) = fd.params
        .foldLeft((Map.empty[Variable, Expr], Seq.empty[ValDef])) { case ((paramSubst, params), vd) =>
          val ntpe = symbols.replaceKeepPositions(paramSubst, vd.tpe)
          val nvd = pureParams.getOrElse(vd.id, vd).copy(tpe = ntpe).copiedFrom(vd)
          (paramSubst + (vd.toVariable -> nvd.toVariable), params :+ nvd)
        }

      fd.copy(
        params = params,
        returnType = symbols.replaceKeepPositions(paramSubst, fd.returnType),
        fullBody = exprOps.replaceKeepPositions(paramSubst, fd.fullBody)
      ).copiedFrom(fd)
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
  }

  override protected def getContext(syms: Symbols) = new TransformerContext()(using syms)

  // For each class, we add a sealed flag, and optionally add a dummy subclass
  // with the corresponding methods
  override protected type ClassResult = (ClassDef, Option[ClassDef], Seq[FunDef], Seq[TypeDef])

  override protected final val classCache = new ExtractionCache[ClassDef, ClassResult]({ (cd, context) =>
    val symbols = context.symbols
    ClassKey(cd) + ValueKey(context.mustAddSubclass(cd)) + ValueKey(context.isMutable(cd)) + SetKey(
      if (context.mustAddSubclass(cd))
        context.lnfm(cd).toSet[Identifier]
      else
        Set[Identifier]()
    )(using symbols)
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
    val symbols = context.symbols
    import symbols.{given, _}

    if (context.mustAddSubclass(cd)) {
      val newCd = cd.copy(flags = (cd.flags :+ IsSealed).distinct).copiedFrom(cd)

      val typeArgs = freshenTypeParams(cd.typeArgs)
      val classSubst = (cd.typeArgs zip typeArgs).toMap

      // We lookup the latest non-final methods, and split them in three groups:
      // normal methods, setters, and getters
      val lnfm = context.lnfm(cd).toSeq
      val (accessors, methods) = lnfm.partition { id =>
        val fd = symbols.getFunction(id)
        fd.isAccessor && !typeOps.exists {
          case TypeSelect(Some(This(ct)), _) => ct.id == cd.id
          case _ => false
        } (fd.returnType) // We don't want to add fields for vals which are path-dependent on `this`,
                          // because this is invalid in Scala (ie. fields cannot refer to `this`).
      }

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

      // These are the flags that we *discard* when overriding an accessor or a method and creating a field
      def overrideDiscardFlag(flag: Flag) = flag match {
        case IsAbstract           => true
        case IsAccessor(_)        => true
        case IsMethodOf(_)        => true
        case IsTypeMemberOf(_)    => true
        case FieldDefPosition(_)  => true
        case _                    => false
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
          Seq(Synthetic, IsMethodOf(ct.id), Derived(Some(id)), IsAccessor(Some(vd.id)))

        val accessor = exprOps.freshenSignature(if (fd.isSetter) {
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
        })

        context.addPurityAnnotations(instantiator.transform(accessor))
      }

      // For the normal methods, we create overrides with no body
      val dummyFunOverrides = methods.map { id =>
        val fd = symbols.getFunction(id)
        val instantiator = getInstantiator(fd)
        val (specs, _) = deconstructSpecs(fd.fullBody)

        val dummy = exprOps.freshenSignature(fd.copy(
          id = ast.SymbolIdentifier(id.symbol),
          fullBody = reconstructSpecs(specs, None, fd.returnType),
          flags = (
            fd.flags.filterNot(overrideDiscardFlag) ++
              Seq(Extern, Derived(Some(id)), Synthetic, IsMethodOf(dummyClass.id))
          ).distinct
        ))

        context.addPurityAnnotations(instantiator.transform(dummy))
      }

      val dummyTypeDefOverrides = cd.typeMembers.map { id =>
        val td = symbols.getTypeDef(id)
        td.copy(
          id = ast.SymbolIdentifier(id.symbol),
          rhs = TypeBounds(NothingType(), AnyType(), Seq.empty),
          flags = (
            td.flags.filterNot(overrideDiscardFlag) ++
            Seq(IsAbstract, Derived(Some(td.id)), Synthetic, IsTypeMemberOf(dummyClass.id))
          ).distinct
        )
      }

      (newCd, Some(dummyClass), dummyFunOverrides ++ newAccessors, dummyTypeDefOverrides)
    }
    else (cd, None, Seq.empty, Seq.empty)
  }


  /* ====================================
   *         Extraction of functions
   * ==================================== */

  private[this] def duplicate(fd: FunDef): FunDef = {
    exprOps.freshenSignature(fd.copy(
      id = ast.SymbolIdentifier(fd.id.name),
      flags = (fd.flags :+ Derived(Some(fd.id))).distinct
    ).copiedFrom(fd))
  }

  // We duplicate concrete non-final/accessor/field/invariant functions of non-sealed classes
  override protected def extractFunction(context: TransformerContext, orig: FunDef): FunctionResult = {
    val fd = context.addPurityAnnotations(orig)
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
      .withTypeDefs(results.flatMap(_._4))

  override protected def registerFunctions(syms: Symbols, results: Seq[FunctionResult]): Symbols =
    syms.withFunctions(results.flatMap(fr => fr._1 +: fr._2.toSeq))
}

object Sealing {
  def apply(tt: Trees)(using inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = {
    class Impl(override val s: tt.type, override val t: tt.type) extends Sealing(s)(t)
    new Impl(tt, tt)
  }
}
