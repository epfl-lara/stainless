package stainless.frontends.scalac

import scala.collection.mutable
import scala.tools.nsc.SubComponent

/**
 * This class contains a traverser that rejects Scala programs that don't fit in the
 * PureScala or ImperativeScala fragments.
 *
 * Some interesting cases:
 *
 *  - pattern match variables are fresh variables that have to "inherit" the @ghost annotation
 *    from the corresponding case class field
 *  - case classes generate a large number of synthetic methods that need to be patched with @ghost
 *    in cases where there are @ghost parameters
 *  - some case class synthetics will contain invalid accesses to ghost code (i.e. methods equals and unapply)
 *    but we don't report the errors in synthetic code. This is harmless and the ghost code will be
 *    removed as usual
 *
 * This class mutates some symbols by adding the @ghost annotation (see cases above). The AST is not changed.
 */
trait FragmentChecker extends SubComponent { self: StainlessExtraction =>
  import global._

  import ExpressionExtractors.ExCall
  import StructuralExtractors.ExObjectDef

  private val errors = mutable.Set.empty[(Int, Int, String)]

  /**
   * Report an error, unless there is already an error with the same message reported in an enclosing position.
   */
  private def reportError(pos: Position, msg: String): Unit = {
    if (!errorsEnclosing(pos.start, pos.end)(msg)) {
      ctx.reporter.error(pos, msg)
      errors += ((pos.start, pos.end, msg))
    }
  }

  private def errorsEnclosing(start: Int, end: Int): Set[String] = {
    errors.flatMap { case (s, e, msg) =>
      if (s <= start && end <= e) Some(msg)
      else None
    }.toSet
  }

  def hasErrors(): Boolean = errors.nonEmpty

  // Note: we wrap Symbols into an Option to emphasize the fact that the symbol may not exist
  // and that care must be taken in case it does not.
  private def getClassIfDefinedOrNone(cls: String): Option[ClassSymbol] = {
    val sym = rootMirror.getClassIfDefined(cls)
    if (sym.exists) Some(sym.asClass) else None
  }

  private def getModuleIfDefinedOrNone(mod: String): Option[ModuleSymbol] = {
    val sym = rootMirror.getModuleIfDefined(mod)
    if (sym.exists) Some(sym.asModule) else None
  }

  private def getModuleClassIfDefinedOrNone(cls: String): Option[Symbol] =
    getModuleIfDefinedOrNone(cls).map(_.moduleClass)

  private def getPackageIfDefinedOrNone(pkg: String): Option[ModuleSymbol] = {
    val sym = rootMirror.getPackageIfDefined(pkg)
    if (sym.exists) Some(sym.asModule) else None
  }

  class GhostAnnotationChecker extends Traverser {
    private val ghostAnnotation = getClassIfDefinedOrNone("stainless.annotation.ghost")

    private var ghostContext: Boolean = false

    def withinGhostContext[A](body: => A): A = {
      val old = ghostContext
      ghostContext = true
      val res = body
      ghostContext = old
      res
    }

    var patternContext: Boolean = false

    def withinPatternContext[A](body: => A): A = {
      val old = patternContext
      patternContext = true
      val res = body
      patternContext = old
      res
    }

    private def isGhostDefaultGetter(m: Tree): Boolean = m match {
      case DefDef(mods, name, tparams, vparamss, tpt, field @ Select(This(_), f)) =>
        field.symbol.hasGhostAnnotation
      case _ => false
    }

    /**
     * Synthetics introduced by typer for case classes won't propagate the @ghost annotation
     * to the copy method or for default arguments, leading to invalid accesses from non-ghost
     * code to ghost code. We fix it here by adding @ghost to these synthetics
     */
    private def propagateGhostAnnotation(m: MemberDef): Unit = {
      val sym = m.symbol

      if (sym.isArtifact) m match {
        case vd @ ValDef(mods, _, _, ExCall(_, c, _, _)) if isDefaultGetter(c) && c.hasGhostAnnotation =>
          sym.addGhostAnnotation()
        case _ => ()
      }
      else if (sym.isCaseCopy) {
        val caseClassParams = sym.owner.primaryConstructor.info.params
        for ((copyParam, caseParam) <- sym.info.params.zip(caseClassParams) if caseParam.hasGhostAnnotation)
          copyParam.addGhostAnnotation()
      }
      else if (sym.isDefaultGetter && isGhostDefaultGetter(m)) {
        sym.addGhostAnnotation()
      }
      else if (sym.isSetter && sym.hasGhostAnnotation) {
        // make the setter parameter ghost but the setter itself stays non-ghost. this allows it
        // to be called from non-ghost code and at the same time allows assigning ghost state via the ghost argument
        sym.removeGhostAnnotation()
        sym.info.params.head.addGhostAnnotation()
      }
      else if (sym.isModuleOrModuleClass && sym.companionClass.hasGhostAnnotation) {
        sym.addGhostAnnotation()
        sym.moduleClass.addGhostAnnotation()
      }
    }

    /**
     * Methods that should be considered as part of a ghost context, even though they are not
     * explicitly ghost. They are typically synthetic methods for case classes that are harmless
     * if they touch ghost code
     */
    private def effectivelyGhost(sym: Symbol): Boolean = {
      sym.isSynthetic &&
      (
        (
          sym.owner.isCaseClass &&
          (
            sym.name == nme.equals_ ||
            sym.name == nme.productElement ||
            sym.name == nme.hashCode_
          )
        ) ||
        (
          sym.owner.companionClass.isCaseClass &&
          sym.name == nme.unapply
        )
      )
    }

    private def symbolIndex(tree: Tree): Int = tree match {
      case Apply(fun, args) => symbolIndex(fun) + 1
      case _ => 0
    }

    override def traverse(tree: Tree): Unit = {
      val sym = tree.symbol
      tree match {
        case Ident(_) if sym.hasGhostAnnotation && !ghostContext =>
          reportError(tree.pos, s"Cannot access a ghost symbol outside of a ghost context. [ $tree in $currentOwner ]")

        case Select(qual, _) if sym.hasGhostAnnotation && !ghostContext =>
          reportError(tree.pos, s"Cannot access a ghost symbol outside of a ghost context. [ $tree in $currentOwner ]")
          super.traverse(tree)

        case m: MemberDef  =>
          if (m.symbol.isSynthetic || m.symbol.isAccessor || m.symbol.isArtifact)
            propagateGhostAnnotation(m)

          // We consider some synthetic methods values as being inside ghost
          // but don't auto-annotate as such because we don't want all code to be removed.
          // They are synthetic case class methods that are harmless if they see some ghost nulls
          if (m.symbol.hasGhostAnnotation || effectivelyGhost(sym))
            withinGhostContext(super.traverse(m))
          else
            super.traverse(m)

        case CaseDef(pat, guard, body) =>
          withinPatternContext(traverse(pat))
          traverse(guard)
          traverse(body)

        case f @ Apply(fun, args) if fun.symbol.hasGhostAnnotation =>
          traverse(fun)
          withinGhostContext(traverseTrees(args))

        case Apply(fun, args) if patternContext =>
          traverse(fun)

          // pattern match variables need to get the ghost annotation from their case class argument
          for ((param, arg) <- fun.tpe.paramLists(symbolIndex(fun)).zip(args))
            if (param.hasGhostAnnotation) {
              arg match {
                case b@Bind(_, body) =>
                  b.symbol.addGhostAnnotation()
                  traverse(body)
                case _ =>
                  traverse(arg)
              }
            } else
              traverse(arg)

        case f @ Apply(fun, args) =>
          traverse(fun)

          for ((param, arg) <- f.symbol.info.paramLists(symbolIndex(fun)).zip(args))
            if (param.hasGhostAnnotation)
              withinGhostContext(traverse(arg))
            else
              traverse(arg)

        case Assign(lhs, rhs) =>
          if (lhs.symbol.hasGhostAnnotation)
            withinGhostContext(traverse(rhs))
          else
            super.traverse(tree)

        case _ =>
          super.traverse(tree)
      }
    }

    extension (sym: Symbol) {
      private def hasGhostAnnotation: Boolean = ghostAnnotation.exists(sym.hasAnnotation)
      private def addGhostAnnotation(): Unit = ghostAnnotation.foreach(sym.addAnnotation)
      private def removeGhostAnnotation(): Unit = ghostAnnotation.foreach(sym.removeAnnotation)
    }
  }

  class Checker extends Traverser {
    private val ScalaEnsuringMethod = rootMirror.getRequiredModule("scala.Predef").info.decl(newTermName("Ensuring"))
      .alternatives.filter(_.isMethod).head

    private val StainlessLangPackage = getPackageIfDefinedOrNone("stainless.lang")
    private val ExternAnnotation = getClassIfDefinedOrNone("stainless.annotation.extern")
    private val IgnoreAnnotation = getClassIfDefinedOrNone("stainless.annotation.ignore")
    private val StainlessOld = StainlessLangPackage.map(_.info.decl(newTermName("old")))
    private val StainlessBVObject = getModuleIfDefinedOrNone("stainless.math.BitVectors")
    private val StainlessBVClass = getClassIfDefinedOrNone("stainless.math.BitVectors.BV")
    private val StainlessBVArrayIndex = getClassIfDefinedOrNone("stainless.math.BitVectors.ArrayIndexing").map(_.companionClass)
    private val BigInt_ApplyMethods =
      (StainlessLangPackage.map(_.info.decl(newTermName("BigInt")).info.decl(nme.apply).alternatives).getOrElse(Nil)
      ++ rootMirror.getRequiredModule("scala.math.BigInt").info.decl(nme.apply).alternatives).toSet

    private val RequireMethods =
      definitions.PredefModule.info.decl(newTermName("require")).alternatives.toSet
        ++ getModuleIfDefinedOrNone("stainless.lang.StaticChecks").map(_.info.decl(newTermName("require")).alternatives.toSet).getOrElse(Set.empty)

    private val stainlessReplacement = mutable.Map(
      definitions.ListClass -> "stainless.collection.List",
      definitions.NilModule.moduleClass -> "stainless.collection.Nil",
      definitions.OptionClass -> "stainless.lang.Option",
      rootMirror.getRequiredClass("scala.util.Either") -> "stainless.lang.Either",
      definitions.ScalaPackageClass.info.decl(newTermName("Nil")) -> "stainless.collection.Nil",
      rootMirror.getRequiredClass("scala.collection.Map") -> "stainless.lang.Map",
      rootMirror.getRequiredClass("scala.collection.immutable.Map") -> "stainless.lang.Map",
      rootMirror.getRequiredClass("scala.collection.Set") -> "stainless.lang.Set",
      rootMirror.getRequiredClass("scala.collection.immutable.Set") -> "stainless.lang.Set",
    )

    // We do not in general support the types for these methods, but we do extract them.
    // We therefore skip the typing check for them.
    private val bvSpecialFunctions =
      StainlessBVObject.map(bvObj => Set(
        bvObj.info.decl(newTermName("min")),
        bvObj.info.decl(newTermName("max"))
      )).getOrElse(Set.empty) ++
      StainlessBVArrayIndex.map(bvArray => Set(bvArray.info.decl(nme.apply))).getOrElse(Set.empty) ++
      StainlessBVClass.map(bvClass => Set(
        bvClass.info.decl(newTermName("widen")),
        bvClass.info.decl(newTermName("narrow")),
        bvClass.info.decl(newTermName("toSigned")),
        bvClass.info.decl(newTermName("toUnsigned")),
      )).getOrElse(Set.empty)

    private val objectMethods = Set[Symbol](
      definitions.Object_eq, definitions.Object_ne, definitions.Object_synchronized, definitions.Object_clone,
      definitions.Object_finalize, definitions.Object_notify, definitions.Object_notifyAll, definitions.Object_getClass
    )

    // Types that may show up due to inference that will later cause a missing dependency error
    // should we not report an error before.
    private val unsupportedTypes: Set[Symbol] = Set(
      definitions.SerializableClass,
      definitions.ProductRootClass,
    )

    // method println is overloaded, so we need to add all overloads to our map
    addOverloadsToMap(definitions.PredefModule.info.decl(newTermName("println")), "stainless.io.StdOut.println")

    private def addOverloadsToMap(sym: Symbol, replacement: String): Unit = {
      sym.alternatives.foreach(a => stainlessReplacement += a -> replacement)
    }

    private def checkType(tree: Tree, tpe0: Type): Unit = {
      object Errors {
        def empty: Errors = Errors(Set.empty, Set.empty)
      }
      case class Errors(libRepls: Set[(Symbol, String)], unsupported: Set[Type]) {
        def addReplacement(ts: (Symbol, String)): Errors = copy(libRepls = libRepls + ts)
        def addUnsupported(t: Type): Errors = copy(unsupported = unsupported + t)
      }
      var errs = Errors.empty
      def strip(tpe: Type): Type = {
        // The extraction frontend filters out type that are unsupported before extracting them,
        // so we do here the same to avoid having false positive.
        tpe.map {
          case tpe@RefinedType(parents, defs) if defs.isEmpty =>
            val filtered = parents.filterNot(isIgnored)
            if (filtered.size == 1) filtered.head
            else tpe
          case tpe => tpe
        }
      }
      val tpe = strip(tpe0)
      for (tp <- tpe) {
        val tpSym = tp.typeSymbol
        if (stainlessReplacement.contains(tpSym))
          errs = errs.addReplacement(tpSym -> stainlessReplacement(tpSym))
        else tp match {
          case _: ExistentialType => errs = errs.addUnsupported(tp)
          case _ => ()
        }
      }

      for ((sym, replacement) <- errs.libRepls) {
        reportError(tree.pos, s"Scala API `${sym.name}` is not directly supported, please use `$replacement` instead.")
      }

      def contains(hay: Type, needle: Type): Boolean = {
        var found = false
        hay.foreach { tp => if (tp eq needle) found = true }
        found
      }

      def sourceOfType(tree: Tree, tp: Type): Unit = {
        tree match {
          case dd: DefDef =>
            // It seems to be impossible to know whether a type was inferred or ascribed
            val ddTpe = strip(dd.tpt.tpe)
            if (existentialsInType(ddTpe).nonEmpty) {
              reportError(dd.tpt.pos, s"Hint: the return type of ${dd.name} is `$ddTpe`")
              sourceOfType(dd.rhs, tp)
            }
          case bl: Block => sourceOfType(bl.expr, tp)
          case vd: ValDef =>
            val vdTpe = strip(repackExistential(vd.tpt.tpe))
            if (existentialsInType(vdTpe).nonEmpty) {
              reportError(vd.tpt.pos, s"Hint: the type of ${vd.name} is `$vdTpe`")
              sourceOfType(vd.rhs, tp)
            }
          case ite: If =>
            def branches(ite: If): Seq[Tree] = {
              Seq(ite.thenp) ++ (ite.elsep match {
                case ite2: If => branches(ite2)
                case t => Seq(t)
              })
            }
            val iteTp = strip(repackExistential(ite.tpe))
            val iteTpWiden = iteTp.widen
            if (existentialsInType(iteTpWiden).nonEmpty) {
              reportError(ite.pos, s"Hint: the widened type of this if expression is `$iteTpWiden`")
              val brchs = branches(ite)
              for (branch <- brchs) {
                reportError(branch.pos, s"Hint: this branch type is `${branch.tpe}`")
              }
            }
          case mtch: Match =>
            val mtchTp = strip(repackExistential(mtch.tpe))
            val mtchTpWiden = mtchTp.widen
            if (existentialsInType(mtchTpWiden).nonEmpty) {
              reportError(mtch.pos, s"Hint: the widened type of this match expression is `$mtchTpWiden`")
              for (branch <- mtch.cases) {
                reportError(branch.pos, s"Hint: this case type is `${branch.tpe}`")
              }
            }
          case _ => ()
        }
      }

      for (tp <- errs.unsupported) {
        reportError(tree.pos, s"Type `$tp` is unsupported")
        sourceOfType(tree, tp)
      }
    }

    private var classBody = false
    def inClassBody[T](f: => T): T = {
      val old = classBody
      classBody = true
      val res = f
      classBody = old
      res
    }

    override def traverse(tree: Tree): Unit = {
      val sym = tree.symbol
      if (sym ne null) {
        // exit early if it's a subtree we shouldn't validate
        if (skipTraversal(sym)) {
          return
        }
        // Ignore class constructors because they duplicate param accessors (fields) which we already check
        // or skip if they are annotated with @extern.
        // We do not check the *type* for unapply call since these refer to Scala Option API
        // These can be extracted anyway (note that we still validate the sub-trees)
        if ((sym.tpe ne null) && !sym.isClassConstructor && sym.name != nme.unapply) {
          checkType(tree, sym.tpe)
        }
      }

      tree match {
        case od @ ExObjectDef(_, tmpl) =>
          if (tmpl.parents.exists(p => !isIgnored(p.tpe))) {
            reportError(tree.pos, "Objects cannot extend classes or implement traits, use a case object instead")
          }
          super.traverse(od)

        case ClassDef(mods, name, tparams, impl) =>
          val isSupported = {
            sym.isAbstractClass ||
            sym.isCaseClass ||
            sym.isModuleClass ||
            sym.isAnonymousClass ||
            sym.isImplicit ||
            sym.isNonBottomSubClass(definitions.AnnotationClass)
          }

          if (!isSupported) {
            reportError(tree.pos, "Only abstract classes, case classes, anonymous classes, and objects are allowed in Stainless.")
          }

          val parents = impl.parents.map(_.tpe).filterNot(isIgnored)
          if (parents.length > 1) {
            reportError(tree.pos, s"Stainless supports only simple type hierarchies: Classes can only inherit from a single class/trait")
          }

          impl foreach {
            case cd: ClassDef if !cd.symbol.owner.isMethod =>
              reportError(cd.pos, "Classes can only be defined at the top-level, within objects, or within methods")

            case _ => ()
          }

          atOwner(sym)(traverse(impl))

        case DefDef(_, _, _, _, _, rhs) if sym.isClassConstructor =>
          if (sym.isAuxiliaryConstructor)
            reportError(tree.pos, "Auxiliary constructors are not allowed in Stainless.")
          if (!sym.info.paramss.flatten.isEmpty && sym.owner.isAbstractClass)
            reportError(tree.pos, "Abstract class constructor parameters are not allowed in Stainless.")
          atOwner(sym)(traverse(rhs))

        case DefDef(_, _, _, _, _, rhs) =>
          // recurse only inside `rhs`, as parameter/type parameters have been checked already in `checkType`
          atOwner(sym)(traverse(rhs))

        case vd @ ValDef(mods, _, _, _) if sym.owner.isClass && !sym.owner.isAbstractClass && mods.isMutable && !mods.isCaseAccessor =>
          reportError(tree.pos, "Variables are only allowed within functions and as constructor parameters in Stainless.")

        case Apply(fun, List(arg)) if StainlessOld.contains(sym) =>
          arg match {
            case This(_) => ()
            case t if t.symbol != null && t.symbol.isVariable => ()
            case t =>
              reportError(t.pos, s"Stainless `old` is only defined on `this` and variables.")
          }
          super.traverse(tree)

        case Apply(fun, args) if BigInt_ApplyMethods(sym) =>
          if (args.size != 1 || !args.head.isInstanceOf[Literal])
            reportError(args.head.pos, "Only literal arguments are allowed for BigInt.")
          super.traverse(tree)

        case ExCall(Some(s @ Select(rec: Super, _)), _, _, _) =>
          if (s.symbol.isAbstract && !s.symbol.isConstructor)
            reportError(tree.pos, "Cannot issue a super call to an abstract method.")
          super.traverse(tree)

        case Throw(ex) =>
          reportError(tree.pos, "throw expressions are unsupported in Stainless")
          super.traverse(tree)

        case Apply(fun, args) =>
          if (stainlessReplacement.contains(sym))
            reportError(tree.pos, s"Scala API ($sym) no longer extracted, please use ${stainlessReplacement(sym)}")
          if (objectMethods(sym))
            reportError(tree.pos, s"Method ${sym.name} on Object is not supported")
          super.traverse(tree)

        case Try(_, cases, finalizer) =>
          if (cases.isEmpty && finalizer.isEmpty) reportError(tree.pos, "try expressions are not supported in Stainless")
          else if (cases.isEmpty && !finalizer.isEmpty) reportError(tree.pos, "try-finally expressions are not supported in Stainless")
          else if (finalizer.isEmpty) reportError(tree.pos, "try-catch expressions are not supported in Stainless")
          else reportError(tree.pos, "try-catch-finally expressions are not supported in Stainless")
          super.traverse(tree)

        case Template(_, self, body) =>
          for (t <- body if !(t.isDef || t.isType || t.isEmpty || t.isInstanceOf[Import])) {
            // `require` is allowed inside classes, but not inside objects
            if (RequireMethods(t.symbol))
              if (currentOwner.isModuleClass)
                reportError(t.pos, "`require` is not allowed inside object bodies.")
              else ()
            else
              reportError(t.pos, "Only definitions are allowed inside class bodies.")
          }
          // We do not visit parents, as they will contain reference to synthetic classes such as Product, Serializable, etc.
          atOwner(sym) {
            traverse(self)
            traverseTrees(body)
          }

        case _ =>
          super.traverse(tree)
      }
    }

    private def skipTraversal(sym: Symbol): Boolean = {
      val isExtern = ExternAnnotation.exists(sym.hasAnnotation)
      val isIgnore = IgnoreAnnotation.exists(sym.hasAnnotation)
      // * If it's a synthetic symbol, we will still visit if it is either:
      //    -the scala Ensuring method (that creates the Ensuring class), which for some reasons is synthetic (though StaticChecks.Ensuring is not for instance)
      //    -an anonymous function
      //    -an anonymous class
      // * We furthermore ignore ClassTag[T].apply() that appear for Array operations, which we can still extract.
      isExtern || isIgnore || (sym.isSynthetic && (sym ne ScalaEnsuringMethod) && !sym.isAnonymousFunction && !sym.isAnonymousFunction) ||
        (sym.owner eq definitions.ClassTagModule.moduleClass) ||
        bvSpecialFunctions(sym) || StainlessBVClass.contains(sym)
    }
  }
}
