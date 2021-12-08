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

  private val erroneousPositions = mutable.Set.empty[Int]

  /**
   * Report an error, unless there is already an error reported at the same position.
   */
  def reportError(pos: Position, msg: String): Unit = {
    if (!erroneousPositions(pos.start)) {
      ctx.reporter.error(pos, msg)
      erroneousPositions += pos.start
    }
  }

  def hasErrors(): Boolean = erroneousPositions.nonEmpty

  class GhostAnnotationChecker extends Traverser {
    val ghostAnnotation = rootMirror.getRequiredClass("stainless.annotation.ghost")
    val ghostMethod = rootMirror.getPackage("stainless.lang").info.member(TermName("ghost"))

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
        field.symbol.hasAnnotation(ghostAnnotation)
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
        case vd @ ValDef(mods, _, _, ExCall(_, c, _, _)) if isDefaultGetter(c) && c.hasAnnotation(ghostAnnotation) =>
          sym.addAnnotation(ghostAnnotation)
        case _ => ()
      }
      else if (sym.isCaseCopy) {
        val caseClassParams = sym.owner.primaryConstructor.info.params
        for ((copyParam, caseParam) <- sym.info.params.zip(caseClassParams) if caseParam.hasAnnotation(ghostAnnotation))
          copyParam.addAnnotation(ghostAnnotation)
      }
      else if (sym.isDefaultGetter && isGhostDefaultGetter(m)) {
        sym.addAnnotation(ghostAnnotation)
      }
      else if (sym.isSetter && sym.hasAnnotation(ghostAnnotation)) {
        // make the setter parameter ghost but the setter itself stays non-ghost. this allows it
        // to be called from non-ghost code and at the same time allows assigning ghost state via the ghost argument
        sym.removeAnnotation(ghostAnnotation)
        sym.info.params.head.addAnnotation(ghostAnnotation)
      }
      else if (sym.isModuleOrModuleClass && sym.companionClass.hasAnnotation(ghostAnnotation)) {
        sym.addAnnotation(ghostAnnotation)
        sym.moduleClass.addAnnotation(ghostAnnotation)
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
        case Ident(_) if sym.hasAnnotation(ghostAnnotation) && !ghostContext =>
          reportError(tree.pos, s"Cannot access a ghost symbol outside of a ghost context. [ $tree in $currentOwner ]")

        case Select(qual, _) if sym.hasAnnotation(ghostAnnotation) && !ghostContext =>
          reportError(tree.pos, s"Cannot access a ghost symbol outside of a ghost context. [ $tree in $currentOwner ]")
          super.traverse(tree)

        case m: MemberDef  =>
          if (m.symbol.isSynthetic || m.symbol.isAccessor || m.symbol.isArtifact)
            propagateGhostAnnotation(m)

          // We consider some synthetic methods values as being inside ghost
          // but don't auto-annotate as such because we don't want all code to be removed.
          // They are synthetic case class methods that are harmless if they see some ghost nulls
          if (m.symbol.hasAnnotation(ghostAnnotation) || effectivelyGhost(sym))
            withinGhostContext(super.traverse(m))
          else
            super.traverse(m)

        case CaseDef(pat, guard, body) =>
          withinPatternContext(traverse(pat))
          traverse(guard)
          traverse(body)

        case f @ Apply(fun, args) if fun.symbol.hasAnnotation(ghostAnnotation) =>
          traverse(fun)
          withinGhostContext(traverseTrees(args))

        case Apply(fun, args) if patternContext =>
          traverse(fun)

          // pattern match variables need to get the ghost annotation from their case class argument
          for ((param, arg) <- fun.tpe.paramLists(symbolIndex(fun)).zip(args))
            if (param.hasAnnotation(ghostAnnotation)) {
              arg match {
                case b@Bind(_, body) =>
                  b.symbol.addAnnotation(ghostAnnotation)
                  traverse(body)
                case _ =>
                  traverse(arg)
              }
            } else
              traverse(arg)

        case f @ Apply(fun, args) =>
          traverse(fun)

          for ((param, arg) <- f.symbol.info.paramLists(symbolIndex(fun)).zip(args))
            if (param.hasAnnotation(ghostAnnotation))
              withinGhostContext(traverse(arg))
            else
              traverse(arg)

        case Assign(lhs, rhs) =>
          if (lhs.symbol.hasAnnotation(ghostAnnotation))
            withinGhostContext(traverse(rhs))
          else
            super.traverse(tree)

        case _ =>
          super.traverse(tree)
      }
    }
  }

  class Checker extends Traverser {
    val StainlessLangPackage = rootMirror.getPackage("stainless.lang")
    val ExternAnnotation = rootMirror.getRequiredClass("stainless.annotation.extern")
    val IgnoreAnnotation = rootMirror.getRequiredClass("stainless.annotation.ignore")
    val StainlessOld = StainlessLangPackage.info.decl(newTermName("old"))

    val BigInt_ApplyMethods =
      (StainlessLangPackage.info.decl(newTermName("BigInt")).info.decl(nme.apply).alternatives
      ++ rootMirror.getRequiredModule("scala.math.BigInt").info.decl(nme.apply).alternatives).toSet

    val RequireMethods =
      (definitions.PredefModule.info.decl(newTermName("require")).alternatives.toSet
        + rootMirror.getRequiredModule("stainless.lang.StaticChecks").info.decl(newTermName("require")))


    private val stainlessReplacement = mutable.Map(
      definitions.ListClass -> "stainless.collection.List",
      definitions.NilModule.moduleClass -> "stainless.collection.Nil",
      definitions.OptionClass -> "stainless.lang.Option",
      rootMirror.getRequiredClass("scala.util.Either") -> "stainless.lang.Either",
      definitions.ScalaPackageClass.info.decl(newTermName("Nil")) -> "stainless.collection.Nil",
      rootMirror.getRequiredClass("scala.collection.immutable.Map") -> "stainless.lang.Map",
      rootMirror.getRequiredClass("scala.collection.immutable.Set") -> "stainless.lang.Set"
    )

    // method println is overloaded, so we need to add all overloads to our map
    addOverloadsToMap(definitions.PredefModule.info.decl(newTermName("println")), "stainless.io.StdOut.println")

    private def addOverloadsToMap(sym: Symbol, replacement: String): Unit = {
      sym.alternatives.foreach(a => stainlessReplacement += a -> replacement)
    }

    private def checkType(pos: Position, tpe: Type): Unit = {
      val errors = for {
        tp <- tpe
        if stainlessReplacement.contains(tp.dealias.typeSymbol)
      } yield tp -> stainlessReplacement(tp.typeSymbol)

      for ((tp, replacement) <- errors.distinct) {
        reportError(pos, s"Scala API `$tp` is not directly supported, please use `$replacement` instead.")
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
        val isExtern = sym.hasAnnotation(ExternAnnotation)
        val isIgnore = sym.hasAnnotation(IgnoreAnnotation)

        // exit early if it's a subtree we shouldn't validate
        if (isExtern || isIgnore || sym.isSynthetic) {
          return ()
        }

        // ignore param accessors because they are duplicates of constructor parameters.
        // We catch them when we check constructors
        if ((sym.tpe ne null) && !sym.isParamAccessor) {
          checkType(tree.pos, sym.tpe)
        }
      } else {
        super.traverse(tree)
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

        case DefDef(_, _, _, _, _, rhs) if sym.isConstructor =>
          if (sym.info.paramss.flatten.exists(p => !sym.owner.info.member(p.name).isAccessor))
            reportError(tree.pos, "Non-field constructor parameters are not allowed in Stainless.")
          if (!sym.info.paramss.flatten.isEmpty && sym.owner.isAbstractClass)
            reportError(tree.pos, "Abstract class constructor parameters are not allowed in Stainless.")
          atOwner(sym)(traverse(rhs))

        case DefDef(_, _, _, _, _, rhs) =>
          // recurse only inside `rhs`, as parameter/type parameters have been checked already in `checkType`
          atOwner(sym)(traverse(rhs))

        case vd @ ValDef(mods, _, _, _) if sym.owner.isClass && !sym.owner.isAbstractClass && mods.isMutable && !mods.isCaseAccessor =>
          reportError(tree.pos, "Variables are only allowed within functions and as constructor parameters in Stainless.")

        case Apply(fun, List(arg)) if sym == StainlessOld =>
          arg match {
            case This(_) => ()
            case t if t.symbol != null && t.symbol.isVariable => ()
            case t =>
              reportError(t.pos, s"Stainless `old` is only defined on `this` and variables.")
          }

        case Apply(fun, args) if BigInt_ApplyMethods(sym) =>
          if (args.size != 1 || !args.head.isInstanceOf[Literal])
            reportError(args.head.pos, "Only literal arguments are allowed for BigInt.")

        case ExCall(Some(s @ Select(rec: Super, _)), _, _, _) =>
          if (s.symbol.isAbstract && !s.symbol.isConstructor)
            reportError(tree.pos, "Cannot issue a super call to an abstract method.")

        case Apply(fun, args) =>
          if (stainlessReplacement.contains(sym))
            reportError(tree.pos, s"Scala API ($sym) no longer extracted, please use ${stainlessReplacement(sym)}")

        case Template(parents, self, body) =>
          for (t <- body if !(t.isDef || t.isType || t.isEmpty || t.isInstanceOf[Import])) {
            // `require` is allowed inside classes, but not inside objects
            if (RequireMethods(t.symbol))
              if (currentOwner.isModuleClass)
                reportError(t.pos, "`require` is not allowed inside object bodies.")
              else ()
            else
              reportError(t.pos, "Only definitions are allowed inside class bodies.")
          }

          super.traverse(tree)

        case _ =>
          super.traverse(tree)
      }
    }
  }
}
