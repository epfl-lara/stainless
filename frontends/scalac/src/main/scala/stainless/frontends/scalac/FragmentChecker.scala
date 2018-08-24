package stainless.frontends.scalac

import scala.collection.mutable
import scala.tools.nsc.SubComponent

/**
 * This class contains a traverser that rejects Scala programs that don't fit in the
 * PureScala or ImperativeScala fragments.
 */
trait FragmentChecker extends SubComponent { _: StainlessExtraction =>
  import global._

  // defined by StainlessExtraction
  val ctx: inox.Context

  import StructuralExtractors.ExObjectDef

  class Checker extends Traverser {
    val StainlessLangPackage = rootMirror.getPackage(newTermName("stainless.lang"))
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
      definitions.ListClass -> "stainless.lang.collection.List",
      definitions.NilModule.moduleClass -> "stainless.lang.collection.Nil",
      definitions.OptionClass -> "stainless.lang.Option",
      rootMirror.getRequiredClass("scala.util.Either") -> "stainless.lang.Either",
      definitions.ScalaPackageClass.info.decl(newTermName("Nil")) -> "stainless.lang.collection.Nil",
      rootMirror.getRequiredClass("scala.collection.immutable.Map") -> "stainless.lang.Map",
      rootMirror.getRequiredClass("scala.collection.immutable.Set") -> "stainless.lang.Set"
    )

    // method println is overloaded, so we need to add all overloads to our map
    addOverloadsToMap(definitions.PredefModule.info.decl(newTermName("println")), "stainless.StdOut.println")

    private def addOverloadsToMap(sym: Symbol, replacement: String): Unit = {
      sym.alternatives.foreach(a => stainlessReplacement += a -> replacement)
    }

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

    private def checkType(pos: Position, tpe: Type): Unit = {
      val errors = for {
        tp <- tpe
        if stainlessReplacement.contains(tp.dealias.typeSymbol)
      } yield tp -> stainlessReplacement(tp.typeSymbol)

      for ((tp, replacement) <- errors.distinct)
        reportError(pos, s"Scala API ($tp) no longer extracted, please use ${replacement}")
    }

    def checkVariance(tdef: TypeDef): Unit = {
      // if (tdef.symbol.asType.isCovariant || tdef.symbol.asType.isContravariant)
      //   reportError(tdef.pos, "Stainless supports only invariant type parameters")
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
        if (isExtern || isIgnore || sym.isSynthetic)
          return

        // ignore param accessors because they are duplicates of constructor parameters.
        // We catch them when we check constructors
        if ((sym.tpe ne null) && !sym.isParamAccessor)
          checkType(tree.pos, sym.tpe)
      } else super.traverse(tree)

      tree match {
        case od @ ExObjectDef(_, tmpl) =>
          if (tmpl.parents.exists(p => !ignoreClasses.contains(p.tpe))) {
            reportError(tree.pos, "Objects cannot extend classes or implement traits, use a case object instead")
          }
          super.traverse(od)

        case ClassDef(mods, name, tparams, impl) =>
          if (!sym.isAbstractClass
            && !sym.isCaseClass
            && !sym.isModuleClass
            && !sym.isImplicit
            && !sym.isNonBottomSubClass(definitions.AnnotationClass))
            reportError(tree.pos, "Only abstract classes, case classes and objects are allowed in Stainless.")

          val firstParent = sym.info.firstParent
          if (firstParent != definitions.AnyRefTpe) {
            // we assume type-checked Scala code, so even though usually type arguments are not the same as
            // type parameters, we can assume the super type is fully applied (otherwise we could check via
            // firstParent.typeSymbol.typeParams)
            val parentTParams = firstParent.typeArgs
            val tparams = sym.info.typeParams
            // if (tparams.size != parentTParams.size)
            //   reportError(tree.pos,
            //     s"Stainless supports only simple type hierarchies: Class should define the same type parameters as its super class ${firstParent.typeSymbol.tpe}")
          }
          tparams.foreach(checkVariance)
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

        case vd @ ValDef(mods, _, _, _) if sym.owner.isClass && mods.isMutable && !mods.isCaseAccessor =>
          reportError(tree.pos, "Vars are not allowed in class bodies in Stainless.")

        case t: TypeDef =>
          if (!t.symbol.isAliasType)
            reportError(t.pos, "Stainless doesn't support abstract type members")
          atOwner(sym)(traverse(t.rhs))

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

        case Apply(fun, args) =>
          if (stainlessReplacement.contains(sym))
            reportError(tree.pos, s"Scala API ($sym) no longer extracted, please use ${stainlessReplacement(sym)}")

        case Super(_, _) if !currentOwner.isConstructor => // we need to allow super in constructors
          reportError(tree.pos, "Super calls are not allowed in Stainless.")

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
