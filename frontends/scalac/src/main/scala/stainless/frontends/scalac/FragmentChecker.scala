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


  class Checker extends Traverser {
    val ExternAnnotation = rootMirror.getRequiredClass("stainless.annotation.extern")
    val IgnoreAnnotation = rootMirror.getRequiredClass("stainless.annotation.ignore")

    private val stainlessType: Map[Symbol, String] = Map(
      definitions.ListClass -> "stainless.lang.collection.List",
      definitions.NilModule -> "stainless.lang.collection.Nil",
      definitions.ScalaPackageClass.info.decl(newTermName("Nil")) -> "stainless.lang.collection.Nil",
      rootMirror.getRequiredClass("scala.collection.immutable.Map") -> "stainless.lang.Map",
      rootMirror.getRequiredClass("scala.collection.immutable.Set") -> "stainless.lang.Set"
    )

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
        if stainlessType.contains(tp.dealias.typeSymbol)
      } yield tp -> stainlessType(tp.typeSymbol)

      for ((tp, replacement) <- errors.distinct)
        reportError(pos, s"Scala collection API ($tp) no longer extracted, please use ${replacement}")
    }

    def checkVariance(tdef: TypeDef): Unit = {
      if (tdef.symbol.asType.isCovariant || tdef.symbol.asType.isContravariant)
        reportError(tdef.pos, "Stainless supports only invariant type parameters")
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
            if (tparams.size != parentTParams.size)
              reportError(tree.pos,
                s"Stainless supports only simple type hierarchies: Class should define the same type parameters as its super class ${firstParent.typeSymbol.tpe}")
          }
          tparams.foreach(checkVariance)
          traverse(impl)

        case DefDef(_, _, _, _, _, rhs) if sym.isConstructor =>
          if (!sym.info.paramss.flatten.isEmpty && sym.owner.isAbstractClass)
            reportError(tree.pos, "Constructor parameters are not allowed in Stainless.")
          atOwner(sym)(traverse(rhs))

        case DefDef(_, _, _, _, _, rhs) =>
          // recurse only inside `rhs`, as parameter/type parameters have been check already in `checkType`
          atOwner(sym)(traverse(rhs))

//        case ValDef(_, _, _, rhs) if sym.owner.isAbstractClass && !sym.isParamAccessor => // param accessors are fields issued from constructors
//          if (!(sym.isLazy || sym.hasAnnotation(definitions.ScalaInlineClass)))
//            reportError(tree.pos, s"Fields are not allowed in abstract classes.")
//          atOwner(sym)(traverse(rhs))
//
//        case ValDef(_, _, _, rhs) =>
//          // recurse only inside `rhs`, as parameter/type parameters have been check already in `checkType`
//          atOwner(sym)(traverse(rhs))

        case Super(_, _) if !currentOwner.isConstructor => // we need to allow super in constructors
          reportError(tree.pos, "Super calls are not allowed in Stainless.")

        case _ =>
          super.traverse(tree)
      }
    }
  }
}
