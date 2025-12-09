package stainless
package frontends.dotc

import dotty.tools.dotc._
import core._
import Symbols._
import Contexts.{Context => DottyContext}
import ast.Trees
import Types._
import Trees._
import ast.tpd
import Flags._
import Annotations._
import Denotations._
import StdNames._
import Names._
import util.SourcePosition

import scala.collection.mutable

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
class FragmentChecker(inoxCtx: inox.Context)(using override val dottyCtx: DottyContext) extends ASTExtractors {

  import ExpressionExtractors._
  import StructuralExtractors._

  private val errors = mutable.Set.empty[(Int, Int, String)]

  /**
   * Report an error, unless there is already an error with the same message reported in an enclosing position.
   */
  private def reportError(pos: SourcePosition, msg: String): Unit = {
    if (!errorsEnclosing(pos.start, pos.end)(msg)) {
      inoxCtx.reporter.error(pos, msg)
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

  def ghostPropagater(tree: tpd.Tree): Unit = (new GhostManagement.GhostAnnotationPropagater)((), tree)
  def ghostChecker(tree: tpd.Tree): Unit = (new GhostManagement.GhostAnnotationChecker)((), tree)

  def checker(tree: tpd.Tree): Unit = (new Checker)((), tree)

  private def ctorFieldsOf(clsInfo: ClassInfo): List[Symbol] = {
    // Note: we do filter over clsInfo.fields (defined in Types) because the order of the fields is not kept.
    // Instead, we employ decls because the order is preserved
    clsInfo.decls.iterator.filter(s => !(s `is` Method) && ((s `is` ParamAccessor) || (s `is` CaseAccessor))).toList
  }

  // Note: we wrap Symbols into an Option to emphasize the fact that the symbol may not exist
  // and that care must be taken in case it does not.
  private def getClassIfDefinedOrNone(cls: String)(using DottyContext): Option[ClassSymbol] = {
    val sym = getClassIfDefined(cls)
    if (sym.exists) Some(sym.asClass) else None
  }

  private def getModuleIfDefinedOrNone(mod: String)(using DottyContext): Option[Symbol] = {
    val sym = getModuleIfDefined(mod)
    if (sym.exists) Some(sym) else None
  }

  private def getModuleClassIfDefinedOrNone(cls: String)(using DottyContext): Option[Symbol] =
    getModuleIfDefinedOrNone(cls).map(_.moduleClass)

  private def getPackageIfDefinedOrNone(pkg: String)(using DottyContext): Option[Symbol] = {
    val name = termName(pkg)
    val ref = staticRef(name, generateStubs = false, isPackage = true)
    if (ref.exists) Some(ref.requiredSymbol("package", name)(_.is(Package)).asTerm)
    else None
  }

    object GhostManagement {
      private val ghostAnnotation = getClassIfDefinedOrNone("stainless.annotation.ghost")
      extension (sym: Symbol) {
        private def hasGhostAnnotation(using DottyContext): Boolean = ghostAnnotation.exists(ghostClassSymbol => sym.hasAnnotation(ghostClassSymbol))
        private def addGhostAnnotation()(using DottyContext): Unit = ghostAnnotation.foreach(ghostClassSymbol => sym.addAnnotation(ghostClassSymbol))
        private def removeGhostAnnotation()(using DottyContext): Unit = ghostAnnotation.foreach(ghostClassSymbol => sym.removeAnnotation(ghostClassSymbol))
      }
      /**
        * Tree traverser that propagates ghost annotations on synthesized members:
          - copy and apply methods: propagates ghost parameter annotations
          - unapply methods application
          - setters

        * see inline comments for more information.
        * 
        * This has to run as a separate tree traversal to avoid cases where an application of a function is 
        * checked for ghost validity before the annotations had been propagated. 
        * See https://github.com/epfl-lara/stainless/issues/1670
        */
      class GhostAnnotationPropagater extends tpd.TreeTraverser {
        def isCaseCopy(s: Symbol): Boolean = {
          (s `is` Method) && (s.owner `is` Case) && (s `is` Synthetic) && s.name == nme.copy
        }

        def isCaseApply(s: Symbol): Boolean = {
          // The apply method is to be found in the module class, so we need to check that its owner is indeed a ModuleClass
          (s `is` Method) && (s.owner `is` ModuleClass) && (s `is` Synthetic) && s.name == nme.apply && s.owner.companionClass.exists
        }

        /**
         * Synthetics introduced by typer for case classes won't propagate the @ghost annotation
         * to the copy method or for default arguments, leading to invalid accesses from non-ghost
         * code to ghost code. We fix it here by adding @ghost to these synthetics
         */
        private def propagateGhostAnnotation(m: tpd.MemberDef): Unit = {
          val sym = m.symbol
          lazy val isCopy = isCaseCopy(sym)
          lazy val isApply = isCaseApply(sym)


          if (isCopy || isApply) {
            val ownerSymbol = 
              if (isCopy) sym.owner
              // The apply method is in the module class; we get the actual case class using companionClass
              else sym.owner.companionClass
            val clsInfo = ownerSymbol.denot.asClass.classInfo
              
            val ctorFields = ctorFieldsOf(clsInfo)
            val params = m.asInstanceOf[tpd.DefDef].termParamss.flatten.map(_.symbol)
            for ((ctorField, param) <- ctorFields.zip(params) if ctorField.hasGhostAnnotation)
              param.addGhostAnnotation()
              
            // We also propagate the ghost annotation on the class to apply method
            if isApply && ownerSymbol.hasGhostAnnotation then
              sym.addGhostAnnotation()
          } else if (sym.isSetter && sym.hasGhostAnnotation) {
            // make the setter parameter ghost but the setter itself stays non-ghost. this allows it
            // to be called from non-ghost code and at the same time allows assigning ghost state via the ghost argument
            sym.removeGhostAnnotation()
            val param = m.asInstanceOf[tpd.DefDef].termParamss.flatten.head
            param.symbol.addGhostAnnotation()
          } else if (((sym `is` Module) || (sym `is` ModuleClass)) && sym.companionClass.hasGhostAnnotation) {
            sym.addGhostAnnotation()
            sym.moduleClass.addGhostAnnotation()
          }
        }

        override def traverse(tree: tpd.Tree)(using ctx: DottyContext): Unit = {
          val sym = tree.symbol
          tree match {
            case m: tpd.MemberDef  =>
              if ((m.symbol `is` Synthetic) || (m.symbol `is` Accessor) || (m.symbol `is` Artifact))
                propagateGhostAnnotation(m)
              traverseChildren(m)

            case UnApply(fun, _, args) if fun.symbol.name == nme.unapply && (fun.symbol `is` Synthetic) =>
              traverse(fun)

              // The pattern match variables need to add the ghost annotation from their case class ctor fields
              // We only do that for case classes synthesized unapply methods.

              val caseClassInfo = fun.symbol.denot.owner // The owner of the unapply method is the companion object
                .denot.companionClass.asClass // We need the class itself to get the case class ctor fields
                .classInfo
              val ctorFields = ctorFieldsOf(caseClassInfo)
              for ((param, arg) <- ctorFields.zip(args))
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

            case _ =>
              traverseChildren(tree)
          }
        }
      }

      class GhostAnnotationChecker extends tpd.TreeTraverser {
        private var ghostContext: Boolean = false

        def withinGhostContext[A](body: => A): A = {
          val old = ghostContext
          ghostContext = true
          val res = body
          ghostContext = old
          res
        }

        // Note: we not have a isGhostDefaultGetter because Dotty does not generate getters for fields

        /**
         * Methods that should be considered as part of a ghost context, even though they are not
         * explicitly ghost. They are typically synthetic methods for case classes that are harmless
         * if they touch ghost code
         */
        private def effectivelyGhost(sym: Symbol): Boolean = {
          // copy$default$n are synthetic methods that simply return the n-th (starting from 1) constructor field
          def isCopyDefault = sym.name match {
            case DerivedName(nme.copy, kind) =>
              sym.name `is` NameKinds.DefaultGetterName
            case _ => false
          }
          def isProductAccessor = sym.name match {
            case nme._1 | nme._2 | nme._3 | nme._4 | nme._5 | nme._6 | nme._7 | nme._8 | nme._9 | nme._10 |
                nme._11 | nme._12 | nme._13 | nme._14 | nme._15 | nme._16 | nme._17 | nme._18 | nme._19 | nme._20 |
                nme._21 | nme._22 => true
            case _ => false
          }

          (sym `is` Synthetic) &&
          (
            (
              (sym.owner `is` CaseClass) &&
              (
                sym.name == nme.equals_ ||
                sym.name == nme.productElement ||
                sym.name == nme.hashCode_ ||
                isCopyDefault ||
                isProductAccessor
              )
            ) ||
            (
              (sym.owner.companionClass `is` CaseClass) &&
              sym.name == nme.unapply
            )
          )
        }

        private def symbolIndex(tree: tpd.Tree): Int = tree match {
          case Apply(fun, args) => symbolIndex(fun) + 1
          case _ => 0
        }

        override def traverse(tree: tpd.Tree)(using ctx: DottyContext): Unit = {
          val sym = tree.symbol
          tree match {
            case Ident(_) if sym.hasGhostAnnotation && !ghostContext =>
              reportError(tree.sourcePos, s"Cannot access a ghost symbol outside of a ghost context. [ ${tree.show} in ${ctx.owner} ]")

            case Select(qual, _) if sym.hasGhostAnnotation && !ghostContext =>
              reportError(tree.sourcePos, s"Cannot access a ghost symbol outside of a ghost context. [ ${tree.show} in ${ctx.owner} ]")
              traverseChildren(tree)

            case m: tpd.MemberDef  =>
              // We consider some synthetic methods values as being inside ghost
              // but don't auto-annotate as such because we don't want all code to be removed.
              // They are synthetic case class methods that are harmless if they see some ghost nulls
              if (m.symbol.hasGhostAnnotation || effectivelyGhost(sym))
                withinGhostContext(traverseChildren(m))
              else
                traverseChildren(m)

            case f @ Apply(fun, args) if fun.symbol.hasGhostAnnotation =>
              traverse(fun)
              withinGhostContext(args foreach traverse)

            case f @ Apply(fun, args) =>
              val params = fun.symbol.denot.paramSymss
              val leadingTypeParams = params.exists(_.exists(_.isType))
              val termParams = if (leadingTypeParams) params.tail else params

              for ((param, arg) <- termParams(symbolIndex(fun)).zip(args))
                if (param.hasGhostAnnotation)
                  withinGhostContext(traverse(arg))
                else
                  traverse(arg)

            case Assign(lhs, rhs) =>
              if (lhs.symbol.hasGhostAnnotation)
                withinGhostContext(traverse(rhs))
              else
                traverseChildren(tree)

            case _ =>
              traverseChildren(tree)
          }
        }
      }
    }

  class Checker extends tpd.TreeTraverser {
    private val ScalaEnsuringMethod = requiredMethod("scala.Predef.Ensuring")

    private val StainlessLangPackage = getClassIfDefinedOrNone("stainless.lang.package$")
    private val ExternAnnotation = getClassIfDefinedOrNone("stainless.annotation.extern")
    private val IgnoreAnnotation = getClassIfDefinedOrNone("stainless.annotation.ignore")
    private val StainlessOld = StainlessLangPackage.map(_.info.decl(Names.termName("old")).symbol)
    private val StainlessBVObject = getModuleClassIfDefinedOrNone("stainless.math.BitVectors")
    private val StainlessBVClass = getClassIfDefinedOrNone("stainless.math.BitVectors.BV")
    private val StainlessBVArrayIndex = getModuleClassIfDefinedOrNone("stainless.math.BitVectors.ArrayIndexing")

    private val BigInt_ApplyMethods =
      (StainlessLangPackage.map(_.info.decl(Names.termName("BigInt")).info.decl(nme.apply).alternatives).getOrElse(Nil)
      ++ Symbols.requiredModule("scala.math.BigInt").info.decl(nme.apply).alternatives).toSet

    private val RequireMethods =
      defn.ScalaPredefModule.info.decl(Names.termName("require")).alternatives.toSet
        ++ getModuleIfDefinedOrNone("stainless.lang.StaticChecks").map(_.info.decl(Names.termName("require")).alternatives.toSet).getOrElse(Set.empty)

    private val stainlessReplacement = mutable.Map(
      defn.ListClass -> "stainless.collection.List",
      defn.NilModule.moduleClass -> "stainless.collection.Nil",
      defn.OptionClass -> "stainless.lang.Option",
      Symbols.requiredClass("scala.util.Either") -> "stainless.lang.Either",
      defn.ScalaPackageClass.info.decl(Names.termName("Nil")) -> "stainless.collection.Nil",
      Symbols.requiredClass("scala.collection.Map") -> "stainless.lang.Map",
      Symbols.requiredClass("scala.collection.immutable.Map") -> "stainless.lang.Map",
      Symbols.requiredClass("scala.collection.Set") -> "stainless.lang.Set",
      Symbols.requiredClass("scala.collection.immutable.Set") -> "stainless.lang.Set",
    )

    // We do not in general support the types for these methods, but we do extract them.
    // We therefore skip the typing check for them.
    private val bvSpecialFunctions =
      StainlessBVObject.map(bvObj => Set(
        bvObj.info.decl(termName("min")),
        bvObj.info.decl(termName("max"))
      )).getOrElse(Set.empty) ++
      StainlessBVArrayIndex.map(bvArray => Set(bvArray.info.decl(StdNames.nme.apply))).getOrElse(Set.empty) ++
      StainlessBVClass.map(bvClass => Set(
        bvClass.info.decl(termName("widen")),
        bvClass.info.decl(termName("narrow")),
        bvClass.info.decl(termName("toSigned")),
        bvClass.info.decl(termName("toUnsigned")),
      )).getOrElse(Set.empty)

    // Types that may show up due to inference that will later cause a missing dependency error
    // should we not report an error before.
    private val unsupportedTypes: Set[Symbol] = Set(
      defn.EnumClass,
      defn.SerializableClass,
      defn.ProductClass,
      defn.Mirror_ProductClass,
      defn.Mirror_SumClass,
      defn.Mirror_SingletonClass,
      defn.MatchableClass,
    )

    // method println is overloaded, so we need to add all overloads to our map
    addOverloadsToMap(defn.ScalaPredefModule.info.decl(Names.termName("println")), "stainless.io.StdOut.println")

    private def addOverloadsToMap(denot: Denotation, replacement: String): Unit =
      denot.alternatives.foreach(a => stainlessReplacement += a.symbol -> replacement)

    private def checkType(tree: tpd.Tree, tpe: Type): Unit = {
      object Errors {
        def empty: Errors = Errors(Set.empty, Set.empty)
      }
      case class Errors(libRepls: Set[(Symbol, String)], unsupported: Set[Type]) {
        def addReplacement(ts: (Symbol, String)): Errors = copy(libRepls = libRepls + ts)
        def addUnsupported(t: Type): Errors = copy(unsupported = unsupported + t)
      }
      val tyAcc = new TypeAccumulator[Errors] {
        override def apply(acc: Errors, tp: Type): Errors = {
          tp match {
            case SuperType(_, _) =>
              // We do not traverse SuperType as it contains all hierarchy,
              // including traits such as Product, etc. we do not support.
              return acc

            case ot: OrType =>
              // The extraction replace OrType with their join, so we do the same here to catch potential "Matchable" types
              return apply(acc, ot.join)

            // The extraction explicitly ignore Product and Serializable when they appear in AndType, we do the same here
            case AndType(tp, prod) if prod.typeSymbol == defn.ProductClass => return apply(acc, tp)
            case AndType(prod, tp) if prod.typeSymbol == defn.ProductClass => return apply(acc, tp)
            case AndType(tp, prod) if defn.isProductClass(prod.typeSymbol) => return apply(acc, tp)
            case AndType(prod, tp) if defn.isProductClass(prod.typeSymbol) => return apply(acc, tp)
            case AndType(tp, ser) if ser.typeSymbol == defn.SerializableClass => return apply(acc, tp)
            case AndType(ser, tp) if ser.typeSymbol == defn.SerializableClass => return apply(acc, tp)

            case _ => ()
          }

          val newAcc = {
            val tpSym = tp.typeSymbol
            if (stainlessReplacement.contains(tpSym))
              acc.addReplacement(tpSym -> stainlessReplacement(tpSym))
            else if (unsupportedTypes.contains(tpSym))
              acc.addUnsupported(tp)
            else acc
          }
          foldOver(newAcc, tp)
        }
      }

      val errs = tyAcc(Errors.empty, tpe)
      for ((sym, replacement) <- errs.libRepls) {
        reportError(tree.sourcePos, s"Scala API `${sym.name.show}` is not directly supported, please use `$replacement` instead.")
      }

      // Returns true if `needle` is in `hay` where the OrType in `needle` are replaced with their join, and return the transformed `needle` as well
      def contains(hay: Type, needle: Type): (Boolean, Type) = {
        var found = false
        val tm = new TypeMap() {
          override def apply(tp: Type): Type = {
            if (tp eq needle) {
              found = true
              tp
            } else {
              tp match {
                case ot: OrType => apply(ot.join)
                case AndType(tp, prod) if prod.typeSymbol == defn.ProductClass => apply(tp)
                case AndType(prod, tp) if prod.typeSymbol == defn.ProductClass => apply(tp)
                case AndType(tp, prod) if defn.isProductClass(prod.typeSymbol) => apply(tp)
                case AndType(prod, tp) if defn.isProductClass(prod.typeSymbol) => apply(tp)
                case AndType(tp, ser) if ser.typeSymbol == defn.SerializableClass => apply(tp)
                case AndType(ser, tp) if ser.typeSymbol == defn.SerializableClass => apply(tp)
                case _ => mapOver(tp)
              }
            }
          }
        }
        val widened = tm(hay)
        (found, widened)
      }

      def sourceOfType(tree: tpd.Tree, tp: Type): Unit = {
        tree match {
          case dd: tpd.DefDef =>
            dd.tpt match {
              case inf: tpd.InferredTypeTree =>
                val (contained, widened) = contains(inf.tpe, tp)
                if (contained) {
                  reportError(inf.sourcePos, s"Hint: the inferred return type of ${dd.name.show} is `${inf.tpe.show}`, and is widened to ${widened.show}")
                  sourceOfType(dd.rhs, tp)
                }
              case _ => ()
            }
          case bl: tpd.Block => sourceOfType(bl.expr, tp)
          case vd: tpd.ValDef =>
            vd.tpt match {
              case inf: tpd.InferredTypeTree =>
                val (contained, widened) = contains(inf.tpe, tp)
                if (contained) {
                  reportError(inf.sourcePos, s"Hint: the inferred type of ${vd.name.show} is `${inf.tpe.show}`, and is widened to ${widened.show}")
                  sourceOfType(vd.rhs, tp)
                }
              case _ => ()
            }
          case ite: tpd.If =>
            def branches(ite: tpd.If): Seq[tpd.Tree] = {
              Seq(ite.thenp) ++ (ite.elsep match {
                case ite2: tpd.If => branches(ite2)
                case t => Seq(t)
              })
            }
            val (contained, widened) = contains(ite.tpe, tp)
            if (contained) {
              reportError(ite.sourcePos, s"Hint: the type of this if expression is ${ite.tpe.show} and is widened to `${widened.show}`")
              val brchs = branches(ite)
              for (branch <- brchs) {
                reportError(branch.sourcePos, s"Hint: this branch type is `${branch.tpe.widenTermRefExpr.widenSingleton.show}`")
              }
            }
          case mtch: tpd.Match =>
            val (contained, widened) = contains(mtch.tpe, tp)
            if (contained) {
              reportError(mtch.sourcePos, s"Hint: the type of this match expression is ${mtch.tpe.show} and is widened to `${widened.show}`")
              for (branch <- mtch.cases) {
                reportError(branch.sourcePos, s"Hint: this case type is `${branch.tpe.widenTermRefExpr.widenSingleton.show}`")
              }
            }
          case _ => ()
        }
      }

      for (tp <- errs.unsupported) {
        reportError(tree.sourcePos, s"Type `${tp.show}` is unsupported")
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

    override def traverse(tree: tpd.Tree)(using ctx: DottyContext): Unit = {
      val sym = tree.symbol
      if (sym.exists) {
        // exit early if it's a subtree we shouldn't validate
        if (skipTraversal(sym)) {
          return
        }

        // Ignore class constructors because they duplicate param accessors (fields) which we already check
        // or skip if they are annotated with @extern.
        if (!sym.isConstructor) {
          // Widening TermRef allows to check for method type parameter, ValDef type, etc.
          // But do we not check type for ident, otherwise we will report each occurrence of the variable as erroneous
          // which will rapidly overwhelm the console.
          tree match {
            case _: tpd.Ident => return // Nothing to check further, so we return
            case Typed(_: tpd.Ident, _) =>
              // To avoid traversing the type tree which will result in reporting unsupported type again
              return
            case _ =>
              checkType(tree, tree.tpe.widenTermRefExpr)
          }
        }
      }

      tree match {
        case cd @ ExClassDef() =>
          val isSupported =
            sym.isClass ||
            (sym `is` Implicit) ||
            sym.isAnnotation

          if (!isSupported) {
            reportError(tree.sourcePos, "Only abstract classes, case classes, anonymous classes, and objects are allowed in Stainless.")
          }

          val template = cd.rhs.asInstanceOf[tpd.Template]
          val parents = template.parents.map(_.tpe).filterNot(isIgnored)
          if (parents.length > 1) {
            reportError(tree.sourcePos, s"Stainless supports only simple type hierarchies: Classes can only inherit from a single class/trait")
          }
          traverse(template.constr)
          template.body.foreach {
            case nested @ ExClassDef() =>
              reportError(nested.sourcePos, "Classes can only be defined at the top-level, within objects, or within methods")
            case tr => traverse(tr)
          }

        case dd @ DefDef(_, _, _, _) if sym.isConstructor =>
          if (!dd.rhs.isEmpty)
            reportError(tree.sourcePos, "Auxiliary constructors are not allowed in Stainless.")
          if (dd.termParamss.filter(termParams => termParams.exists(vdef => !isIgnoredParameterType(vdef.tpe))).size > 1)
              reportError(tree.sourcePos, "Multi-clauses classes are not allowed in Stainless.")
          if (dd.termParamss.flatten.nonEmpty && (sym.owner `isOneOf` AbstractOrTrait))
            reportError(tree.sourcePos, "Abstract class and trait constructor parameters are not allowed in Stainless.")
          traverse(dd.rhs)

        case dd @ DefDef(_, _, _, _) =>
          // recur only inside `dd.rhs`, as parameter/type parameters have been checked already in `checkType`
          traverse(dd.rhs)

        case vd @ ValDef(_, _, _) if sym.exists && sym.owner.isClass && !(sym.owner `isOneOf` AbstractOrTrait) && (sym `is` Mutable) && !sym.isOneOf(CaseAccessor | ParamAccessor) =>
          reportError(tree.sourcePos, "Variables are only allowed within functions and as constructor parameters in Stainless.")

        case Apply(fun, List(arg)) if StainlessOld.contains(sym) =>
          arg match {
            case This(_) => ()
            case t if t.symbol.isTerm && (t.symbol `is` Mutable) && !(t.symbol `is` Method) => ()
            case t =>
              reportError(t.sourcePos, s"Stainless `old` is only defined on `this` and variables.")
          }
          traverseChildren(tree)

        case Apply(fun, args) if BigInt_ApplyMethods(sym) =>
          if (args.size != 1 || !args.head.isInstanceOf[tpd.Literal])
            reportError(args.head.sourcePos, "Only literal arguments are allowed for BigInt.")
          traverseChildren(tree)

        case ExCall(Some(s @ Select(Super(_, _), _)), _, _, _) =>
          if ((s.symbol `is` Abstract) && !s.symbol.isConstructor)
            reportError(tree.sourcePos, "Cannot issue a super call to an abstract method.")
          traverseChildren(tree)

//        case Apply(ex, Seq(arg)) if ex.symbol == defn.throwMethod =>
//          reportError(tree.sourcePos, "throw expressions are unsupported in Stainless")
//          traverseChildren(tree)

        case Apply(fun, args) =>
          if (stainlessReplacement.contains(sym))
            reportError(tree.sourcePos, s"Scala API ($sym) no longer extracted, please use ${stainlessReplacement(sym)}")
          if (defn.ObjectMethods.contains(sym))
            reportError(tree.sourcePos, s"Method ${sym.name} on Object is not supported")
          traverseChildren(tree)

        case Try(_, cases, finalizer) =>
          if (cases.isEmpty && finalizer.isEmpty) reportError(tree.sourcePos, "try expressions are not supported in Stainless")
          else if (cases.isEmpty && !finalizer.isEmpty) reportError(tree.sourcePos, "try-finally expressions are not supported in Stainless")
          else if (finalizer.isEmpty) reportError(tree.sourcePos, "try-catch expressions are not supported in Stainless")
          else reportError(tree.sourcePos, "try-catch-finally expressions are not supported in Stainless")
          traverseChildren(tree)

        case tpl @ Template(_, _, _, _) =>
          for (t <- tpl.body if !(t.isDef || t.isType || t.isEmpty || t.isInstanceOf[tpd.Import])) {
            // `require` is allowed inside classes, but not inside objects
            if (RequireMethods(t.symbol) && (ctx.owner `is` ModuleClass))
              reportError(t.sourcePos, "`require` is not allowed inside object bodies.")
            else
              reportError(t.sourcePos, "Only definitions are allowed inside class bodies.")
          }
          traverse(tpl.constr)
          // We do not visit parents, as they will contain reference to synthetic classes such as Product, Serializable, etc.
          traverse(tpl.self)
          traverse(tpl.body)

        case _ =>
          traverseChildren(tree)
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
      isExtern || isIgnore || ((sym `is` Synthetic) && (sym ne ScalaEnsuringMethod) && !sym.isAnonymousFunction && !sym.isAnonymousFunction) ||
        (sym.owner eq defn.ClassTagModule_apply) ||
        bvSpecialFunctions(sym) || StainlessBVClass.contains(sym)
    }
  }
}
