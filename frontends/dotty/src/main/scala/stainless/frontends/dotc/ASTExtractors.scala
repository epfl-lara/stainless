package stainless
package frontends.dotc

import scala.language.implicitConversions

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Constants._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._
import core.Annotations._

import scala.collection.mutable.{ Map => MutableMap }

trait ASTExtractors {

  protected val ctx: dotty.tools.dotc.core.Contexts.Context
  import ctx.given

  def classFromName(nameStr: String): ClassSymbol = ctx.requiredClass(typeName(nameStr))
  def moduleFromName(nameStr: String): TermSymbol = ctx.requiredModule(typeName(nameStr))

  def getAnnotations(sym: Symbol, ignoreOwner: Boolean = false): Seq[(String, Seq[tpd.Tree])] = {
    val erased = if (sym.isEffectivelyErased) Seq(("ghost", Seq.empty)) else Seq()
    val inline = if (sym.annotations exists (_.symbol.fullName.toString == "scala.inline")) Seq(("inline", Seq.empty)) else Seq()
    val ownerSymbols = sym.maybeOwner.annotations.filter(annot =>
      !annot.name.startsWith("keep") || sym.isAccessor
    )

    erased ++ inline ++ (for {
      a <- sym.annotations ++ (if (!ignoreOwner) ownerSymbols else Set.empty)
      name = a.symbol.fullName.toString.replaceAll("\\.package\\$\\.", ".")
      if name startsWith "stainless.annotation."
      shortName = name drop "stainless.annotation.".length
    } yield (shortName, a.arguments)).foldLeft[(Set[String], Seq[(String, Seq[tpd.Tree])])]((Set(), Seq())) {
      case (acc @ (keys, _), (key, _)) if keys contains key => acc
      case ((keys, seq), (key, args)) => (keys + key, seq :+ (key -> args))
    }._2
  }

  // Well-known symbols that we match on

  protected lazy val scalaAnySym  = classFromName("scala.Any")
  protected lazy val scalaMapSym  = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym  = classFromName("scala.collection.immutable.Set")
  protected lazy val scalaListSym = classFromName("scala.collection.immutable.List")

  protected lazy val scalaProductClassSym = classFromName("scala.Product")

  protected lazy val exceptionSym = classFromName("stainless.lang.Exception")

  protected lazy val setSym         = classFromName("stainless.lang.Set")
  protected lazy val mapSym         = classFromName("stainless.lang.Map")
  protected lazy val mutableMapSym  = classFromName("stainless.lang.MutableMap")
  protected lazy val bagSym         = classFromName("stainless.lang.Bag")
  protected lazy val realSym        = classFromName("stainless.lang.Real")

  protected lazy val optionSymbol = classFromName("stainless.lang.Option")
  protected lazy val someSymbol   = classFromName("stainless.lang.Some")
  protected lazy val noneSymbol   = classFromName("stainless.lang.None")

  protected lazy val listSymbol = classFromName("stainless.collection.List")
  protected lazy val consSymbol = classFromName("stainless.collection.Cons")
  protected lazy val nilSymbol  = classFromName("stainless.collection.Nil")

  protected lazy val optionClassSym     = classFromName("scala.Option")
  protected lazy val arraySym           = classFromName("scala.Array")
  protected lazy val someClassSym       = classFromName("scala.Some")
//  protected lazy val byNameSym          = classFromName("scala.<byname>")
  protected lazy val bigIntSym          = classFromName("scala.math.BigInt")
  protected lazy val stringSym          = classFromName("java.lang.String")

  protected def functionTraitSym(i:Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple(sym: Symbol, size: Int): Boolean = {
    (size > 0 && size <= 22) && {
      (sym == classFromName(s"scala.Tuple$size")) ||
      (sym == moduleFromName(s"scala.Tuple$size"))
    }
  }

  object TupleSymbol {
    // It is particularly time expensive so we cache this.
    private val cache = MutableMap[Symbol, Option[Int]]()
    private val cardinality = """Tuple(\d{1,2})""".r
    def unapply(sym: Symbol): Option[Int] = cache.getOrElse(sym, {
      // First, extract a guess about the cardinality of the Tuple.
      // Then, confirm that this is indeed a regular Tuple.
      val name = sym.originalName.toString
      val res = name match {
        case cardinality(i) if isTuple(sym, i.toInt) => Some(i.toInt)
        case _ => None
      }

      cache(sym) = res
      res
    })

    def unapply(tpe: Type): Option[Int] = tpe.classSymbols.collectFirst { case TupleSymbol(i) => i }

    def unapply(tree: tpd.Tree): Option[Int] = unapply(tree.tpe)
  }

  def isBigIntSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

//  def isByNameSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      getResolvedTypeSym(sym.info.resultType.typeSymbol)
    } else {
      sym
    }
  }

  def isAnySym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaAnySym
  }

  def isSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == setSym
  }

  def isMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mapSym
  }

  def isMutableMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mutableMapSym
  }

  def isBagSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bagSym
  }

  def isRealSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == realSym
  }

  def isScalaSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaSetSym
  }

  def isScalaListSym(sym: Symbol): Boolean = {
    getResolvedTypeSym(sym) == scalaListSym
  }

  def isScalaMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaMapSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction(sym: Symbol, i: Int) : Boolean = {
    0 <= i && i <= 22 && sym == functionTraitSym(i)
  }

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def hasIntType(t: tpd.Tree) = {
    val tpe = t.tpe.widen
    tpe =:= defn.IntClass.info
  }

  def hasBigIntType(t: tpd.Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t: tpd.Tree) = isStringSym(t.tpe.typeSymbol)

//  def hasRealType(t: tpd.Tree) = isRealSym(t.tpe.typeSymbol)

  def isDefaultGetter(sym: Symbol) = {
    (sym is Synthetic) && sym.name.isTermName && sym.name.toTermName.toString.contains("$default$")
  }

  def isCopyMethod(sym: Symbol) = {
    (sym is Synthetic) && sym.name.isTermName && sym.name.toTermName.toString == "copy"
  }

  def canExtractSynthetic(sym: Symbol) = {
    (sym is Implicit) ||
    isDefaultGetter(sym) ||
    isCopyMethod(sym)
  }

  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  // Actual extractors

  object AuxiliaryExtractors {
    object ExSelected {
      def unapplySeq(select: tpd.Select): Option[Seq[String]] = select match {
        case Select(This(tname), name) =>
          Some(Seq(tname.toString, name.toString))
        case Select(from: tpd.Select, name) =>
          unapplySeq(from).map(seq => seq :+ name.toString)
        case Select(from: tpd.Ident, name) =>
          Some(Seq(from.toString, name.toString))
        case _ => None
      }
    }

    object ExNamed {
      def unapply(name: Name): Option[String] = Some(name.toString)
    }

    object ExSymbol {
      def unapplySeq(arg: Any): Option[Seq[String]] = arg match {
        case (t: Tree[_]) => Some(t.symbol.fullName.toString.split('.').toSeq)
        case sym: Symbol => Some(sym.fullName.toString.split('.').toSeq)
      }
    }
  }

  object ExpressionExtractors {

    object ExIdentifier {
      def unapply(tree: tpd.Tree): Option[(Symbol, tpd.Ident)] = tree match {
        case i: tpd.Ident => Some((i.symbol, i))
        case _ => None
      }
    }

    object ExThis {
      def unapply(tree: tpd.Tree): Option[(Symbol, tpd.This)] = tree match {
        case thiz: tpd.This => Some((thiz.symbol, thiz))
        case _ => None
      }
    }

    object ExTyped {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Typed(e,t) => Some((e, t))
        case _ => None
      }
    }

    object ExLiteral {
      def unapply(tree: tpd.Literal): Boolean = true
    }

    object ExBooleanLiteral {
      def unapply(tree: tpd.Literal): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExCharLiteral {
      def unapply(tree: tpd.Literal): Option[Char] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.CharClass => Some(c.charValue)
        case _ => None
      }
    }

    object ExInt8Literal {
      def unapply(tree: tpd.Literal): Option[Byte] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.ByteClass => Some(c.byteValue)
        case _ => None
      }
    }

    object ExInt16Literal {
      def unapply(tree: tpd.Literal): Option[Short] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.ShortClass => Some(c.shortValue)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: tpd.Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.IntClass => Some(c.intValue)
        case _ => None
      }
    }

    object ExInt64Literal {
      def unapply(tree: tpd.Literal): Option[Long] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.LongClass => Some(c.longValue)
        case _ => None
      }
    }

    object ExBigIntLiteral {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("scala", "math", "BigInt$", "apply"), Seq(i)) => Some(i)
        case Apply(ExSymbol("stainless", "lang", "package$", "BigInt$", "apply"), Seq(i)) => Some(i)
        case _ => None
      }
    }

    object ExRealLiteral {
      def unapply(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case Apply(ExSymbol("stainless", "lang", "Real$", "apply"), args) => Some(args)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: tpd.Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe.classSymbol == defn.UnitClass => true
        case _ => false
      }
    }

    /** Returns a string literal from a constant string literal. */
    object ExStringLiteral {
      def unapply(tree: tpd.Tree): Option[String] = tree  match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.StringClass =>
          Some(c.stringValue)
        case _ =>
          None
      }
    }

    object ExThisCall {
      def unapply(tree: tpd.Tree): Option[(ThisType, Symbol, Seq[tpd.Tree], Seq[tpd.Tree])] = {
        val optCall = tree match {
          case id @ Ident(_) => Some((id, Nil, Nil))
          case Apply(id @ Ident(_), args) => Some((id, Nil, args))
          case TypeApply(id @ Ident(_), tps) => Some((id, tps, Nil))
          case Apply(TypeApply(id @ Ident(_), tps), args) => Some((id, tps, args))
          case _ => None
        }

        optCall.flatMap { case (id, tps, args) =>
          id.tpe match {
            case ref @ TermRef(tt: ThisType, _) if !(ref.symbol.owner is Module) =>
              Some((tt, id.symbol, tps, args))
            case _ => None
          }
        }
      }
    }

    object ExLambda {
      def unapply(tree: tpd.Tree): Option[(Seq[tpd.ValDef], tpd.Tree)] = tree match {
        case Block(Seq(dd @ DefDef(_, _, Seq(vparams), _, _)), ExUnwrapped(Closure(Nil, call, _))) if call.symbol == dd.symbol =>
          Some((vparams, dd.rhs))
        case _ => None
      }
    }

    /** Matches the construct stainless.math.wrapping[A](a) and returns a */
    object ExWrapping {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree  match {
        case Apply(TypeApply(ExSymbol("stainless", "math", "package$", "wrapping"), Seq(_)), tree :: Nil) =>
          Some(tree)
        case _ =>
          None
      }
    }

    // Dotc seems slightly less consistent than scalac: it uses to format for
    // casts. Like scalac, it uses Select for `.toByte`, but it also uses
    // Apply("byte2int", arg) for implicit conversions (and perhaps for other
    // conversions as well).
    object ExCastCall {
      // Returns: (arg, from, to)
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Type, Type)] = tree match {
        case Apply(Ident(name), List(arg)) =>
          val tmp: Option[(Symbol, Symbol)] = name.toString match {
            case "byte2short" => Some(defn.ByteClass, defn.ShortClass)
            case "byte2int"   => Some(defn.ByteClass, defn.IntClass)
            case "byte2long"  => Some(defn.ByteClass, defn.LongClass)

            case "short2byte" => Some(defn.ShortClass, defn.ByteClass)
            case "short2int"  => Some(defn.ShortClass, defn.IntClass)
            case "short2long" => Some(defn.ShortClass, defn.LongClass)

            case "int2byte"   => Some(defn.IntClass, defn.ByteClass)
            case "int2short"  => Some(defn.IntClass, defn.ShortClass)
            case "int2long"   => Some(defn.IntClass, defn.LongClass)

            case "long2byte"  => Some(defn.LongClass, defn.ByteClass)
            case "long2short" => Some(defn.LongClass, defn.ShortClass)
            case "long2int"   => Some(defn.LongClass, defn.IntClass)

            case _ => None
          }

          tmp map { case (from, to) => (arg, from.info, to.info) }
        case _ => None
      }
    }

    object ExCall {
      def unapply(tree: tpd.Tree): Option[(Option[tpd.Tree], Symbol, Seq[tpd.Tree], Seq[tpd.Tree])] = {
        val optCall = tree match {
          case tree @ Ident(_) => Some((None, tree.symbol, Nil, Nil))
          case tree @ Select(qualifier, _) => Some((Some(qualifier), tree.symbol, Nil, Nil))
          case tree @ Apply(id: tpd.Ident, args) => Some((None, id.symbol, Nil, args))
          case tree @ Apply(select @ Select(qualifier, _), args) => Some((Some(qualifier), select.symbol, Nil, args))
          case tree @ TypeApply(id: tpd.Ident, tps) => Some((None, id.symbol, tps, Nil))
          case tree @ TypeApply(select @ Select(qualifier, _), tps) => Some((Some(qualifier), select.symbol, tps, Nil))
          case tree @ Apply(ExCall(caller, sym, tps, args), newArgs) => Some((caller, sym, tps, args ++ newArgs))
          case tree @ TypeApply(ExCall(caller, sym, tps, args), newTps) => Some((caller, sym, tps ++ newTps, args))
          case _ => None
        }

        optCall.map { case (rec, sym, tps, args) =>
          val newRec = rec.filterNot { r =>
            (r.symbol is Module) && !(r.symbol is Case)
          }
          (newRec, sym, tps, args)
        }
      }
    }

    object ExConstructor {
      def unapply(tree: tpd.Tree): Option[(Type, Seq[tpd.Tree])] = tree match {
        case Apply(Select(New(tpt), nme.CONSTRUCTOR), args) =>
          Some((tpt.tpe, args))

        case Apply(TypeApply(Select(New(tpt), nme.CONSTRUCTOR), _), args) =>
          Some((tree.tpe, args))

        case Apply(e, args) if (
          (e.symbol.owner is Module) &&
          (e.symbol is Synthetic) &&
          (e.symbol.name.toString == "apply")
        ) => Some((tree.tpe, args))

        case Select(s, _) if (tree.symbol is Case) && (tree.symbol is Module) =>
          Some((tree.tpe, Seq()))

        case Ident(_) if (tree.symbol is Case) && (tree.symbol is Module) =>
          Some((tree.tpe, Seq()))

        case _ =>
          None
      }
    }

    object ExTuple {
      def unapply(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case Apply(Select(New(tupleType), nme.CONSTRUCTOR), args) if isTuple(tupleType.symbol, args.size) =>
          Some(args)
        case Apply(TypeApply(Select(ExIdentifier(sym, id), _), _), args) if isTuple(sym, args.size) =>
          Some(args)
        case Apply(TypeApply(Select(
          Apply(TypeApply(ExSymbol("scala", "Predef$", "ArrowAssoc"), Seq(_)), Seq(from)),
          ExNamed("->") | ExNamed("$minus$greater")
        ), Seq(_)), Seq(to)) => Some(Seq(from, to))
        case _ => None
      }
    }

    object ExTupleSelect {
      private val Pattern = """_(\d{1,2})""".r

      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Int)] = tree match {
        case Select(tuple @ TupleSymbol(i), ExNamed(Pattern(n))) if n.toInt <= i =>
          Some((tuple, n.toInt))
        case _ => None
      }
    }

    object ExUnwrapped {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(
            ExSymbol("scala", "Predef$", "Ensuring") |
            ExSymbol("stainless", "lang", "StaticChecks$", "Ensuring"),
            Seq(arg)) => Some(arg)

        case Apply(ExSymbol("stainless", "lang", "package$", "Throwing"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "BooleanDecorations"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "SpecsDecorations"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "StringDecorations"), Seq(arg)) => Some(arg)
        case Apply(ExSymbol("stainless", "lang", "package$", "WhileDecorations"), Seq(arg)) => Some(arg)
        case _ => Some(tree)
      }
    }
  }

  object StructuralExtractors {

    object ExObjectDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        val sym = td.symbol
        td.isClassDef && ((sym is ModuleClass) || (sym is Package)) && !(sym is Synthetic) && !(sym is Case)
      }
    }

    object ExClassDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        td.isClassDef
      }
    }

    object ExTypeDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        !td.isClassDef
      }
    }

    object ExFunctionDef {
      def unapply(tree: tpd.DefDef): Option[(Symbol, Seq[tpd.TypeDef], Seq[tpd.ValDef], Type, tpd.Tree)] = tree match {
        case dd @ DefDef(name, tparams, vparamss, tpt, rhs) =>
          if ((
            name != nme.CONSTRUCTOR &&
            !dd.symbol.is(Accessor) &&
            !dd.symbol.is(Synthetic) &&
            !dd.symbol.is(Label)
          ) || (
            (dd.symbol is Synthetic) &&
            canExtractSynthetic(dd.symbol) &&
            !(getAnnotations(tpt.symbol) exists (_._1 == "ignore"))
          )) {
            Some((dd.symbol, tparams, vparamss.flatten, tpt.tpe, dd.rhs))
          } else {
            None
          }

        case _ => None
      }
    }

    object ExFieldDef {
      def unapply(tree: tpd.ValDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case vd @ ValDef(_, tpt, _) if (
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            !(sym is Synthetic) && !(sym is Mutable)
          ) => Some((sym, tpt.tpe, vd.rhs))

          case _ => None
        }
      }
    }

    object ExMutableFieldDef {
      def unapply(tree: tpd.ValDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case ValDef(_, tpt, _) if (
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            !(sym is Synthetic) && (sym is Mutable)
          ) => Some((sym, tpt.tpe, tree.rhs))

          case _ => None
        }
      }
    }

    object ExFieldAccessorFunction {
      /** Matches the accessor function of a field */
      def unapply(dd: tpd.DefDef): Option[(Symbol, Type, Seq[tpd.ValDef], tpd.Tree)] = dd match {
        case DefDef(name, tparams, vparamss, tpt, _) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          (dd.symbol is Accessor) && !(dd.symbol is Lazy)
        ) =>
          Some((dd.symbol, tpt.tpe, vparamss.flatten, dd.rhs))
        case _ => None
      }
    }

    object ExLazyFieldAccessorFunction {
      def unapply(dd: tpd.DefDef): Option[(Symbol, Type, tpd.Tree)] = dd match {
        case DefDef(name, tparams, vparamss, tpt, _) if(
          vparamss.size <= 1 && name != nme.CONSTRUCTOR &&
          !(dd.symbol is Synthetic) && (dd.symbol is Accessor) && (dd.symbol is Lazy)
        ) =>
          Some((dd.symbol, tpt.tpe, dd.rhs))
        case _ => None
      }
    }

    object ExFieldAssign {
      def unapply(tree: tpd.Assign): Option[(Symbol, tpd.Tree, tpd.Tree)] = tree match {
        // case Assign(sel@Select(This(_), v), rhs) => Some((sel.symbol, sel, rhs))
        case Assign(sel@Select(lhs, _), rhs) => Some((sel.symbol, lhs, rhs))
        case _ => None
      }
    }

    object ExWhile {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case WhileDo(cond, body) => Some((cond, body))
        case _ => None
      }
    }

    object ExWhileWithInvariant {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree, tpd.Tree)] = tree match {
        case Apply(
          Select(
            Apply(
              ExSymbol("stainless", "lang", "package$", "WhileDecorations"),
              List(ExWhile(cond, body)),
            ),
            ExNamed("invariant"),
          ),
          List(pred)
        ) => Some((cond, body, pred))
        case _ => None
      }
    }

    object ExRequire {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, Boolean)] = tree match {
        case Apply(ExSymbol("scala", "Predef$", "require"), Seq(body)) =>
          Some((body, false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "require"), Seq(body)) =>
          Some((body, true))

        case _ => None
      }
    }

    object ExDecreases {
      def unapply(tree: tpd.Apply): Option[Seq[tpd.Tree]] = tree match {
        case Apply(ExSymbol("stainless", "lang", "package$", "decreases"), args) => Some(args)
        case _ => None
      }
    }

    object ExAssert {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, Option[String], Boolean)] = tree match {
        case Apply(ExSymbol("dotty", "DottyPredef$", "assert"), Seq(body)) =>
          Some((body, None, false))

        case Apply(ExSymbol("scala", "Predef$", "assert"), Seq(body)) =>
          Some((body, None, false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "assert"), Seq(body)) =>
          Some((body, None, true))

        case Apply(ExSymbol("dotty", "DottyPredef$", "assert"), Seq(body, Literal(cnst: Constant))) =>
          Some((body, Some(cnst.stringValue), false))

        case Apply(ExSymbol("scala", "Predef$", "assert"), Seq(body, Literal(cnst: Constant))) =>
          Some((body, Some(cnst.stringValue), false))

        case Apply(ExSymbol("stainless", "lang", "StaticChecks$", "assert"), Seq(body, Literal(cnst: Constant))) =>
          Some((body, Some(cnst.stringValue), true))

        case _ => None
      }
    }

    object ExEnsuring {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree, Boolean)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("scala", "Predef$", "Ensuring", "ensuring"),
          _, Seq(contract)
        ) => Some((rec, contract, false))

        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "StaticChecks$", "Ensuring", "ensuring"),
          _, Seq(contract)
        ) => Some((rec, contract, true))

        case _ => None
      }
    }

    object ExThrowing {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "Throwing", "throwing"),
          _, Seq(contract)
        ) => Some((rec, contract))
        case _ => None
      }
    }

    object ExHolds {
      def unapplySeq(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "BooleanDecorations", "holds"),
          Seq(), args) => Some(rec +: args)
        case _ => None
      }
    }

    object ExHoldsBecause {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExHolds(body, Apply(ExSymbol("stainless", "lang", "package$", "because"), Seq(proof))) =>
          Some((body, proof))

        case Apply(
          Select(
            Apply(
              ExSymbol("stainless", "lang" | "proof", "package$", "boolean2ProofOps"),
              List(ExHolds(body)),
            ),
            ExNamed("because"),
          ),
          List(proof)
        ) =>
          Some((body, proof))

        case _ => None
      }
    }

    object ExBecause {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "proof" | "equations", "package$", "ProofOps", "because"),
          Seq(), Seq(proof)
        ) =>
          def extract(t: tpd.Tree): Option[tpd.Tree] = t match {
            case Apply(ExSymbol("stainless", "proof" | "equations", "package$", "ProofOps$", "apply"), Seq(body)) => Some(body)
            case Block(Seq(v @ ValDef(_, _, _)), e) => extract(e).filter(_.symbol == v.symbol).map(_ => v.rhs)
            case Inlined(_, members, last) => extract(Block(members, last))
            case _ => None
          }
          extract(rec).map(_ -> proof)

        case _ =>
          None
      }
    }

    object ExComputes {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "SpecsDecorations", "computes"),
          _, Seq(expected)) => Some((rec, expected))
        case _ => None
      }
    }

    /** Extracts the `(input, output) passes { case In => Out ...}` and returns (input, output, list of case classes) */
    object ExPasses {
      import ExpressionExtractors._

      def unapply(tree: tpd.Apply) : Option[(tpd.Tree, tpd.Tree, List[tpd.CaseDef])] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "Passes", "passes"),
          _,
          Seq(ExLambda(_, Match(_, cases)))
        ) =>
          def extract(t: tpd.Tree): Option[tpd.Tree] = t match {
            case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "Passes"), _), Seq(body)) =>
              Some(body)
            case _ => None
          }

          extract(rec) flatMap {
            case ExTuple(Seq(in, out)) => Some((in, out, cases))
            case res => None
          }

        case _ => None
      }
    }

    object ExError {
      def unapply(tree: tpd.Apply) : Option[(String, tpd.Tree)] = tree match {
        case a @ Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "error"), List(tpe)), List(lit : tpd.Literal)) =>
          Some((lit.const.stringValue, tpe))
        case _ =>
          None
      }
    }

    object ExOld {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "old"), Seq(_)), Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    object ExSnapshot {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(TypeApply(ExSymbol("stainless", "lang", "package$", "snapshot"), Seq(_)), Seq(arg)) => Some(arg)
        case _ => None
      }
    }

    object ExIndexedAt {
      def unapply(annot: Annotation): Option[tpd.Tree] = annot match {
        case ConcreteAnnotation(
          Apply(Select(New(ExSymbol("stainless", "annotation", "indexedAt")), _), Seq(arg))
        ) => Some(arg)
        case _ => None
      }
    }
  }

  object ExIdentity {
    def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
      case Apply(TypeApply(ExSymbol("scala", "Predef$", "identity"), Seq(_)), Seq(body)) =>
        Some(body)
      case Apply(TypeApply(ExSymbol("scala", "Predef$", "locally"), Seq(_)), Seq(body)) =>
        Some(body)
      case _ => None
    }
  }

}
