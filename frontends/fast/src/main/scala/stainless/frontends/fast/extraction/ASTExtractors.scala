package stainless.frontends.fast.extraction

import dotty.tools.dotc._
import ast.untpd
import ast.Trees._
import core.Contexts._
import core.Constants._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._

import scala.collection.mutable.{ Map => MutableMap }

trait ASTExtractors extends ExtractMods {

  protected implicit val ctx: Context

  def classFromName(nameStr: String): ClassSymbol = ctx.requiredClass(typeName(nameStr))

  def getAnnotations(sym: Symbol, ignoreOwner: Boolean = false): Seq[(String, Seq[untpd.Tree])] = {
    (for {
      a <- sym.annotations ++ (if (!ignoreOwner) sym.maybeOwner.annotations else Set.empty)
      name = a.symbol.fullName.toString.replaceAll("\\.package\\$\\.", ".")
      if name startsWith "stainless.annotation."
      shortName = name drop "stainless.annotation.".length
    } yield (shortName, a.arguments)).foldLeft[(Set[String], Seq[(String, Seq[untpd.Tree])])]((Set(), Seq())) {
      case (acc@(keys, _), (key, _)) if keys contains key => acc
      case ((keys, seq), (key, args)) => (keys + key, seq :+ (key -> args))
    }._2
  }

  // Well-known symbols that we match on

  protected lazy val scalaMapSym = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym = classFromName("scala.collection.immutable.Set")
  protected lazy val scalaListSym = classFromName("scala.collection.immutable.List")

  protected lazy val exceptionSym = classFromName("stainless.lang.Exception")

  protected lazy val setSym = classFromName("stainless.lang.Set")
  protected lazy val mapSym = classFromName("stainless.lang.Map")
  protected lazy val bagSym = classFromName("stainless.lang.Bag")
  protected lazy val realSym = classFromName("stainless.lang.Real")

  protected lazy val optionSymbol = classFromName("stainless.lang.Option")
  protected lazy val someSymbol = classFromName("stainless.lang.Some")
  protected lazy val noneSymbol = classFromName("stainless.lang.None")

  protected lazy val listSymbol = classFromName("stainless.collection.List")
  protected lazy val consSymbol = classFromName("stainless.collection.Cons")
  protected lazy val nilSymbol = classFromName("stainless.collection.Nil")

  protected lazy val optionClassSym = classFromName("scala.Option")
  protected lazy val arraySym = classFromName("scala.Array")
  protected lazy val someClassSym = classFromName("scala.Some")
  //  protected lazy val byNameSym          = classFromName("scala.<byname>")
  protected lazy val bigIntSym = classFromName("scala.math.BigInt")
  protected lazy val stringSym = classFromName("java.lang.String")

  protected def functionTraitSym(i: Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple(sym: Symbol, size: Int): Boolean = (size > 0 && size <= 22) && (sym == classFromName(s"scala.Tuple$size"))

  //  object TupleSymbol {
  //    // It is particularly time expensive so we cache this.
  //    private val cache = MutableMap[Symbol, Option[Int]]()
  //    private val cardinality = """Tuple(\d{1,2})""".r
  //    def unapply(sym: Symbol): Option[Int] = cache.getOrElseUpdate(sym, {
  //      // First, extract a guess about the cardinality of the Tuple.
  //      // Then, confirm that this is indeed a regular Tuple.
  //      val name = sym.originalName.toString
  //      name match {
  //        case cardinality(i) if isTuple(sym, i.toInt) => Some(i.toInt)
  //        case _ => None
  //      }
  //    })
  //
  //    def unapply(tpe: Type): Option[Int] = tpe.classSymbols.collectFirst { case TupleSymbol(i) => i }
  //
  //    def unapply(tree: untpd.Tree): Option[Int] = unapply(tree.tpe)
  //  }

  //  def hasRealType(t: untpd.Tree) = isRealSym(t.tpe.typeSymbol)

  def isDefaultGetter(sym: Symbol) = {
    sym.name.isTermName && sym.name.toTermName.toString.contains("$default$")
  }

  def isCopyMethod(sym: Symbol) = {
    sym.name.isTermName && sym.name.toTermName.toString == "copy"
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
  }

  object ExpressionExtractors {

  }

  object StructuralExtractors {

    object ExFunctionDef {
      def unapply(dd: untpd.DefDef): Option[(Symbol, Seq[untpd.TypeDef], Seq[untpd.ValDef], untpd.Tree, untpd.Tree)] = {
        val mods = extractMods(dd)
        dd match {
          case DefDef(name, tparams, vparamss, tpt, rhs) =>
            if ((
              name != nme.CONSTRUCTOR &&
                mods.flags.is(Accessor) &&
                mods.flags.is(Synthetic) &&
                mods.flags.is(Label)
              ) || (
              (dd.symbol is Synthetic)
              //              &&
              //              canExtractSynthetic(dd.symbol) &&
              //              !(getAnnotations(tpt.symbol) contains "ignore")
              )) {
              Some((dd.symbol, tparams, vparamss.flatten, tpt.tpe, dd.rhs))
            } else {
              None
            }

          case _ => None
        }
      }
    }

    object ExObjectDef {
      def unapply(td: untpd.ModuleDef): Boolean = {
        //        val sym = td.symbol
        //        td.isClassDef && ((sym is ModuleClass) || (sym is Package)) && !(sym is Synthetic) && !(sym is Case)
        true
      }
    }

  }

}
