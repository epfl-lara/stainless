/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

import inox.utils
import inox.utils.InoxSerializer

import java.io.{File, FileWriter}
import scala.reflect.runtime.universe._
import scala.collection.mutable.{ArrayBuffer, HashMap => MutableMap, HashSet => MutableSet}

trait RustInteropGeneration { self: InoxSerializer =>
  // Used to replace `Identifier`, if present
  protected val optSymbolIdentifierT: Option[Type] = None

  // The `Pattern` type, if any
  protected val optPatternT: Option[Type] = None

  def generateRustInterop(file: File) = {
    val writer = new FileWriter(file)
    def write(s: String) = {
      writer.write(s)
      writer.write('\n')
    }

    val TreeT = typeOf[inox.trees.Tree]
    val DefinitionT = typeOf[inox.trees.Definition]
    val FlagT = typeOf[inox.trees.Flag]
    val ExprT = typeOf[inox.trees.Expr]
    val TypeT = typeOf[inox.trees.Type]

    val IdentifierT = typeOf[inox.ast.Identifier]
    val VariableT = typeOf[inox.trees.Variable]
    val BigIntT = typeOf[scala.math.BigInt]

    case class Field(name: String, tpe: Type)
    case class Class(
                      classSymbol: ClassSymbol,
                      fields: List[Field],
                      customIdentity: Option[String],
                      markerId: Int,
                      needsHash: Boolean,
                      needsSerializable: Boolean)

    var definitionClasses = ArrayBuffer[Class]()
    var flagClasses = ArrayBuffer[Class]()
    var exprClasses = ArrayBuffer[Class]()
    var typeClasses = ArrayBuffer[Class]()
    var patternClasses = ArrayBuffer[Class]()
    var otherClasses = ArrayBuffer[Class]()

    // For some fields Stainless trees require types that are more
    // specific than can (easily) be represented in Rust.
    // We fix two cases:
    // - To avoid a separate abstract class Pattern, we replace them by Expr
    // - To avoid distinguishing the union of Identifier and SymbolIdentifier,
    //    we always require the more specific SymbolIdentifier (Stainless only)
    def fixUnrepresentableTypes(tpe: Type): Type = tpe match {
      case TypeRef(_, constr, args) if args.nonEmpty =>
        appliedType(constr, args.map(fixUnrepresentableTypes))
      case TypeRef(_, sym, _) =>
        sym.name.toString match {
          case "Identifier" => optSymbolIdentifierT.getOrElse(tpe)
          case _ => tpe
        }
      case tpe =>
        tpe
    }

    // Collect the list of Inox classes to generate Rust code for
    classSerializers.foreach { case (runtimeClass, serializer) =>
      val rootMirror = scala.reflect.runtime.universe.runtimeMirror(runtimeClass.getClassLoader)
      val classSymbol = rootMirror.classSymbol(runtimeClass)

      val rawFields = fieldsForClassSymbol(classSymbol)
      var fields: List[Field] = rawFields.map { field =>
        var name = field.name.toString
        if (name == "in")
          name = "in_" // `in` is a rust keyword
        val tpe = field.info match {
          case NullaryMethodType(tpe) => tpe
          case tpe => tpe
        }
        Field(name, fixUnrepresentableTypes(tpe))
      } .toList

      val baseClasses = classSymbol.toType.baseClasses
      val isDefinition = baseClasses.contains(DefinitionT.typeSymbol)
      val isFlag = baseClasses.contains(FlagT.typeSymbol)
      val isExpr = baseClasses.contains(ExprT.typeSymbol)
      val isType = baseClasses.contains(TypeT.typeSymbol)
      val isPattern = optPatternT.map(tpe => baseClasses.contains(tpe.typeSymbol)).getOrElse(false)

      val name = classSymbol.name.toString

      var customIdentity: Option[String] = None
      var needsHash = true
      var needsSerializable = true
      var ignore = false

      def replaceFieldType(name: String, newTpe: Type): Unit =
        fields = fields.map {
          case f if f.name == name => f.copy(tpe = newTpe)
          case f => f
        }

      name match {
        case "ADTSort" | "FunDef" | "ClassDef" =>
          customIdentity = Some("id")
        case "TypeParameterDef" =>
          customIdentity = Some("tp.id")
          needsSerializable = false
        case "ValDef" =>
          fields = fields :+ Field("v", VariableT)
          customIdentity = Some("v.id")
          needsSerializable = false
        case "TypeParameter" =>
          customIdentity = Some("id")
        case "ADTConstructor" =>
          customIdentity = Some("id")
        case "Annotation" =>
          // TODO: Support Seq[Any] rather than only Seq[Expr] in Annotation
          replaceFieldType("args", typeOf[Seq[inox.trees.Expr]])
        case "BVLiteral" =>
          replaceFieldType("value", BigIntT) // to avoid BitSet
          needsSerializable = false
        case "LiteralPattern" =>
          replaceFieldType("lit", ExprT) // to avoid generic Literal[T]
        case "LargeArray" =>
          needsHash = false
        case "Identifier" =>
          customIdentity = Some("globalId")
          needsSerializable = false
        case "SymbolIdentifier" =>
          fields = List(Field("id", IdentifierT), Field("symbol_path", typeOf[Seq[String]]))
          customIdentity = Some("id.globalId")
          needsSerializable = false
        case "Symbol" =>
          customIdentity = Some("id")
          needsSerializable = false
        case "SerializationResult" =>
          ignore = true
        case "TerminationStatus" | "Unknown" | "Terminating" | "NonTerminating" =>
          ignore = true
        case _ =>
      }

      if (!ignore) {
        val clazz = Class(classSymbol, fields, customIdentity, serializer.id, needsHash, needsSerializable)
        if (isDefinition)   definitionClasses += clazz
        else if (isFlag)    flagClasses += clazz
        else if (isExpr)    exprClasses += clazz
        else if (isType)    typeClasses += clazz
        else if (isPattern) patternClasses += clazz
        else                otherClasses += clazz
      }
    }

    definitionClasses = definitionClasses.sortBy(_.classSymbol.name.toString)
    flagClasses       = flagClasses.sortBy(_.classSymbol.name.toString)
    exprClasses       = exprClasses.sortBy(_.classSymbol.name.toString)
    typeClasses       = typeClasses.sortBy(_.classSymbol.name.toString)
    patternClasses    = patternClasses.sortBy(_.classSymbol.name.toString)
    otherClasses      = otherClasses.sortBy(_.classSymbol.name.toString)

    // Helpers for computing which annotations are required in the generated Rust code

    val allClasses = definitionClasses ++ flagClasses ++ exprClasses ++ typeClasses ++ patternClasses ++ otherClasses
    val abstractClassTypes = (Set(TreeT, DefinitionT, FlagT, ExprT, TypeT) ++ optPatternT).map(_.typeSymbol)

    def shouldIgnoreTypeArgs(tpe: Type): Boolean =
      tpe.typeSymbol.name.toString == "LiteralPattern"

    def isInoxType(tpe: Type): Boolean =
      (tpe.baseClasses.toSet & Set(TreeT.typeSymbol, FlagT.typeSymbol)).nonEmpty ||
        tpe.typeSymbol == IdentifierT.typeSymbol ||
        optSymbolIdentifierT.map(tpe.typeSymbol == _.typeSymbol).getOrElse(false)
    def isAllocType(tpe: Type): Boolean =
      isInoxType(tpe) && !abstractClassTypes.contains(tpe.typeSymbol)

    def inoxTypesInType(tpe: Type): Set[Type] =
      if (isInoxType(tpe)) Set(tpe) else tpe.typeArgs.flatMap(inoxTypesInType).toSet
    def allocTypesInType(tpe: Type): Set[Type] =
      if (isAllocType(tpe)) Set(tpe) else tpe.typeArgs.flatMap(allocTypesInType).toSet

    val classIsDirectPartOf = {
      val result =
        MutableMap[ClassSymbol, MutableSet[ClassSymbol]]().withDefaultValue(MutableSet.empty)
      for { clazz <- allClasses
            field <- clazz.fields
            fieldTpe <- inoxTypesInType(field.tpe)
            fieldSym = fieldTpe.typeSymbol if fieldSym.isClass
            }
        result(fieldSym.asClass) += clazz.classSymbol

      def addParent(parentTpe: Type, classes: ArrayBuffer[Class]) = {
        val parentSym = parentTpe.typeSymbol.asClass
        classes.foreach(c => result(c.classSymbol) += parentSym)
      }
      addParent(DefinitionT, definitionClasses)
      addParent(FlagT, flagClasses)
      addParent(ExprT, exprClasses)
      addParent(TypeT, typeClasses)
      optPatternT.foreach { PatternT => addParent(PatternT, patternClasses) }

      result
    }

    val classNeedsLifetime: Set[ClassSymbol] = {
      val initialLifetimeUsers =
        allClasses
          .filter(_.fields.exists(f => allocTypesInType(f.tpe).nonEmpty))
          .map(_.classSymbol)
          .toSet
      inox.utils.fixpoint[Set[ClassSymbol]]({
        classes => classes.flatMap(classIsDirectPartOf).toSet
      })(initialLifetimeUsers)
    }

    def typeNeedsLifetime(tpe: Type): Boolean = {
      val sym = tpe.typeSymbol
      sym.isClass && classNeedsLifetime(sym.asClass)
    }

    def renderLifetimeFor(tpe: Type): String =
      if (typeNeedsLifetime(tpe)) "<'a>" else ""

    def renderSimpleType(tpe: Type, asRef: Boolean): String = {
      assert(tpe.typeArgs.isEmpty || shouldIgnoreTypeArgs(tpe), s"$tpe")
      val prefix = if (asRef && isAllocType(tpe)) "&'a " else ""
      val suffix = renderLifetimeFor(tpe)
      val name = tpe.typeSymbol.name.toString
      s"$prefix$name$suffix"
    }

    def renderType(tpe: Type, asRef: Boolean): String = tpe match {
      case TypeRef(_, constr, args) if args.nonEmpty =>
        val argsStr = args.map(renderType(_, asRef)).mkString(", ")
        if (constr.name.toString.startsWith("Tuple")) {
          s"($argsStr)"
        } else {
          s"${constr.name}<${args.map(renderType(_, asRef)).mkString(", ")}>"
        }
      case _ =>
        renderSimpleType(tpe, asRef)
    }

    // Generate an enum grouping AST classes together
    def printAbstractClass(absClassType: Type, classes: ArrayBuffer[Class]) = {
      val absClassSymbol = absClassType.typeSymbol
      val simpleName = absClassSymbol.name.toString
      val name = renderSimpleType(absClassType, asRef=false)

      // Enum definition
      val variantStrs = classes.map { c =>
        s"${c.classSymbol.name}(${renderSimpleType(c.classSymbol.toType, asRef=true)})"
      }
      write(s"/// ${absClassSymbol.fullName}")
      write("#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]")
      write(s"pub enum $name {${variantStrs.mkString("\n  ", ",\n  ", "\n")}}\n")

      // Factory methods
      write(s"impl Factory {")
      for (clazz <- classes) {
        val simpleVariantName = clazz.classSymbol.name.toString
        val variantName = renderSimpleType(clazz.classSymbol.toType, asRef=false)
        val paramStrs = clazz.fields.map{ f => s"${f.name}: ${renderType(f.tpe, asRef=true)}" }
        write(s"  pub fn $simpleVariantName<'a>(&'a self, ${paramStrs.mkString(", ")}) -> &'a mut $variantName {")
        write(s"    self.bump.alloc($simpleVariantName {")
        for (f <- clazz.fields)
          write(s"      ${f.name},")
        write("    })")
        write("  }\n")
      }
      write("}\n")

      // Serializable trait implementation
      write(s"impl<'a> Serializable for $name {")
      write("  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {")
      write("    match self {")
      for (clazz <- classes) {
        val simpleVariantName = clazz.classSymbol.name.toString
        write(s"      $simpleName::$simpleVariantName(v) => v.serialize(s)?,")
      }
      write("    };")
      write("    Ok(())")
      write("  }")
      write("}\n")

      // From trait implementations
      for (clazz <- classes) {
        val variantName = renderSimpleType(clazz.classSymbol.toType, asRef=false)
        write(s"derive_conversions_for_ast!($name, $variantName);")
      }
      write("")
    }

    // Generate a concrete AST classes
    def printClasses(classes: ArrayBuffer[Class]) = {
      classes.foreach { c =>
        val classType = c.classSymbol.toType
        val name = renderSimpleType(classType, asRef=false)

        // Struct definition
        val fieldStrs = c.fields.map{ f => s"pub ${f.name}: ${renderType(f.tpe, asRef=true)}" }
        val derives =
          Seq("Clone", "Debug") ++ (
            if (c.customIdentity.isDefined) Seq()
            else (
              Seq("PartialEq", "Eq") ++ (if (c.needsHash) Seq("Hash") else Seq())
              )
            )
        write(s"/// ${c.classSymbol.fullName}")
        write(s"#[derive(${derives.mkString(", ")})]")
        write(s"pub struct $name {${fieldStrs.mkString("\n  ", ",\n  ", "\n")}}\n")

        // Eq, Ord and Hash trait implementations
        if (c.customIdentity.isDefined) {
          val path = c.customIdentity.get
          write(s"impl${renderLifetimeFor(classType)} PartialEq for $name {")
          write(s"  fn eq(&self, other: &Self) -> bool { self.$path == other.$path }")
          write("}")
          write(s"impl${renderLifetimeFor(classType)} Eq for $name {}")
          write(s"impl${renderLifetimeFor(classType)} PartialOrd for $name {")
          write(s"  fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }")
          write("}")
          write(s"impl${renderLifetimeFor(classType)} Ord for $name {")
          write(s"  fn cmp(&self, other: &Self) -> Ordering { self.$path.cmp(&other.$path) }")
          write("}")
          if (c.needsHash) {
            write(s"impl${renderLifetimeFor(classType)} Hash for $name {")
            write(s"  fn hash<H: Hasher>(&self, state: &mut H) { self.$path.hash(state); }")
            write("}\n")
          }
        }

        // Serializable trait implementation
        if (c.needsSerializable) {
          write(s"impl${renderLifetimeFor(classType)} Serializable for $name {")
          write("  fn serialize<S: Serializer>(&self, s: &mut S) -> SerializationResult {")
          write(s"    s.write_marker(MarkerId(${c.markerId}))?;")
          for (field <- c.fields)
            write(s"    self.${field.name}.serialize(s)?;")
          write(s"    Ok(())")
          write("  }")
          write("}\n")
        }
      }
    }

    def printCaption(caption: String) =
      write(s"\n// === $caption ===\n")

    write("// AUTO-GENERATED FROM STAINLESS")
    write("#![allow(non_snake_case)]")
    write("use super::Factory;")
    write("use crate::ser::types::*;")
    write("use crate::ser::{MarkerId, Serializable, SerializationResult, Serializer};")
    write("use std::cmp::Ordering;")
    write("use std::hash::{Hash, Hasher};")

    printCaption("Definitions")
    printAbstractClass(DefinitionT, definitionClasses)
    printClasses(definitionClasses)

    printCaption("Flags")
    printAbstractClass(FlagT, flagClasses)
    printClasses(flagClasses)

    printCaption("Expressions")
    printAbstractClass(ExprT, exprClasses)
    printClasses(exprClasses)

    printCaption("Types")
    printAbstractClass(TypeT, typeClasses)
    printClasses(typeClasses)

    optPatternT.foreach { PatternT =>
      printCaption("Patterns")
      printAbstractClass(PatternT, patternClasses)
      printClasses(patternClasses)
    }

    printCaption("Other")
    printClasses(otherClasses)

    writer.flush()
    writer.close()
  }
}

class RustInteropGenerator {
  protected val serializer: RustInteropGeneration =
    new utils.InoxSerializer(inox.trees) with RustInteropGeneration {}

  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      println(s"Usage: output-path")
      sys.exit(1)
    }
    serializer.generateRustInterop(new File(args(0)))
  }
}

object RustInteropGeneratorTool extends RustInteropGenerator {
  override protected val serializer: RustInteropGeneration =
    new XLangSerializer(stainless.extraction.xlang.trees) with RustInteropGeneration {
      override protected val optSymbolIdentifierT: Option[Type] =
        Some(typeOf[stainless.ast.SymbolIdentifier])
      override protected val optPatternT: Option[Type] =
        Some(typeOf[stainless.trees.Pattern])
    }
}
