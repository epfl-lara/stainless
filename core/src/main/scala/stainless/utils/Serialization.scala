/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package utils

import inox.utils._

import java.io.OutputStream

import scala.reflect._
import scala.reflect.runtime.universe._

class StainlessSerializer(override val trees: ast.Trees, serializeProducts: Boolean = false)
  extends InoxSerializer(trees, serializeProducts) {
  import trees._

  /** An extension to the set of registered classes in the `InoxSerializer`.
    * occur within Stainless programs.
    *
    * The new identifiers in the mapping range from 120 to 149.
    *
    * NEXT ID: 150
    */
  override protected def classSerializers: Map[Class[_], Serializer[_]] =
    super.classSerializers ++ Map(
      // Stainless ast Expressions
      classSerializer[NoTree]           (120),
      classSerializer[Error]            (121),
      classSerializer[Require]          (122),
      classSerializer[Annotated]        (123),
      classSerializer[Ensuring]         (124),
      classSerializer[Assert]           (125),
      classSerializer[MatchExpr]        (126),
      classSerializer[MatchCase]        (127),
      classSerializer[WildcardPattern]  (128),
      classSerializer[ADTPattern]       (129),
      classSerializer[TuplePattern]     (130),
      classSerializer[LiteralPattern[_]](131),
      classSerializer[UnapplyPattern]   (132),
      classSerializer[FiniteArray]      (133),
      classSerializer[LargeArray]       (134),
      classSerializer[ArraySelect]      (135),
      classSerializer[ArrayUpdated]     (136),
      classSerializer[ArrayLength]      (137),

      // Stainless ast Types
      classSerializer[ArrayType](138),

      // Stainless Flags
      classSerializer[Extern.type]     (139),
      classSerializer[Opaque.type]     (140),
      classSerializer[Unchecked.type]  (141),
      classSerializer[Derived]         (142),
      classSerializer[IsField]         (143),
      classSerializer[IsUnapply]       (144),

      mappingSerializer[SymbolIdentifier](145)
        (id => (id.globalId, id.id, id.symbol.path, id.symbol.id))
        (p => new SymbolIdentifier(new Identifier(p._3.last, p._1, p._2), new Symbol(p._3, p._4))),

      classSerializer[PartialEval.type](146),
      classSerializer[Ghost.type]      (147),
      classSerializer[Private.type]    (148),
      classSerializer[Final.type]      (149),
      classSerializer[Synthetic.type]  (182)
    )
}

class XLangSerializer(override val trees: extraction.xlang.Trees, serializeProducts: Boolean = false)
  extends StainlessSerializer(trees, serializeProducts) {
  import trees._

  /** An extension to the set of registered classes in the `StainlessSerializer`.
    * occur within Stainless programs.
    *
    * The new identifiers in the mapping range from 180 to 232.
    *
    * NEXT ID: 233
    */
  override protected def classSerializers: Map[Class[_], Serializer[_]] =
    super.classSerializers ++ Map(
      // Termination trees
      classSerializer[Decreases](180),

      // Inlining trees
      classSerializer[Inline.type]    (181),
      classSerializer[InlineOnce.type](228),

      // Inner-function trees
      classSerializer[LocalFunDef](183),
      classSerializer[LetRec]     (184),
      classSerializer[ApplyLetRec](185),
      classSerializer[Outer]      (186),
      classSerializer[Inner]      (187),

      // Imperative trees
      classSerializer[Block]          (188),
      classSerializer[LetVar]         (189),
      classSerializer[Assignment]     (190),
      classSerializer[FieldAssignment](191),
      classSerializer[While]          (192),
      classSerializer[ArrayUpdate]    (193),
      classSerializer[Old]            (194),
      classSerializer[BoolBitwiseAnd] (195),
      classSerializer[BoolBitwiseOr]  (196),
      classSerializer[BoolBitwiseXor] (197),
      classSerializer[IsVar.type]     (198),
      classSerializer[IsMutable.type] (199),
      classSerializer[IsPure.type]    (230),

      // Object-oriented trees
      classSerializer[ClassConstructor] (200),
      classSerializer[ClassSelector]    (201),
      classSerializer[IsInstanceOf]     (202),
      classSerializer[AsInstanceOf]     (203),
      classSerializer[ClassPattern]     (204),
      classSerializer[InstanceOfPattern](205),
      classSerializer[ClassType]        (206),
      classSerializer[AnyType]          (207),
      classSerializer[NothingType]      (208),
      // `UnionType` and `IntersectionType` are package-private to `oo`
      classSerializer[TypeBounds]       (209),
      // classSerializer[RefinementType]   (210), -> now in Inox
      classSerializer[ClassDef]         (222),
      classSerializer[IsInvariant.type] (223),
      classSerializer[IsAbstract.type]  (224),
      classSerializer[IsSealed.type]    (225),
      classSerializer[Bounds]           (226),
      classSerializer[Variance]         (227),
      classSerializer[IsCaseObject.type](229),

      // Throwing trees
      classSerializer[Throwing](211),
      classSerializer[Throw]   (212),
      classSerializer[Try]     (213),

      // Methods trees
      classSerializer[This]            (214),
      classSerializer[Super]           (215),
      classSerializer[MethodInvocation](216),
      classSerializer[IsMethodOf]      (217),
      classSerializer[IsAccessor]      (231),
      classSerializer[Snapshot]        (232),

      // XLang trees
      classSerializer[Ignore.type](218),
      classSerializer[Import]     (219),
      classSerializer[UnitDef]    (220),
      classSerializer[ModuleDef]  (221)
    )
}

object Serializer {
  def apply(t: ast.Trees, serializeProducts: Boolean = false): Serializer { val trees: t.type } =
    (t match {
      case xt: extraction.xlang.Trees => new XLangSerializer(xt)
      case _ => new StainlessSerializer(t)
    }).asInstanceOf[Serializer { val trees: t.type }]
}
