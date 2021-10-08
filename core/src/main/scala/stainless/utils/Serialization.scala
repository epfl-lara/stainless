/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package utils

import inox.utils._

import java.io.OutputStream

import scala.reflect._

import stainless.termination.{TerminationReport => TR}

class StainlessSerializer(override val trees: ast.Trees, serializeProducts: Boolean = false)
  extends InoxSerializer(trees, serializeProducts) {
  import trees._

  final inline def stainlessClassSerializer[T: ClassTag](inline id: Int): (Class[_], Serializer[T]) =
    classTag[T].runtimeClass -> stainlessClassSerializerMacro[T](this, id).asInstanceOf[Serializer[T]]

  /** An extension to the set of registered classes in the `InoxSerializer`.
    * occur within Stainless programs.
    *
    * The new identifiers in the mapping range from 120 to 172.
    *
    * NEXT ID: 173
    */
  override protected def classSerializers: Map[Class[_], Serializer[_]] =
    super.classSerializers ++ Map(
      stainlessClassSerializer[NoTree]             (120),
      stainlessClassSerializer[Error]              (121),
      stainlessClassSerializer[Require]            (122),
      stainlessClassSerializer[Annotated]          (123),
      stainlessClassSerializer[Ensuring]           (124),
      stainlessClassSerializer[Assert]             (125),
      stainlessClassSerializer[MatchExpr]          (126),
      stainlessClassSerializer[MatchCase]          (127),
      stainlessClassSerializer[WildcardPattern]    (128),
      stainlessClassSerializer[ADTPattern]         (129),
      stainlessClassSerializer[TuplePattern]       (130),
      stainlessClassSerializer[LiteralPattern[Any]](131),
      stainlessClassSerializer[UnapplyPattern]     (132),
      stainlessClassSerializer[FiniteArray]        (133),
      stainlessClassSerializer[LargeArray]         (134),
      stainlessClassSerializer[ArraySelect]        (135),
      stainlessClassSerializer[ArrayUpdated]       (136),
      stainlessClassSerializer[ArrayLength]        (137),
      stainlessClassSerializer[SizedADT]           (154),
      stainlessClassSerializer[Passes]             (158),

      stainlessClassSerializer[Max]                (160),

      // Stainless ast Types
      stainlessClassSerializer[ArrayType]    (138),
      stainlessClassSerializer[RecursiveType](152),
      stainlessClassSerializer[ValueType]    (153),
      stainlessClassSerializer[AnnotatedType](157),
      // Stainless Flags
      stainlessClassSerializer[Extern.type]      (139),
      stainlessClassSerializer[Opaque.type]      (140),
      stainlessClassSerializer[DropVCs.type]     (141),
      stainlessClassSerializer[Library.type]     (168),
      stainlessClassSerializer[Derived]          (142),
      stainlessClassSerializer[IsField]          (143),
      stainlessClassSerializer[IsUnapply]        (144),
      stainlessClassSerializer[ClassParamInit]   (170),
      stainlessClassSerializer[DropConjunct.type](171),
      stainlessClassSerializer[SplitVC.type]     (172),

      stainlessClassSerializer[TerminationStatus]      (161),
      stainlessClassSerializer[TR.Unknown.type]        (162),
      stainlessClassSerializer[TR.Terminating.type]    (163),
      stainlessClassSerializer[TR.NonTerminating.type] (164),

      mappingSerializer[SymbolIdentifier](145)
        (id => (id.globalId, id.id, id.symbol.path, id.symbol.id))
        (p => new SymbolIdentifier(new Identifier(p._3.last, p._1, p._2), new Symbol(p._3, p._4))),

      stainlessClassSerializer[PartialEval.type]    (146),
      stainlessClassSerializer[Law.type]            (150),
      stainlessClassSerializer[Ghost.type]          (147),
      stainlessClassSerializer[Private.type]        (148),
      stainlessClassSerializer[Final.type]          (149),
      stainlessClassSerializer[Decreases]           (151),
      stainlessClassSerializer[Erasable.type]       (155),
      stainlessClassSerializer[IndexedAt]           (156),
      stainlessClassSerializer[Wrapping.type]       (159),
      stainlessClassSerializer[Synthetic.type]      (165),
      stainlessClassSerializer[InlineInvariant.type](166),
      stainlessClassSerializer[Lazy.type]           (167),
      stainlessClassSerializer[Template.type]       (169),
    )
}

class XLangSerializer(override val trees: extraction.xlang.Trees, serializeProducts: Boolean = false)
  extends StainlessSerializer(trees, serializeProducts) {
  import trees._

  /** An extension to the set of registered classes in the `StainlessSerializer`.
    * occur within Stainless programs.
    *
    * The new identifiers in the mapping range from 180 to 260.
    *
    * NEXT ID: 261
    */
  override protected def classSerializers: Map[Class[_], Serializer[_]] =
    super.classSerializers ++ Map(
      // Termination trees
      stainlessClassSerializer[Decreases](180),

      // Induction trees
      stainlessClassSerializer[TraceInduct.type] (244),
      stainlessClassSerializer[Induct.type]      (258),

      // Inlining trees
      stainlessClassSerializer[Inline.type]    (181),
      stainlessClassSerializer[InlineOnce.type](228),

      // Inner-function trees
      stainlessClassSerializer[LocalFunDef](183),
      stainlessClassSerializer[LetRec]     (184),
      stainlessClassSerializer[ApplyLetRec](185),
      stainlessClassSerializer[Outer]      (186),
      stainlessClassSerializer[Inner]      (187),

      // Imperative trees
      stainlessClassSerializer[Block]                  (188),
      stainlessClassSerializer[LetVar]                 (189),
      stainlessClassSerializer[Assignment]             (190),
      stainlessClassSerializer[FieldAssignment]        (191),
      stainlessClassSerializer[While]                  (192),
      stainlessClassSerializer[ArrayUpdate]            (193),
      stainlessClassSerializer[Old]                    (194),
      stainlessClassSerializer[BoolBitwiseAnd]         (195),
      stainlessClassSerializer[BoolBitwiseOr]          (196),
      stainlessClassSerializer[BoolBitwiseXor]         (197),
      stainlessClassSerializer[IsVar.type]             (198),
      stainlessClassSerializer[IsMutable.type]         (199),
      stainlessClassSerializer[IsPure.type]            (230),
      stainlessClassSerializer[Snapshot]               (239),
      stainlessClassSerializer[MutableMapType]         (248),
      stainlessClassSerializer[MutableMapWithDefault]  (249),
      stainlessClassSerializer[MutableMapApply]        (250),
      stainlessClassSerializer[MutableMapUpdate]       (251),
      stainlessClassSerializer[MutableMapUpdated]      (252),
      stainlessClassSerializer[MutableMapDuplicate]    (253),
      stainlessClassSerializer[Swap]                   (259),
      stainlessClassSerializer[FreshCopy]              (260),
      stainlessClassSerializer[Reads]                  (182),
      stainlessClassSerializer[Modifies]               (210),

      // Object-oriented trees
      stainlessClassSerializer[ClassConstructor] (200),
      stainlessClassSerializer[ClassSelector]    (201),
      stainlessClassSerializer[IsInstanceOf]     (202),
      stainlessClassSerializer[AsInstanceOf]     (203),
      stainlessClassSerializer[ClassPattern]     (204),
      stainlessClassSerializer[InstanceOfPattern](205),
      stainlessClassSerializer[ClassType]        (206),
      stainlessClassSerializer[AnyType]          (207),
      stainlessClassSerializer[NothingType]      (208),
      // `UnionType` and `IntersectionType` are package-private to `oo`
      stainlessClassSerializer[TypeBounds]       (209),
      stainlessClassSerializer[ClassDef]         (222),
      stainlessClassSerializer[IsInvariant.type] (223),
      stainlessClassSerializer[IsAbstract.type]  (224),
      stainlessClassSerializer[IsSealed.type]    (225),
      stainlessClassSerializer[Bounds]           (226),
      stainlessClassSerializer[Variance]         (227),
      stainlessClassSerializer[IsCaseObject.type](229),
      stainlessClassSerializer[TypeSelect]       (237),
      stainlessClassSerializer[TypeApply]        (254),
      stainlessClassSerializer[TypeDef]          (255),
      stainlessClassSerializer[IsTypeMemberOf]   (246),

      // Inner classes trees
      stainlessClassSerializer[LetClass]             (232),
      stainlessClassSerializer[LocalClassDef]        (233),
      stainlessClassSerializer[LocalMethodDef]       (234),
      stainlessClassSerializer[LocalMethodInvocation](240),
      stainlessClassSerializer[LocalClassConstructor](235),
      stainlessClassSerializer[LocalClassSelector]   (241),
      stainlessClassSerializer[LocalClassType]       (236),
      stainlessClassSerializer[LocalThis]            (242),
      stainlessClassSerializer[LocalTypeDef]         (247),

      // Throwing trees
      stainlessClassSerializer[Throwing](211),
      stainlessClassSerializer[Throw]   (212),
      stainlessClassSerializer[Try]     (213),
      stainlessClassSerializer[Return]  (257),

      // Methods trees
      stainlessClassSerializer[This]            (214),
      stainlessClassSerializer[Super]           (215),
      stainlessClassSerializer[MethodInvocation](216),
      stainlessClassSerializer[IsMethodOf]      (217),
      stainlessClassSerializer[IsAccessor]      (231),
      stainlessClassSerializer[ValueClass.type] (243),

      // XLang trees
      stainlessClassSerializer[Ignore.type]     (218),
      stainlessClassSerializer[FieldDefPosition](245),
      stainlessClassSerializer[Import]          (219),
      stainlessClassSerializer[UnitDef]         (220),
      stainlessClassSerializer[ModuleDef]       (221),
      stainlessClassSerializer[UnknownType]     (238),
      stainlessClassSerializer[StrictBV.type]   (256),
    )
}

object Serializer {
  def apply(t: ast.Trees, serializeProducts: Boolean = false): Serializer { val trees: t.type } =
    (t match {
      case xt: extraction.xlang.Trees => new XLangSerializer(xt)
      case _ => new StainlessSerializer(t)
    }).asInstanceOf[Serializer { val trees: t.type }]
}
