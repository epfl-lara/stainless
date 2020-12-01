/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.transformers.{TransformerOp, TransformerWithExprOp, TransformerWithTypeOp}

trait SymbolOps extends oo.SymbolOps { self: TypeOps =>
  import trees._
  import symbols._

  override protected def transformerWithPC[P <: PathLike[P]](
    path: P,
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(implicit pp: PathProvider[P]): TransformerWithPC[P] = {
    new TransformerWithPC[P](path, exprOp, typeOp)
      with imperative.TransformerWithPC
      with TransformerWithExprOp
      with TransformerWithTypeOp
  }

  // TODO: Add cache
  def classForField(ct: ClassType, id: Identifier): Option[TypedClassDef] = {
    val related = (ct.tcd +: ct.tcd.ancestors).flatMap(tcd => tcd +: tcd.descendants).toSet
    related.collectFirst { case tcd if tcd.fields.exists(_.id == id) => tcd }
  }

  def getClassField(ct: ClassType, id: Identifier): Option[ValDef] = {
    classForField(ct, id).flatMap(_.fields.find(_.id == id))
  }

  def isMutableType(tpe: Type): Boolean = {
    isMutableType(tpe, mutableClasses, Set())
  }

  def isMutableClassType(ct: ClassType): Boolean = {
    isMutableClassType(ct, mutableClasses, Set())
  }

  @inline def mutableClasses: Set[Identifier] = _mutableClasses.get
  private[this] val _mutableClasses = inox.utils.Lazy({
    val initialClasses = symbols.classes.values.filter { cd =>
      cd.fields.exists(_.flags contains IsVar)
    }.map(_.id).toSet

    inox.utils.fixpoint[Set[Identifier]] { mutableClasses =>
      mutableClasses ++
      symbols.classes.collect {
        case (id, cd) if isMutableClassType(cd.typed.toType, mutableClasses, Set()) => id
      } ++
      mutableClasses.flatMap { id =>
        val cd = symbols.getClass(id)
        cd.ancestors.map(_.id).toSet ++ cd.descendants.map(_.id).toSet
      }
    } (initialClasses)
  })

  private[this] def isMutableClassType(ct: ClassType, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = {
    mutableClasses.contains(ct.id) || (!visited(ct.id) && ct.tcd.fields.exists { vd =>
      vd.flags.contains(IsVar) || isRealMutableType(vd.getType, mutableClasses, visited + ct.id)
    })
  }

  private[this] def isRealMutableType(tpe: Type, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = tpe match {
    case tp: TypeParameter => false
    case _ => isMutableType(tpe, mutableClasses, visited)
  }

  private[this] def isMutableType(tpe: Type, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = tpe match {
    case tp: TypeParameter => tp.flags contains IsMutable
    case TypeBounds(NothingType(), AnyType(), flags) => flags contains IsMutable
    case any: AnyType => true
    case arr: ArrayType => true
    case map: MutableMapType => true
    case ft: FunctionType => false
    case ct: ClassType => isMutableClassType(ct, mutableClasses, visited)
    case adt: ADTType => isMutableADTType(adt, mutableClasses, visited)
    case ta: TypeApply if ta.isAbstract => ta.getTypeDef.flags contains IsMutable
    case ta: TypeApply => isMutableType(ta.getType, mutableClasses, visited)
    case NAryType(tps, _) => tps.exists(isMutableType(_, mutableClasses, visited))
  }

  private[this] def isMutableADTType(adt: ADTType, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = {
    !visited(adt.id) &&
    adt.getSort.constructors.exists { cons =>
      cons.fields.exists { vd =>
        vd.flags.contains(IsVar) || isRealMutableType(vd.getType, mutableClasses, visited + adt.id)
      }
    }
  }

  // -----------------------------------------------------------------
  // Utilities for heap classes, for the full-imperative pipeline
  // -----------------------------------------------------------------

  // Indicates whether a type erases to a reference
  object erasesToRef {
    def apply(tpe: Type): Boolean = cache(tpe)

    lazy val cache = new utils.ConcurrentCached[Type, Boolean](erasesToRef(_))

    private def erasesToRef(tpe: Type): Boolean = tpe match {
      case AnyHeapRef() => true
      // We lookup the parents through the cache so that the hierarchy is traversed at most once
      case ct: ClassType => ct.tcd.parents.exists(a => cache(a.toType))
      case _ => false
    }
  }

  // Indicates whether a type is a heap type, that is, contains a reference
  object isHeapType {
    def apply(tpe: Type): Boolean = isHeapType(tpe, heapClasses, Set())

    @inline def heapClasses: Set[Identifier] = _heapClasses.get
    private[this] val _heapClasses = inox.utils.Lazy({
      val initialClasses = symbols.classes.values.filter { cd =>
        erasesToRef(cd.typed.toType)
      }.map(_.id).toSet

      inox.utils.fixpoint[Set[Identifier]] { heapClasses =>
        heapClasses ++
        symbols.classes.collect {
          case (id, cd) if isHeapClassType(cd.typed.toType, heapClasses, Set()) => id
        } ++
        heapClasses.flatMap { id =>
          symbols.getClass(id).ancestors.map(_.id).toSet
        }
      } (initialClasses)
    })

    private[this] def isHeapType(tpe: Type, heapClasses: Set[Identifier], visited: Set[Identifier]): Boolean = tpe match {
      // In those cases we have to be conservative and only assume a heap type when
      // the user says so through a flag
      case tp: TypeParameter => tp.flags contains IsMutable
      case TypeBounds(NothingType(), AnyType(), flags) => flags contains IsMutable
      case ta: TypeApply if ta.isAbstract => ta.getTypeDef.flags contains IsMutable
      case any: AnyType => true

      // For now arrays and maps are not supported by the full-imperative phase
      case arr: ArrayType => false
      case map: MutableMapType => false
      case ft: FunctionType => false // functions do not live in the heap

      // In those cases we have to recurse on the structure of the type
      case ct: ClassType => isHeapClassType(ct, heapClasses, visited)
      case adt: ADTType => isHeapADTType(adt, heapClasses, visited)
      case ta: TypeApply => isHeapType(ta.getType, heapClasses, visited)
      case NAryType(tps, _) => tps.exists(isHeapType(_, heapClasses, visited))
    }

    private[this] def isHeapClassType(ct: ClassType, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = {
      mutableClasses.contains(ct.id) || (!visited(ct.id) && ct.tcd.fields.exists { vd =>
        isHeapType(vd.getType, mutableClasses, visited + ct.id)
      })
    }

    private[this] def isHeapADTType(adt: ADTType, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = {
      !visited(adt.id) &&
      adt.getSort.constructors.exists { cons =>
        cons.fields.exists { vd =>
          isHeapType(vd.getType, mutableClasses, visited + adt.id)
        }
      }
    }
  }
}
