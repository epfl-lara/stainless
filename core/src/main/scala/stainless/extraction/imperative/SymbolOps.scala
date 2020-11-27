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

  // Indicates whether types live in the heap or not
  lazy val livesInHeap = new utils.ConcurrentCached[Type, Boolean](_livesInHeap(_))

  // Indicates whether types touch heap (i.e. contain some data that lives in the heap)
  lazy val touchesHeap = new utils.ConcurrentCached[Type, Boolean](_touchesHeap(_))

  // Only the trait AnyHeapRef and its descendants live in the heap
  private def _livesInHeap(tpe: Type): Boolean = tpe match {
    case AnyHeapRef() => true
    // We lookup the parents through the cache so that the hierarchy is traversed at most once
    case ct: ClassType => ct.tcd.parents.exists(a => livesInHeap(a.toType))
    case _ => false
  }
  
  // We recurse on the content of the type to see if it contains references
  private def _touchesHeap(tpe: Type): Boolean = tpe match {
    // In the following cases tpe can be instantiated to anything so we are conservative
    // and assum that it can touch the heap
    case _: AnyType => true
    case _: TypeParameter => true
    case _: TypeBounds => true
    case ta: TypeApply if ta.isAbstract => true

    // A function doesn't live in the heap in our model
    case _: FunctionType => false

    // For classes and ADTs we have to recurse over the fields of the type
    case ct: ClassType =>
      ct.tcd.fields.exists { vd =>
        touchesHeap(vd.getType)
      }

    case adt: ADTType =>
      adt.getSort.constructors.exists { cons =>
        cons.fields.exists { vd =>
          touchesHeap(vd.getType)
        }
      }

    // For other types, we can just recurse on the structure of the type
    case NAryType(tps, _) =>
      tps.exists(touchesHeap(_))
  }
}

