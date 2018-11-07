/* Copyright 2009-2018 EPFL, Lausanne */

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
    (ct.tcd +: ct.tcd.descendants).collectFirst {
      case tcd if tcd.fields.exists(_.id == id) => tcd
    }
  }

  def getClassField(ct: ClassType, id: Identifier): Option[ValDef] = {
    classForField(ct, id).flatMap(_.fields.find(_.id == id))
  }

  def isMutableType(tpe: Type): Boolean = {
    isMutableType(tpe, mutableClasses)
  }

  def isMutableClassType(ct: ClassType): Boolean = {
    isMutableClassType(ct, mutableClasses)
  }

  private[this] val mutableClasses = {
    val initialClasses = symbols.classes.values.filter { cd =>
      cd.fields.exists(_.flags contains IsVar)
    }.map(_.id).toSet

    inox.utils.fixpoint[Set[Identifier]] { mutableClasses =>
      mutableClasses ++
      symbols.classes.collect {
        case (id, cd) if isMutableClassType(cd.typed.toType, mutableClasses) => id
      } ++
      mutableClasses.flatMap { id =>
        val cd = symbols.getClass(id)
        cd.ancestors.map(_.id).toSet ++ cd.descendants.map(_.id).toSet
      }
    } (initialClasses)
  }

  private[this] def isMutableClassType(ct: ClassType, mutableClasses: Set[Identifier]): Boolean = {
    ct.tcd.fields.exists { vd =>
      vd.flags.contains(IsVar) || isMutableType(vd.getType, mutableClasses)
    }
  }

  private[this] def isMutableType(tpe: Type, mutableClasses: Set[Identifier]): Boolean = tpe match {
    case tp: TypeParameter => tp.flags contains IsMutable
    case arr: ArrayType => true
    case ft: FunctionType => false
    case ct: ClassType if mutableClasses contains ct.id => true
    case adt: ADTType => isMutableADTType(adt, mutableClasses)
    case NAryType(tps, _) => tps.exists(isMutableType(_, mutableClasses))
  }

  private[this] def isMutableADTType(adt: ADTType, mutableClasses: Set[Identifier]): Boolean = {
    adt.getSort.constructors.exists { cons =>
      cons.fields.exists { vd =>
        vd.flags.contains(IsVar) || isMutableType(vd.getType, mutableClasses)
      }
    }
  }
}

