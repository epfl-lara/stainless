/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.transformers.{TransformerOp, TransformerWithExprOp, TransformerWithTypeOp}

trait SymbolOps extends TypeOps with oo.SymbolOps { self =>
  import trees._
  import symbols.{given, _}

  override protected def transformerWithPC[P <: PathLike[P]](
    path: P,
    theExprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    theTypeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(using PathProvider[P]): StainlessTransformerWithPC[P] = {
    class Impl(override val s: self.trees.type,
               override val t: self.trees.type,
               override val symbols: self.symbols.type)
              (using override val pp: PathProvider[P])
      extends StainlessTransformerWithPC[P](s, t, symbols)
         with imperative.TransformerWithPC
         with TransformerWithExprOp
         with TransformerWithTypeOp {
      override protected def exprOp(expr: s.Expr, env: Env, op: TransformerOp[s.Expr, Env, t.Expr]): t.Expr = {
        theExprOp(expr, env, op)
      }

      override protected def typeOp(ty: s.Type, env: Env, op: TransformerOp[s.Type, Env, t.Type]): t.Type = {
        theTypeOp(ty, env, op)
      }
    }

    new Impl(self.trees, self.trees, self.symbols)
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

    def freeClassDefType(cd: ClassDef): ClassType =
      cd.typed(cd.tparams.map { tparam =>
        tparam.tp.freshen match {
          case t @ TypeParameter(id, flags) =>
            TypeParameter(id, flags.filterNot(_ == IsMutable)).copiedFrom(t)
        }
      }).toType

    inox.utils.fixpoint[Set[Identifier]] { mutableClasses =>
      mutableClasses ++
      symbols.classes.collect {
        case (id, cd) if isMutableClassType(freeClassDefType(cd), mutableClasses, Set()) => id
      } ++
      mutableClasses.flatMap { id =>
        val cd = symbols.getClass(id)
        cd.ancestors.map(_.id).toSet ++ cd.descendants.map(_.id).toSet
      }
    } (initialClasses)
  })

  private[this] def isMutableClassType(ct: ClassType, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = {
    mutableClasses.contains(ct.id) || (!visited(ct.id) && ct.tcd.fields.exists { vd =>
      vd.flags.contains(IsVar) || isMutableType(vd.getType, mutableClasses, visited + ct.id)
    })
  }

  private[this] def isMutableType(tpe: Type, mutableClasses: Set[Identifier], visited: Set[Identifier]): Boolean = tpe match {
    case _ if tpe == Untyped => true
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
        vd.flags.contains(IsVar) || isMutableType(vd.getType, mutableClasses, visited + adt.id)
      }
    }
  }
}

