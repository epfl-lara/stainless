/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

trait TypeOps extends oo.TypeOps { self =>
  protected val trees: Trees
  import trees._
  import symbols.{given, _}

  override def unapplyAccessorResultType(id: Identifier, inType: Type): Option[Type] =
    lookupFunction(id)
      .filter(_.flags exists { case IsMethodOf(_) => true case _ => false })
      .filter(_.params.isEmpty)
      .flatMap { fd =>
        lookupClass(fd.flags.collectFirst { case IsMethodOf(id) => id }.get).flatMap { cd =>
          instantiation(ClassType(cd.id, cd.tparams.map(_.tp)), inType)
            .filter(tpMap => cd.tparams forall (tpd => tpMap contains tpd.tp))
            .map(tpMap => typeOps.instantiateType(fd.returnType, tpMap))
        }
      }.orElse(super.unapplyAccessorResultType(id, inType))

  def firstSuperMethod(id: SymbolIdentifier): Option[SymbolIdentifier] = {
    def rec(cd: ClassDef): Option[SymbolIdentifier] = {
      cd.methods.find(_.symbol == id.symbol)
        .orElse(cd.parents.headOption.flatMap(ct => rec(symbols.getClass(ct.id))))
    }

    getFunction(id).flags
      .collectFirst { case IsMethodOf(id) => symbols.getClass(id) }
      .flatMap(cd => cd.parents.headOption.map(ct => symbols.getClass(ct.id)))
      .flatMap(rec(_))
  }

  def firstSuperTypeMember(id: SymbolIdentifier): Option[SymbolIdentifier] = {
    def rec(cd: ClassDef): Option[SymbolIdentifier] = {
      cd.typeMembers.find(_.symbol == id.symbol)
        .orElse(cd.parents.headOption.flatMap(ct => rec(symbols.getClass(ct.id))))
    }

    getTypeDef(id).flags
      .collectFirst { case IsTypeMemberOf(id) => symbols.getClass(id) }
      .flatMap(cd => cd.parents.headOption.map(ct => symbols.getClass(ct.id)))
      .flatMap(rec(_))
  }
}
