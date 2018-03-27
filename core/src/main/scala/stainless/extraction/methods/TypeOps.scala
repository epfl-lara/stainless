/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

trait TypeOps extends oo.TypeOps { self =>
  protected val trees: Trees
  import trees._
  import symbols._

  override protected def unapplyAccessorResultType(id: Identifier, inType: Type): Option[Type] =
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
}
