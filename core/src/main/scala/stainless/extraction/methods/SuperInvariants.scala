/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package methods

import stainless.ast.{Symbol, SymbolIdentifier}
import stainless.ast.SymbolIdentifier.IdentifierOps

/** Ensures invariants of ancestors are enforced by
 *  conjoining call to parent invariant in each invariant.
 */
trait SuperInvariants
  extends oo.CachingPhase
    with IdentitySorts
    with SimpleFunctions
    with oo.IdentityTypeDefs
    with oo.IdentityClasses { self =>

  val s: Trees
  val t: Trees

  override protected final val funCache = new ExtractionCache({ (fd, context) =>
    FunctionKey(fd) + SetKey(context.ancestorsInvariants(fd).map(FunctionKey(_)))
  })

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    import s._
    import symbols._

    def ancestorsInvariants(fd: s.FunDef): Set[s.FunDef] = {
      fd.getClassDef.map { cd =>
        cd.ancestors.flatMap(_.cd.methods).map(symbols.getFunction).filter(_.isInvariant).toSet
      }.getOrElse(Set.empty)
    }

    override def transform(e: s.Expr): t.Expr = e match {
      case _ => super.transform(e)
    }

    override def transform(fd: s.FunDef): t.FunDef = {
      if (!fd.isMethod || !fd.isInvariant) {
        super.transform(fd)
      } else {
        val nfd = superInvariantCall(fd).map { call =>
          fd.copy(fullBody = s.And(call, fd.fullBody).copiedFrom(fd.fullBody))
        }.getOrElse(fd)

        super.transform(nfd)
      }
    }

    private def getSuperInvariant(tcd: s.TypedClassDef, inv: s.FunDef): Option[(s.TypedClassDef, s.FunDef)] = {
      val sym = inv.id.unsafeToSymbolIdentifier.symbol
      val superInv = tcd.cd.methods
        .find(_.symbol == sym)
        .map(fd => tcd -> symbols.getFunction(fd))

      superInv orElse {
        tcd.parents.headOption.flatMap(getSuperInvariant(_, inv))
      }
    }

    private def superInvariantCall(inv: s.FunDef): Option[s.Expr] = {
      require(inv.isMethod && inv.isInvariant)

      for {
        cd <- inv.getClassDef
        parent <- cd.ancestors.headOption
        (superClass, superInv) <- getSuperInvariant(parent, inv)
      } yield {
        s.MethodInvocation(
          s.Super(superClass.toType).copiedFrom(inv.fullBody),
          superInv.id,
          superInv.typeArgs,
          Seq.empty
        ).copiedFrom(inv.fullBody)
      }
    }
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    context.transform(fd)
  }
}

object SuperInvariants {
  def apply(ts: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: ts.type
  } = new SuperInvariants {
    override val s: ts.type = ts
    override val t: ts.type = ts
    override val context = ctx
  }
}

