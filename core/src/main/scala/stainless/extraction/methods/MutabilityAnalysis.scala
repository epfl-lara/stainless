/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.language.existentials

/** Add `IsMutable` flag to classes that are mutable.
  *
  * Compute a fixpoint of all classes that are mutable by taking into account:
  * - setters
  * - getters to mutable types
  * - ancestors that are mutable
  * - descendants that are mutable
  * - classes that are already marked mutable
  */

trait MutabilityAnalysis extends oo.ExtractionPipeline
  with IdentityFunctions
  with IdentitySorts
  with oo.SimpleClasses
  { self =>


  /* ====================================
   *       Context and caches setup
   * ==================================== */

  val s: Trees
  val t: s.type
  import s._
  import s.exprOps._

  protected class TransformerContext(implicit symbols: Symbols) {

    // This function is used in the fixpoint below to gather ClassType's that
    // contain a getter whose return type is mutable.
    // For a given call to `isMutableType`, the set `mutableClasses` is fixed,
    // but may grow while computing the fixpoint below.
    private def isMutableType(tpe: Type, mutableClasses: Set[Identifier]): Boolean = {
      def rec(tpe: Type, seen: Set[Identifier]): Boolean = tpe match {
        case tp: TypeParameter => tp.flags contains IsMutable
        case arr: ArrayType => true
        case ClassType(cid, _) if mutableClasses(cid) => true
        case ClassType(cid, _) if seen(cid) => false
        // We don't need to check for mutable fields here, as at this point every
        // field still has a getter
        case ClassType(cid, tps) =>
          symbols.getClass(cid).methods.exists{ fid =>
            val fd = symbols.getFunction(fid)
            // note that setters and mutable flags are taken into account in the
            // initial state of the `mutableClasses` fixpoint
            fd.isGetter && rec(fd.returnType, seen + cid)
          }
        case _: FunctionType => false
        case NAryType(tps, _) => tps.exists(rec(_, seen))
      }

      rec(tpe, Set())
    }

    private val mutableClasses: Set[Identifier] = {
      val initialClasses = symbols.classes.values.filter { cd =>
        (cd.flags contains IsMutable) || // class is marked as mutable
        (cd.methods exists (fid => symbols.getFunction(fid).isSetter)) // class contains a setter
      }.map(_.id).toSet

      inox.utils.fixpoint[Set[Identifier]](mutableClasses =>
        mutableClasses ++
        symbols.classes.collect { case (id, cd) if isMutableType(cd.typed.toType, mutableClasses) => id } ++
        mutableClasses.flatMap { id =>
          val cd = symbols.getClass(id)
          cd.ancestors.map(_.id) ++ cd.descendants.map(_.id)
        }
      )(initialClasses)
    }


    def isMutable(id: Identifier) = mutableClasses(id)
    def isMutableType(tpe: Type): Boolean = isMutableType(tpe, mutableClasses)

    // Throw an exception if there is a class:
    // - which extends a non-sealed class not annotated with @mutable, or
    // - a class which extends a class without respecting non-mutability of the parent type parameters
    def checkMutability(): Unit = {
      for (
        cd <- symbols.classes.values if isMutable(cd.id);
        act <- cd.parents; acd <- act.lookupClass;
        if !acd.cd.flags.contains(IsMutable) && !acd.cd.isSealed
      ) {
        throw MethodsException(cd,
          s"A mutable class (${cd.id.asString}) cannot have a non-@mutable and non-sealed parent (${acd.cd.id.asString})."
        )
      }

      for (
        cd <- symbols.classes.values;
        act <- cd.parents;
        acd <- act.lookupClass;
        (tpe, tp) <- act.tps zip acd.cd.tparams
        if isMutableType(tpe) && !tp.flags.contains(IsMutable)
      ) {
        throw MethodsException(cd,
          s"Cannot extend non-mutable type parameter ${tp.asString} with mutable type ${tpe.asString}."
        )
      }
    }

    checkMutability()
  }

  override protected def getContext(symbols: Symbols) = new TransformerContext()(symbols)

  override protected final val classCache = new ExtractionCache[ClassDef, ClassResult](
    (cd, context) => ClassKey(cd) + ValueKey(context.isMutable(cd.id))
  )


  /* ====================================
   *         Extraction of classes
   * ==================================== */

  override protected def extractClass(context: TransformerContext, cd: ClassDef): ClassResult = {
    if (context.isMutable(cd.id))
      cd.copy(flags = (cd.flags :+ IsMutable).distinct).copiedFrom(cd)
    else
      cd
  }
}

object MutabilityAnalysis {
  def apply(tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = new MutabilityAnalysis {
    override val s: tt.type = tt
    override val t: tt.type = tt
    override val context = ctx
  }
}
