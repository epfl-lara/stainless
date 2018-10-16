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
    def isMutableType(tpe: Type, mutableClasses: Set[Identifier]): Boolean = {
      def rec(tpe: Type, seen: Set[ClassType]): Boolean = tpe match {
        case tp: TypeParameter => tp.flags contains IsMutable
        case arr: ArrayType => true
        case ct@ClassType(cid, tps) if mutableClasses(cid) => true
        case ct@ClassType(cid, tps) if seen(ct) => false
        case ct@ClassType(cid, tps) =>
          symbols.getClass(cid).methods.exists{ fid =>
            val fd = symbols.functions(fid)
            fd.isGetter && rec(fd.returnType, seen + ct)
          }
        case _: FunctionType => false
        case NAryType(tps, _) => tps.exists(rec(_, seen))
      }

      rec(tpe, Set())
    }

    val classes = symbols.classes.values.toSet
    val markedClasses = classes.filter(_.flags.contains(IsMutable))
    val classesWithSetters = classes.filter(_.methods.exists(fid => symbols.functions(fid).isSetter))

    val mutableClasses = inox.utils.fixpoint[Set[ClassDef]](mutableClasses =>
      mutableClasses.flatMap(cd => cd.ancestors.map(_.cd) ++ cd.descendants) ++
      classes.filter(cd => isMutableType(cd.typed.toType, mutableClasses.map(_.id))) ++
      mutableClasses
    )(markedClasses ++ classesWithSetters)

    def isMutable(cd: ClassDef) = mutableClasses(cd)
  }

  override protected def getContext(symbols: Symbols) = new TransformerContext()(symbols)

  override protected final val classCache = new ExtractionCache[ClassDef, ClassResult](
    (cd, context) => ClassKey(cd) + ValueKey(context.isMutable(cd))
  )


  /* ====================================
   *         Extraction of classes
   * ==================================== */

  override protected def extractClass(context: TransformerContext, cd: ClassDef): ClassResult = {
    if (context.isMutable(cd))
      cd.copy(flags = cd.flags.filterNot(_ == IsMutable) :+ IsMutable).copiedFrom(cd)
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
