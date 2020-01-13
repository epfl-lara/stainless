/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package methods

import inox.utils.Position

/** Merge all invariants of a class into a single method */
trait MergeInvariants
  extends oo.CachingPhase
    with IdentitySorts
    with SimpleFunctions
    with oo.IdentityTypeDefs { self =>

  val s: Trees
  val t: Trees

  override protected type ClassResult    = (t.ClassDef, Option[t.FunDef])

  override protected val classCache = new ExtractionCache[s.ClassDef, ClassResult]({ (cd, ctx) =>
    import ctx.symbols
    val invariants = symbols.functions.values.filter { fd =>
      (fd.flags contains s.IsInvariant) &&
      (fd.flags exists { case s.IsMethodOf(id) => id == cd.id case _ => false })
    }.map(FunctionKey(_)).toSet

    ClassKey(cd) + SetKey(invariants)
  })

  override protected final val funCache = new ExtractionCache[s.FunDef, FunctionResult]({ (fd, ctx) =>
    import ctx.symbols
    FunctionKey(fd)
  })

  override protected def getContext(symbols: s.Symbols) = new TransformerContext()(symbols)

  protected class TransformerContext(implicit val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    import s._
    import symbols._

    val toMerge = symbols.classes.values.flatMap { cd =>
      val invs = cd.flags.collect { case HasADTInvariant(id) => id }
      Option(invs).filter(_.length >= 2).map(fds => cd.id -> fds)
    }.toMap

    val mergedInvariant = toMerge.map { case (cid, invs) =>
      val cd = symbols.getClass(cid)
      val vd = ValDef.fresh("thiss", cd.typed.toType)

      val inv = new FunDef(
        FreshIdentifier("inv"),
        Seq.empty,
        Seq(vd.copiedFrom(cd)),
        BooleanType().copiedFrom(cd),
        s.andJoin(invs.map(symbols.getFunction).map { inv =>
          inv.typed.applied(Seq(vd.toVariable.copiedFrom(cd))).copiedFrom(cd)
        }),
        Seq.empty,
      ).copiedFrom(cd)

      cd.id -> transform(inv)
    }.toMap

    override def transform(cd: ClassDef): t.ClassDef = {
      if (mergedInvariant.contains(cd.id)) {
        val newFlags = Seq(HasADTInvariant(mergedInvariant(cd.id).id)) ++ cd.flags.filter {
          case HasADTInvariant(_) => false
          case _ => true
        }
        super.transform(cd.copy(flags = newFlags))
      } else {
        super.transform(cd)
      }
    }
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (t.ClassDef, Option[t.FunDef]) = {
    (context.transform(cd), context.mergedInvariant.get(cd.id))
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    context.transform(fd)
  }

  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[t.FunDef]): t.Symbols =
    symbols.withFunctions(functions)

  override protected def registerClasses(symbols: t.Symbols, classes: Seq[(t.ClassDef, Option[t.FunDef])]): t.Symbols = {
    val (cls, invs) = classes.unzip
    symbols.withClasses(cls).withFunctions(invs.flatten)
  }
}

object MergeInvariants {
  def apply(ts: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: ts.type
  } = new MergeInvariants {
    override val s: ts.type = ts
    override val t: ts.type = ts
    override val context = ctx
  }
}

