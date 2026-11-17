/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

/** Casts `this` to the self type of its class.
 *
 *  The frontend extracts a class `T` with a self type `S`, a subclass of `T`, with the [[SelfType]]`(S)`
 *  flag, and `this` within `T` as `This(S)`. For example,
 *
 * {{{
 * trait Exprs { self: Trees =>
 *   final def lit(v: BigInt): Expr = this.mk(v)
 * }
 * trait Trees extends Exprs {
 *   final def mk(v: BigInt): Expr = ...
 * }
 * }}}
 *
 *  The Scala compiler ensures that every concrete subclass of `T` is a subclass of `S`, so this phase
 *  replaces `This(S)` within the methods of `T` with a cast of `this` to `S`, under the assumption
 *  that it is an instance of `S`:
 *
 * {{{
 * trait Exprs {
 *   final def lit(v: BigInt): Expr = assume(this.isInstanceOf[Trees]); this.asInstanceOf[Trees].mk(v)
 * }
 * }}}
 *
 *  `This(S)` within a member class of `T` refers to the outer instance, which [[MemberClasses]] handles.
 */
class SelfTypes(override val s: Trees)(override val t: s.type)
               (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    val selfTypes: Map[Identifier, ClassType] = symbols.classes.values.flatMap { cd =>
      cd.flags.collectFirst { case SelfType(tpe) => cd.id -> tpe }
    }.toMap

    if (selfTypes.isEmpty) return (symbols, ExtractionSummary.NoSummary)

    class Transformer(cls: Identifier, selfType: ClassType) extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      override def transform(e: Expr): Expr = e match {
        case This(`selfType`) =>
          val thiss = This(ClassType(cls, symbols.getClass(cls).typeArgs)).copiedFrom(e)
          Assume(IsInstanceOf(thiss, selfType).copiedFrom(e), AsInstanceOf(thiss, selfType).copiedFrom(e)).copiedFrom(e)
        case _ => super.transform(e)
      }
    }

    def ownerClass(flags: Seq[Flag]): Option[Identifier] = flags.collectFirst {
      case IsMethodOf(id) => id
      case IsTypeMemberOf(id) => id
    }

    def transformer(flags: Seq[Flag]): Option[Transformer] =
      ownerClass(flags).flatMap(id => selfTypes.get(id).map(new Transformer(id, _)))

    val functions = symbols.functions.values.map(fd => transformer(fd.flags).fold(fd)(_.transform(fd)))
    val typeDefs = symbols.typeDefs.values.map(td => transformer(td.flags).fold(td)(_.transform(td)))

    val newSymbols = NoSymbols
      .withFunctions(functions.toSeq)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(symbols.classes.values.toSeq)
      .withTypeDefs(typeDefs.toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object SelfTypes {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends SelfTypes(s)(t)
    new Impl(trees, trees)
  }
}
