package stainless
package extraction
package xlang
import scala.collection.mutable

class SkolemLifting(override val s: Trees)(override val t: s.type)
                      (using override val context: inox.Context)
  extends oo.ExtractionPipeline
     with oo.NoSummaryPhase
     with IdentitySorts
     with SimplyCachedFunctions
     with oo.IdentityTypeDefs
     with oo.IdentityClasses { self =>
  import s._

  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  override protected type FunctionResult = Seq[FunDef]
  override protected def registerFunctions(symbols: Symbols, functions: Seq[Seq[FunDef]]): Symbols = symbols.withFunctions(functions.flatten)

  override def extractFunction(context: TransformerContext, fd: FunDef): (Seq[FunDef], Unit) = {
    import context.{given, _}

    val skolemDefinitions = mutable.ListBuffer.empty[SkolemDef]

    class SkolemCollector(override val s: self.s.type, override val t: self.s.type)
      extends transformers.ConcreteTreeTransformer(s, t) {

      override def transform(e: s.Expr): t.Expr = {
        e match {
          case s @ SkolemDef(id, _, flags) =>
            skolemDefinitions += s
            super.transform(e)
          case _ =>
            super.transform(e)
        }
      }
    }

    val collector = new SkolemCollector(self.s, self.s)
    collector.transform(fd)

    val skolemMap = skolemDefinitions.groupBy {
      _.flags.collectFirst {
        case IsMethodOf(owner) => owner
        case Derived(Some(owner)) => owner
      }
    }.withDefaultValue(Nil)

    class SkolemTransformer(override val s: self.s.type, override val t: self.s.type)
      extends transformers.ConcreteTreeTransformer(s, t) {
        private def skolemFunctionForFun(id : Identifier): Seq[LocalFunDef] =
          skolemMap(Some(id))
            .map { 
              case SkolemDef(id, tpe, flags) =>
                // we take the non-dependent type
                val newTpe = tpe.getType
                LocalFunDef(
                  id, Seq.empty, Seq.empty, newTpe, 
                  Choose(ValDef(FreshIdentifier("x", true), newTpe), BooleanLiteral(true)), List(IsPure)
                )
            }.toList

        def transform(lfd: s.LocalFunDef): t.LocalFunDef = {
          val newSkolems = skolemFunctionForFun(fd.id)
          val transformed = new t.LocalFunDef(
            lfd.id,
            lfd.tparams.map(transform(_)),
            lfd.params.map(transform(_)),
            transform(lfd.returnType),
            transform(lfd.fullBody),
            lfd.flags.map(transform(_))
          ).setPos(lfd)

          if newSkolems.isEmpty then transformed
          else transformed.copy( fullBody = LetRec(newSkolems, transformed.fullBody))
        }

        override def transform(e: s.Expr): t.Expr = e match {
          case SkolemDef(id, tpe, _) => skolemCall(id)
          case SkolemCall(id, tpe) =>
            val transformedTpe = transform(tpe)
            Annotated(AsInstanceOf(skolemCall(id), transformedTpe), Seq(DropVCs))
          case _ => super.transform(e)
        }
    }

    val transformer = new SkolemTransformer(self.s, self.s)
    (transformer.transform(fd) :: skolemMap(None).map(skolemFunction).toList, ())
  }


  private def skolemFunction(skolem: SkolemDef)(using Symbols): FunDef = {
    val SkolemDef(id, tpe, flags) = skolem
    val newTpe = tpe.getType
    FunDef(
      id,
      Seq.empty,
      Seq.empty,
      newTpe,
      Choose(ValDef(FreshIdentifier("x", true), newTpe), BooleanLiteral(true)),
      flags
    )
  }

  private def skolemCall(call: SkolemCall): Expr = 
    val isMethod = call.collectFirst {
      case IsMethodOf(ownerId) => 
        MethodInvocation(ownerId ,call.id, List.empty, List.empty)
      case _ => false
    }
    if isMethod then MethodInvocation(call.id, List.empty, List.empty)
    else FunctionInvocation(call.id, List.empty, List.empty)
}

object SkolemLifting {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends SkolemLifting(s)(t)
    new Impl(trees, trees)
  }
}