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
          case s : SkolemDef =>
            skolemDefinitions += s
            super.transform(e)
          case _ =>
            super.transform(e)
        }
      }
    }

    val collector = new SkolemCollector(self.s, self.s)
    collector.transform(fd)

    val (skolemsWithFunOwner, skolemsWithClassOrModuleOwner) = 
      skolemDefinitions.partition(_.call.flags.exists {
        case Derived(Some(_)) => true
        case _ => false
      })

    val skolemMap = skolemsWithFunOwner.groupBy {
      _.call.flags.collectFirst {
        case Derived(Some(owner)) => owner
      }.get
    }.withDefaultValue(Nil)

    class SkolemTransformer(override val s: self.s.type, override val t: self.s.type)
      extends transformers.ConcreteTreeTransformer(s, t) {
        private def skolemFunctionForFun(id : Identifier): Seq[LocalFunDef] =
          skolemMap(id)
            .map { 
              case SkolemDef(SkolemCall(id, tpe, flags, _)) =>
                // we take the non-dependent type
                val newTpe = tpe.getType
                LocalFunDef(
                  id, Seq.empty, Seq.empty, newTpe, 
                  Choose(ValDef(FreshIdentifier("x", true), newTpe), BooleanLiteral(true)), List(IsPure)
                )
            }.toList

        override def transform(lfd: s.FunDef): t.FunDef = {
          val newSkolems = skolemFunctionForFun(lfd.id)
          val transformed = super.transform(lfd)

          if newSkolems.isEmpty then transformed
          else transformed.copy( fullBody = LetRec(newSkolems, transformed.fullBody))
        }

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
          case SkolemDef(call) => 
            val transformed = call.copy(tpe = transform(call.tpe), ownerTparams = call.ownerTparams.map(transform(_)))
            skolemCall(transformed)
          case call @ SkolemCall(_, tpe, _, ownerTparams) =>
            val transformed = call.copy(tpe = transform(tpe), ownerTparams = ownerTparams.map(transform(_)))
            Annotated(AsInstanceOf(skolemCall(transformed), transformed.tpe), Seq(DropVCs))
          case _ => super.transform(e)
        }
    }

    val transformer = new SkolemTransformer(self.s, self.s)
    (transformer.transform(fd) :: skolemsWithClassOrModuleOwner.map(skolemFunction).toList, ())
  }


  private def skolemFunction(skolem: SkolemDef)(using Symbols): FunDef = {
    val SkolemDef(SkolemCall(id, tpe, flags, _)) = skolem
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

  private def skolemCall(call: SkolemCall)(using s: Symbols): Expr = 
    call.flags.collectFirst {
      case IsMethodOf(ownerId) =>
        // owner is a class
        s.lookupClass(ownerId).map{ cdef => 
          MethodInvocation(
            This(cdef.typed(call.ownerTparams).toType),
            call.id,
            List.empty,
            List.empty
         )
        }
      case Derived(Some(_)) =>
        // owner is a function
        Some(ApplyLetRec(call.id, List.empty, FunctionType(List.empty, call.tpe), List.empty, List.empty))
    }.flatten.getOrElse {
      // owner is an object
      FunctionInvocation(call.id, List.empty, List.empty)
    }
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