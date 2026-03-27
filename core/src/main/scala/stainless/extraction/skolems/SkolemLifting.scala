/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package skolems

class SkolemLifting(override val s: Trees, override val t: xlang.Trees)
                      (using override val context: inox.Context)
  extends oo.ExtractionPipeline
     with oo.NoSummaryPhase
     with IdentitySorts
     with SimplyCachedFunctions
     with oo.IdentityTypeDefs
     with oo.IdentityClasses { self =>
  override protected type TransformerContext = s.Symbols
  override protected def getContext(symbols: s.Symbols) = symbols

  import s._

  override protected type FunctionResult = Seq[t.FunDef]
  override protected def registerFunctions(symbols: t.Symbols, functions: Seq[Seq[t.FunDef]]): t.Symbols = symbols.withFunctions(functions.flatten)

  private var liftedSkolems: Map[Identifier, t.Expr] = Map.empty

  override def extractFunction(context: Symbols, fd: FunDef): (Seq[t.FunDef], Unit) = {
    import context.{given, _}

    var localSkolems: Map[Identifier, Set[Skolem]] = Map.empty
    var globalSkolems: Set[Skolem] = Set.empty

    // collects information about skolems
    class SkolemCollector(override val s: self.s.type, override val t: self.s.type)
      extends transformers.ConcreteTreeTransformer(s, t) {
      private var parents: List[Identifier] = Nil

      override def transform(fd: s.FunDef): t.FunDef = {
        fd.tparams.map(transform)
        fd.params.map(transform)
        transform(fd.returnType)

        parents = fd.id :: this.parents
        transform(fd.fullBody)
        parents = this.parents.tail

        fd
      }

      override def transform(e: s.Expr): t.Expr = e match {
        case sk @ s.Skolem(id, tpe) =>
          parents.headOption match {
            case Some(parent) =>
              localSkolems = localSkolems + (parent -> (localSkolems.getOrElse(parent, Set.empty) + sk))
            case None =>
              globalSkolems = globalSkolems + sk
          }
          super.transform(e)
        case _ =>
          super.transform(e)
      }
    }

    val collector = new SkolemCollector(self.s, self.s)
    collector.transform(fd)
    liftedSkolems ++= globalSkolems.map { case s.Skolem(id, tpe) => id -> t.FunctionInvocation(id, Seq.empty, Seq.empty) }

    class SkolemTransformer(override val s: self.s.type, override val t: self.t.type)
      extends transformers.ConcreteTreeTransformer(s, t) {

        override def transform(fd: s.FunDef): t.FunDef = {
          val newSkolems = 
            localSkolems
              .getOrElse(fd.id, Nil)
              .filterNot(s => liftedSkolems.contains(s.id))
              .map{ case s.Skolem(id, tpe) => t.ValDef(id, transform(tpe), Seq.empty) }
          liftedSkolems ++= newSkolems.map(vd => vd.id -> vd.toVariable)

          val transformed = super.transform(fd)

          transformed.copy( fullBody =
            newSkolems.foldRight(transformed.fullBody) { case (vd, acc) =>
              val choose = t.Choose(t.ValDef(FreshIdentifier("x", true), vd.tpe), t.BooleanLiteral(true))
              t.Let(vd, choose, acc).setPos(fd.getPos)
            }
          )
        }

        override def transform(e: s.Expr): t.Expr = e match {
          case s.Skolem(id, tpe) =>
            assert(liftedSkolems.contains(id), s"Skolem ${id} was not lifted")
            liftedSkolems(id).setPos(e.getPos)
          case _ =>
            super.transform(e)
      }
    }

    val transformer = new SkolemTransformer(self.s, self.t)

    val globalSkolemsLifted = globalSkolems.map { 
      case s.Skolem(id, tpe) =>
        val ttpe = transformer.transform(tpe)
        val choose = t.Choose(t.ValDef(FreshIdentifier("x", true), ttpe), t.BooleanLiteral(true))
        t.FunDef(id, Seq.empty, Seq.empty, ttpe, choose, Seq(t.Derived(Some(fd.id))))
    }.toList

    (transformer.transform(fd) :: globalSkolemsLifted, ())
  }
}

object SkolemLifting {
  def apply(ts: Trees, tt: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends SkolemLifting(s, t)
    new Impl(ts, tt)
  }
}
