package stainless.frontends.fast.elaborators

trait PatternElaborators {
  self: stainless.frontends.fast.Elaborators =>

  import PatternMatchings._

  class MatchCaseE extends Elaborator[MatchCase, (SimpleTypes.Type, Eventual[trees.MatchCase])] {
    override def elaborate(template: PatternMatchings.MatchCase)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.MatchCase])] =
      for {
        pattern <- PatternE.elaborate(template.pattern)
        (optTpe, guard) <- OptExprE.elaborate {
          template.optGuard match {
            case None => Left(template.pos)
            case Some(expr) => Right(expr)
          }
        }
        _ <- Constrained(Constraint.equal(SimpleTypes.BooleanType(), optTpe))
        (tpe, ev) <- ExprE.elaborate(template.rhs)
      } yield (tpe, Eventual.withUnifier { implicit unifier =>
        trees.MatchCase(pattern.get, Some(guard.get), ev.get)
      })
  }

  val MatchCaseE = new MatchCaseE

  class MatchCaseSeqE extends HSeqE[MatchCase, trees.MatchCase, (SimpleTypes.Type, Eventual[trees.MatchCase])]("MatchCase") {
    override val elaborator = MatchCaseE
    override def wrap(expr: trees.MatchCase, where: IR)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.MatchCase])] =
      Constrained.attempt(SimpleTypes.fromInox(expr.getType(store.getSymbols)).map { st =>
        (st.setPos(where.pos), Eventual.pure(expr))
      }, where, invalidInoxExpr(expr))
  }
  val ExprSeqE = new ExprSeqE

  val MatchCaseSeqE = new MatchCaseSeqE


  class PatternE extends Elaborator[Pattern, Eventual[trees.Pattern]] {
    override def elaborate(template: PatternMatchings.Pattern)(implicit store: Store): Constrained[Eventual[trees.Pattern]] = template match {
      case PatternMatchings.LiteralPattern(Some(binder), lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
          bind <- BindingE.elaborate(binder)
          _ <- Constrained(Constraint.equal(tpe, bind.tpe))
        } yield Eventual.withUnifier { implicit unifier =>
          trees.LiteralPattern(Some(bind.evValDef.get), value.get.asInstanceOf[trees.Literal])
        }
      case PatternMatchings.LiteralPattern(None, lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
        } yield Eventual.withUnifier { implicit unifier =>
          trees.LiteralPattern(None, value.get.asInstanceOf[trees.Literal])
        }
    }
  }

  val PatternE = new PatternE

}
