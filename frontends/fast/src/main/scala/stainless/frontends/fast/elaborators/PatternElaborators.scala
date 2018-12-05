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

  class MatchCaseSeqE extends Elaborator [HSeq[MatchCase], (SimpleTypes.Type, Eventual[Seq[trees.MatchCase]])] {
    override def elaborate(template: HSeq[PatternMatchings.MatchCase])(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[Seq[trees.MatchCase]])] = {

      val constraints = template.elems.map(a => MatchCaseE.elaborate(a.right.get))
      val types = constraints.map(_.get.right.get)
      val constraint = for {
        type1 <- types
        type2 <- types
      } yield Constrained(Constraint.equal(type1._1._1, type2._1._1))
      val cons = Constrained.sequence(constraint ++ constraints)
      for {
        constraint <- cons
      } yield (types.head._1._1, Eventual.withUnifier { implicit unifier =>
        types.map(_._1._2.get)
      })
    }
  }

  val MatchCaseSeqE = new MatchCaseSeqE


  class PatternE extends Elaborator[Pattern, Eventual[trees.Pattern]] {
    override def elaborate(template: PatternMatchings.Pattern)(implicit store: Store): Constrained[Eventual[trees.Pattern]] = template match {
      case PatternMatchings.LiteralPattern(Some(binder), lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
          bind <- BindingE.elaborate(binder)
          _ <- Constrained(Constraint.equal(tpe, bind.tpe))
        } yield Eventual.withUnifier { implicit unifier =>
          trees.LiteralPattern(Some(bind.evValDef.get), value.get.asInstanceOf[trees.Literal[Any]])
        }
      case PatternMatchings.LiteralPattern(None, lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
        } yield Eventual.withUnifier { implicit unifier =>
          trees.LiteralPattern(None, value.get.asInstanceOf[trees.Literal[Any]])
        }
    }
  }

  val PatternE = new PatternE

}
