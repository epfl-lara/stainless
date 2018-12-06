package stainless.frontends.fast.elaborators

trait PatternElaborators {
  self: stainless.frontends.fast.Elaborators =>

  import PatternMatchings._

  class MatchCaseE extends Elaborator[MatchCase, (SimpleTypes.Type, SimpleTypes.Type, Eventual[trees.MatchCase])] {
    override def elaborate(template: PatternMatchings.MatchCase)(implicit store: Store): Constrained[(SimpleTypes.Type, SimpleTypes.Type, Eventual[trees.MatchCase])] =
      for {
        (patternType, pattern) <- PatternE.elaborate(template.pattern)
        (optTpe, guard) <- OptExprE.elaborate {
          template.optGuard match {
            case None => Left(template.pos)
            case Some(expr) => Right(expr)
          }
        }
        _ <- Constrained(Constraint.equal(SimpleTypes.BooleanType(), optTpe))
        (tpe, ev) <- ExprE.elaborate(template.rhs)
      } yield (tpe, patternType, Eventual.withUnifier { implicit unifier =>
        trees.MatchCase(pattern.get, Some(guard.get), ev.get)
      })
  }

  val MatchCaseE = new MatchCaseE

  class MatchCaseSeqE extends Elaborator [HSeq[MatchCase], (SimpleTypes.Type, SimpleTypes.Type, Eventual[Seq[trees.MatchCase]])] {
    override def elaborate(template: HSeq[PatternMatchings.MatchCase])(implicit store: Store): Constrained[(SimpleTypes.Type, SimpleTypes.Type, Eventual[Seq[trees.MatchCase]])] = {
      val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
      val constraints = template.elems.map(a => MatchCaseE.elaborate(a.right.get))
      val constraintSequence = Constrained.sequence(constraints)

      for {
        (rhsTypes, patternTypes, eventuals) <- constraintSequence
          .checkImmediate(_.size == 1, template, xs => wrongNumberOfTypeArguments("Pattern matching", 1, xs.size))
          .map(_.unzip3)
        _ <- Constrained.sequence(patternTypes.map(a => Constrained(Constraint.equal(a, u))))
        _ <- Constrained.sequence(rhsTypes.sliding(2, 1).map(a => Constrained(Constraint.equal(a.head, a(1)))).toSeq)
      } yield (rhsTypes.head, u, Eventual.withUnifier { implicit unifier =>
        eventuals.map(_.get)
      })
    }
  }

  val MatchCaseSeqE = new MatchCaseSeqE


  class PatternE extends Elaborator[Pattern, (SimpleTypes.Type, Eventual[trees.Pattern])] {
    override def elaborate(template: PatternMatchings.Pattern)(implicit store: Store): Constrained[(SimpleTypes.Type, Eventual[trees.Pattern])] = template match {
      case PatternMatchings.LiteralPattern(Some(binder), lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
          bind <- BindingE.elaborate(binder)
          _ <- Constrained(Constraint.equal(tpe, bind.tpe))
        } yield {
          (tpe, Eventual.withUnifier { implicit unifier =>
            trees.LiteralPattern(Some(bind.evValDef.get), value.get.asInstanceOf[trees.Literal[Any]])
          })
        }
      case PatternMatchings.LiteralPattern(None, lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
        } yield (tpe, Eventual.withUnifier { implicit unifier =>
          trees.LiteralPattern(None, value.get.asInstanceOf[trees.Literal[Any]])
        })
      case PatternMatchings.TuplePattern(Some(binder), subPatterns) =>
        val constraints = subPatterns.map(PatternE.elaborate(_))
        val constraintSequence = Constrained.sequence(constraints)


        for {
          (types: Seq[SimpleTypes.Type], eventuals) <- constraintSequence.map(_.unzip)
          binding <- BindingE.elaborate(binder)
          _ <- Constrained(Constraint.equal(SimpleTypes.TupleType(types), binding.tpe))
        } yield (SimpleTypes.TupleType(types), Eventual.withUnifier { implicit unifier =>
          trees.TuplePattern(Some(binding.evValDef.get), eventuals.map(_.get))
        })
      case PatternMatchings.TuplePattern(None, subPatterns) =>
        val constraints = subPatterns.map(PatternE.elaborate(_))
        for {
          (types, eventuals) <- Constrained.sequence(constraints).map(_.unzip)
        } yield (SimpleTypes.TupleType(types), Eventual.withUnifier{implicit unifier =>
          trees.TuplePattern(None, eventuals.map(_.get))
        })
    }
  }

  val PatternE = new PatternE
}
