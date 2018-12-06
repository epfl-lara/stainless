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
        (rhsTypes: Seq[SimpleTypes.Type], patternTypes: Seq[SimpleTypes.Type], eventuals: Seq[Eventual[trees.MatchCase]]) <- constraintSequence.map(a => a.unzip3)
        _ <- Constrained.sequence(patternTypes.map(a => Constrained(Constraint.equal(a, u))))
        _ <- Constrained.sequence(rhsTypes.sliding(2, 1).map(a => Constrained(Constraint.equal(a.head, a(1)))).toSeq)
      } yield (rhsTypes.head, u, Eventual.withUnifier { implicit unifier =>
        eventuals.map(_.get)
      })

//      val types = constraints.map(_.get.right.get)
//      val patternTypingConstraints = types.map(a => Constrained(Constraint.equal(a._1._2, u)))
//
//      val constraint = (for {
//        Seq(first, second) <- types.sliding(2, 1)
//      } yield Constrained(Constraint.equal(first._1._1, second._1._1))).toSeq
//
//      val cons = Constrained.sequence(constraint ++ constraints ++ patternTypingConstraints)
//
//      for {
//        constraint <- cons
//      } yield (types.head._1._1, u, Eventual.withUnifier { implicit unifier =>
//        types.map(_._1._3.get)
//      })
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
        val types: Seq[SimpleTypes.Type] = constraints.map(_.get.right.get._1._1)
        val eventuals:Seq[Eventual[trees.Pattern]] = constraints.map(_.get.right.get._1._2)
        for {
          bind <- BindingE.elaborate(binder)
          _ <- Constrained.sequence(constraints)
          _ <- Constrained(Constraint.equal(SimpleTypes.TupleType(types), bind.tpe))
        } yield (SimpleTypes.TupleType(types), Eventual.withUnifier{implicit unifier =>
          trees.TuplePattern(Some(bind.evValDef.get), eventuals.map(_.get))
        })
      case PatternMatchings.TuplePattern(None, subPatterns) =>
        val constraints = subPatterns.map(PatternE.elaborate(_))
        val types: Seq[SimpleTypes.Type] = constraints.map(_.get.right.get._1._1)
        val eventuals: Seq[Eventual[trees.Pattern]] = constraints.map(_.get.right.get._1._2)
        for {
          _ <- Constrained.sequence(constraints)
        } yield (SimpleTypes.TupleType(types), Eventual.withUnifier{implicit unifier =>
          trees.TuplePattern(None, eventuals.map(_.get))
        })
    }
  }

  val PatternE = new PatternE

}
