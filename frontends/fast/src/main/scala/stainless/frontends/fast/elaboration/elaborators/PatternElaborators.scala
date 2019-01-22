package stainless.frontends.fast.elaboration.elaborators

trait PatternElaborators {
  self: stainless.frontends.fast.Elaborators =>

  import PatternMatchings._

  class MatchCaseE extends Elaborator[MatchCase, (SimpleTypes.Type, SimpleTypes.Type, Eventual[trees.MatchCase])] {
    override def elaborate(template: PatternMatchings.MatchCase)(implicit store: Store): Constrained[(SimpleTypes.Type, SimpleTypes.Type, Eventual[trees.MatchCase])] =
      for {
        (patternType, bindings, pattern) <- PatternE.elaborate(template.pattern)
        (optTpe, guard) <- OptGuardExprE.elaborate {
          template.optGuard match {
            case None => Left(template.pos)
            case Some(expr) => Right(expr)
          }
        }(store.addBindings(bindings))
        _ <- Constrained(Constraint.equal(SimpleTypes.BooleanType(), optTpe))
        (tpe, ev) <- ExprE.elaborate(template.rhs)(store.addBindings(bindings))
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
          .checkImmediate(_.nonEmpty, template, xs => wrongNumberOfTypeArguments("Pattern matching", 1, xs.size))
          .map(_.unzip3)
        _ <- Constrained.sequence(patternTypes.map(a => Constrained(Constraint.equal(a, u))))
        _ <- Constrained.sequence(rhsTypes.sliding(2, 1).map({
          case Seq(a, b) => Constrained(Constraint.equal(a, b))
          case Seq(a) => Constrained(Constraint.equal(a, a))
        }).toSeq)
      } yield (rhsTypes.head, u, Eventual.withUnifier { implicit unifier =>
        eventuals.map(_.get)
      })
    }
  }

  val MatchCaseSeqE = new MatchCaseSeqE


  class PatternE extends Elaborator[Pattern, (SimpleTypes.Type, Seq[SimpleBindings.Binding], Eventual[trees.Pattern])] {
    override def elaborate(template: PatternMatchings.Pattern)(implicit store: Store): Constrained[(SimpleTypes.Type, Seq[SimpleBindings.Binding], Eventual[trees.Pattern])] = template match {
      case PatternMatchings.LiteralPattern(Some(binder), lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
          bind <- BindingE.elaborate(binder)
          _ <- Constrained(Constraint.equal(tpe, bind.tpe))
        } yield {
          (tpe, Seq(bind), Eventual.withUnifier { implicit unifier =>
            trees.LiteralPattern(Some(bind.evValDef.get), value.get.asInstanceOf[trees.Literal[Any]])
          })
        }
      case PatternMatchings.LiteralPattern(None, lit) =>
        for {
          (tpe, value) <- ExprE.elaborate(lit)
        } yield (tpe, Seq(), Eventual.withUnifier { implicit unifier =>
          trees.LiteralPattern(None, value.get.asInstanceOf[trees.Literal[Any]])
        })
      case PatternMatchings.TuplePattern(Some(binder), subPatterns) =>
        val constraints = subPatterns.map(PatternE.elaborate(_))
        val constraintSequence = Constrained.sequence(constraints)

        for {
          (types, bindings, eventuals) <- constraintSequence.map(_.unzip3)
          binding <- BindingE.elaborate(binder)
          _ <- Constrained(Constraint.equal(SimpleTypes.TupleType(types), binding.tpe))
        } yield (SimpleTypes.TupleType(types), bindings.flatten :+ binding, Eventual.withUnifier { implicit unifier =>
          trees.TuplePattern(Some(binding.evValDef.get), eventuals.map(_.get))
        })
      case PatternMatchings.TuplePattern(None, subPatterns) =>
        val constraints = subPatterns.map(PatternE.elaborate(_))
        for {
          (types, bindings, eventuals) <- Constrained.sequence(constraints).map(_.unzip3)
        } yield (SimpleTypes.TupleType(types), bindings.flatten, Eventual.withUnifier{implicit unifier =>
          trees.TuplePattern(None, eventuals.map(_.get))
        })
      case PatternMatchings.WildcardPattern(Some(binder)) =>
        for {
          binding <- BindingE.elaborate(binder)
        } yield (binding.tpe, Seq(binding), Eventual.withUnifier { implicit unifier =>
          trees.WildcardPattern(Some(binding.evValDef.get))
        })

      case PatternMatchings.WildcardPattern(None) =>
        val u = SimpleTypes.Unknown.fresh.setPos(template.pos)
        for {
          _ <- Constrained(Constraint.exist(u))
        } yield (u, Seq(), Eventual.withUnifier { implicit unifier =>
          trees.WildcardPattern(None)
        })

      case PatternMatchings.InstanceOf(Some(binder), tpe) =>
        for {
          binder <- BindingE.elaborate(binder)
          (tpe, eventualTpe) <- TypeE.elaborate(tpe)
        } yield (binder.tpe, Seq(binder), Eventual.withUnifier { implicit unifier =>
          trees.InstanceOfPattern(Some(binder.evValDef.get), eventualTpe.get)
        })
      case PatternMatchings.InstanceOf(None, tpe) =>
        for {
          (tpe, eventualTpe) <- TypeE.elaborate(tpe)
        } yield (tpe, Seq(), Eventual.withUnifier { implicit unifier =>
          trees.InstanceOfPattern(None, eventualTpe.get)
        })
    }
  }

  val PatternE = new PatternE
}
