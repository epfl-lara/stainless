/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet, ListBuffer}

trait PreconditionInference extends inox.ast.SymbolTransformer { self =>
  val trees: Trees
  lazy val s: trees.type = trees
  lazy val t: trees.type = trees

  import trees._

  def transform(syms: Symbols): Symbols = {
    import syms._
    import exprOps._

    object FlatApplication {
      def unapply(app: Application): Option[(Expr, Seq[Expr])] = app match {
        case Application(app: Application, args) => unapply(app).map(p => p._1 -> (p._2 ++ args))
        case Application(caller, args) => Some(caller, args)
      }

      def apply(caller: Expr, args: Seq[Expr]): Expr = caller.getType match {
        case FunctionType(from, to) if args.size >= from.size =>
          val (currArgs, restArgs) = args.splitAt(from.size)
          apply(Application(caller, currArgs), restArgs)
        case _ => caller
      }

      def pre(caller: Expr, args: Seq[Expr]): Expr = caller.getType match {
        case FunctionType(from, to) =>
          val (currArgs, restArgs) = args.splitAt(from.size)
          and(Application(Pre(caller), currArgs), pre(Application(caller, currArgs), restArgs))
        case _ => BooleanLiteral(true)
      }
    }

    type Selector = Either[Identifier, Int]

    implicit class SelectorsWrapper(selectors: Seq[Selector]) {
      def apply(e: Expr): (Expr, Expr) =  {
        def rec(e: Expr, selectors: Seq[Selector]): (Expr, Expr) = selectors match {
          case Left(id) +: rest => e.getType.asInstanceOf[ADTType].getADT match {
            case tcons: TypedADTConstructor =>
              rec(adtSelector(e, id), rest)
            case tsort: TypedADTSort =>
              val tcons = tsort.constructors.find(_.fields.exists(_.id == id)).get
              val (nextCond, expr) = rec(asInstOf(e, tcons.toType), selectors)
              (and(isInstOf(e, tcons.toType), nextCond), expr)
          }
          case Right(i) +: rest => rec(tupleSelect(e, i, true), rest)
          case _ => (BooleanLiteral(true), e)
        }

        rec(e, selectors)
      }
    }

    case class Input(source: Expr, selectors: Seq[Selector]) {
      lazy val (condition, expr): (Expr, Expr) = selectors(source)
    }

    def getInputs(e: Expr, allowInduct: Boolean = false): Seq[Input] = {
      def rec(sel: Seq[Selector], tpe: Type, seen: Set[ADTType]): Seq[Input] = tpe match {
        case FunctionType(from, to) => Seq(Input(e, sel))
        case TupleType(tps) => tps.zipWithIndex.flatMap { case (tp, i) => rec(sel :+ Right(i + 1), tp, seen) }
        case adt: ADTType => adt.getADT match {
          case tadt if seen(adt) || (!allowInduct && tadt.definition.isInductive) => Seq.empty
          case tcons: TypedADTConstructor => tcons.fields.flatMap(vd => rec(sel :+ Left(vd.id), vd.tpe, seen + adt))
          case tsort: TypedADTSort => tsort.constructors.flatMap(tcons => rec(sel, tcons.toType, seen + adt))
        }
        case _ => Seq.empty
      }

      rec(Seq.empty, e.getType, Set.empty)
    }

    sealed abstract class Arguments {
      def lub(that: Arguments): Arguments = (this, that) match {
        case (Empty, arg) => arg
        case (arg, Empty) => arg
        case (Unknown, arg) => Unknown
        case (arg, Unknown) => Unknown
        case (Known(es1), Known(es2)) =>
          val union = es1 ++ es2
          if (union.size > 5) Unknown
          else Known(union)
      }
    }

    case object Empty extends Arguments
    case class Known(es: Set[(Path, Seq[Expr])]) extends Arguments
    case object Unknown extends Arguments

    type Summary = Map[Input, Arguments]

    implicit class SummaryWrapper(summary: Summary) {
      def merge(that: Summary): Summary = that.foldLeft(summary)(_ merge _)
      def merge(p: (Input, Arguments)): Summary = summary.get(p._1) match {
        case None => summary + p
        case Some(arg) => summary + (p._1 -> (arg lub p._2))
      }
    }

    implicit class BooleanMapWrapper[T](map: Map[T, Boolean]) {
      def merge(that: Set[T]): Map[T, Boolean] = map ++ that.map(_ -> true)
      def merge(that: Map[T, Boolean]): Map[T, Boolean] = (map.keySet ++ that.keySet).map {
        k => k -> (map.getOrElse(k, false) || that.getOrElse(k, false))
      }.toMap
    }

    val hasSpecs: Set[Identifier] = {
      def initRefs = functions.values.filter(fd => exists {
        case Pre(_) => true
        case _ => false
      } (fd.fullBody)).toSet

      initRefs.flatMap(fd => Set(fd) ++ transitiveCallers(fd)).map(_.id)
    }

    val preSelectors: Set[Seq[Selector]] = {
      val inputs = functions.values.flatMap(_.params.flatMap(vd => getInputs(vd.toVariable, allowInduct = true)))
      val containers = inputs.flatMap { input =>
        val containers = fold[Set[Expr]]((e, es) => es.flatten.toSet + e)(input.expr)
        containers.map(_ -> input)
      }.groupBy(_._1).mapValues(_.map(_._2).toSet)

      val inputSpecs = inox.utils.fixpoint { used: Map[Input, Boolean] =>
        var result: Map[Input, Boolean] = used

        for (fd <- functions.values if hasSpecs(fd.id)) {
          val fdins = fd.params.flatMap(vd => containers.getOrElse(vd.toVariable, Set.empty)).toSet

          def rec(e: Expr): Unit = e match {
            case Pre(Lambda(args, body)) =>
              rec(body)
            case Pre(arg) =>
              result = result merge (
                if (containers contains arg) containers(arg)
                else fdins.filter(in => bestRealType(in.expr.getType) == bestRealType(arg.getType))
              )
            case fi @ FunctionInvocation(id, _, args) if hasSpecs(id) =>
              val tfd = fi.tfd
              for ((vd, e) <- tfd.params zip args) {
                val vUsed = used.filter(_._1.source == vd.toVariable).map(p => p._1.selectors -> p._2)

                def recSelectors(e: Expr, selectors: Seq[Selector]): Unit = e match {
                  case e if containers contains e =>
                    val newUsed = containers(e).map { case input @ Input(_, selectors) => input -> vUsed.get(selectors) }
                    result = result merge (
                      if (newUsed.forall(_._2.isDefined)) newUsed.map(p => p._1 -> p._2.get).toMap
                      else inputs.map(_ -> true).toMap
                    )

                  case ADT(tpe, es) =>
                    for ((vd, e) <- tpe.getADT.toConstructor.fields zip es) recSelectors(e, selectors :+ Left(vd.id))

                  case Tuple(es) =>
                    for ((e, i) <- es.zipWithIndex) recSelectors(e, selectors :+ Right(i + 1))

                  case _ => rec(e)
                }
              }
            case e if containers contains e =>
              result = result merge containers(e)
            case Operator(es, _) => es.foreach(rec)
          }

          for (vd <- fd.params) rec(vd.toVariable)
        }
        result
      } (inputs.map(_ -> false).toMap)

      inputSpecs.flatMap {
        case (Input(_, selectors), true) =>
          val lastId = selectors.reverse.indexWhere(_.isLeft)
          if (lastId >= 0) Some(selectors.drop(selectors.size - lastId - 1))
          else None
        case _ => None
      }.toSet
    }

    val (handledSelectors, adtSyms): (Set[Seq[Selector]], Symbols) = {
      var handledSelectors: Set[Seq[Selector]] = Set.empty
      val newFunctions = new ListBuffer[FunDef]
      val newADTs = new ListBuffer[ADTDefinition]

      var handled: Set[ADTDefinition] = Set.empty
      def rec(adt: ADTDefinition): Unit = {
        val root = adt.root
        if (!handled(root)) {
          handled += root
          if (!root.invariant.exists(fd => hasSpecs(fd.id))) {
            val constructors = root match {
              case sort: ADTSort => sort.constructors
              case cons: ADTConstructor => Seq(cons)
            }

            val (tparams, thiss) = root.invariant match {
              case Some(fd) => (fd.typeArgs, fd.params.head)
              case None =>
                val typeArgs = root.typeArgs.map(_.freshen)
                (typeArgs, ValDef(FreshIdentifier("thiss"), root.typed(typeArgs).toType))
            }

            for (c <- constructors; vd <- c.fields) {
              typeOps.preTraversal {
                case tpe: ADTType => rec(tpe.getADT.definition)
                case _ =>
              } (vd.tpe)
            }

            val invariant = andJoin(constructors.map { c =>
              val ctpe = c.typed(tparams).toType
              val inputs = getInputs(asInstOf(thiss.toVariable, ctpe), allowInduct = true)
                .filterNot(_.selectors.tails.exists(t => handledSelectors(t) || preSelectors(t)))
              handledSelectors ++= inputs.map(_.selectors)

              implies(isInstOf(thiss.toVariable, ctpe), andJoin(inputs.map { input =>
                val FirstOrderFunctionType(from, to) = input.expr.getType
                val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
                implies(input.condition, forall(vds, FlatApplication.pre(input.expr, vds.map(_.toVariable))))
              }))
            })

            if (invariant != BooleanLiteral(true)) root.invariant match {
              case Some(fd) =>
                newFunctions += fd.copy(fullBody = and(invariant, fd.fullBody))
              case None =>
                val id = FreshIdentifier("inv")
                newADTs += (root match {
                  case sort: ADTSort => sort.copy(flags = sort.flags + HasADTInvariant(id))
                  case cons: ADTConstructor => cons.copy(flags = cons.flags + HasADTInvariant(id))
                })
                newFunctions += new FunDef(
                  id,
                  tparams.map(TypeParameterDef(_)),
                  Seq(thiss),
                  BooleanType,
                  invariant,
                  root.flags filter (_.name == "library")
                )
            }
          }
        }
      }

      for (adt <- adts.values if adt.root == adt) rec(adt)

      val newIds = newFunctions.map(_.id).toSet ++ newADTs.map(_.id)
      val adtSyms = NoSymbols
        .withFunctions(functions.values.filterNot(fd => newIds(fd.id)).toSeq ++ newFunctions)
        .withADTs(adts.values.filterNot(d => newIds(d.id)).toSeq ++ newADTs)

      (handledSelectors, adtSyms)
    }

    val applications: MutableMap[Identifier, Summary] = MutableMap.empty
    for (id <- functions.keySet if !hasSpecs(id)) {
      val fd = getFunction(id)
      val inputs = fd.params
        .flatMap(vd => getInputs(vd.toVariable))
        .filterNot(_.selectors.tails.exists(handledSelectors))

      applications(id) = inputs.map(_ -> Empty).toMap
    }

    val worklist = new ListBuffer[Identifier]
    worklist ++= applications.keys

    while (worklist.nonEmpty) {
      val cid = worklist.remove(0)
      val fd = getFunction(cid)

      val current = applications(cid)
      val containers = current.keySet.flatMap { input =>
        val containers = fold[Set[Expr]]((e, es) => es.flatten.toSet + e)(input.expr)
        containers.map(_ -> input)
      }.groupBy(_._1).mapValues(_.map(_._2))

      def simplifyPath(path: Path, es: Seq[Expr]): (Path, Seq[Expr]) = {
        import syms.simplifier._

        def rec(elements: Seq[Path.Element], cnf: CNFPath, es: Seq[Expr]): (Path, Seq[Expr]) = elements match {
          case Left((vd, e)) +: rest => e match {
            case simp @ (_: Variable | _: Literal[_]) =>
              val replace = (e: Expr) => replaceFromSymbols(Map(vd.toVariable -> simp), e)
              val newRest = rest.map(_.left.map(p => p._1 -> replace(p._2)).right.map(replace))
              rec(newRest, cnf, es.map(replace))
            case _ =>
              val allVars = rest.foldRight(es.flatMap(variablesOf).toSet) {
                case (Left((vd, e)), vars) => vars ++ variablesOf(e) - vd.toVariable
                case (Right(cond), vars) => vars ++ variablesOf(cond)
              }

              if (!allVars(vd.toVariable) && isPure(e, cnf)) {
                rec(rest, cnf, es)
              } else {
                val (rpath, res) = rec(rest, cnf withBinding (vd -> e), es)
                (Path(vd -> e) merge rpath, res)
              }
          }

          case Right(cond) +: rest =>
            if (cnf contains cond) rec(rest, cnf, es)
            else {
              val (rpath, res) = rec(rest, cnf withCond cond, es)
              (Path(cond) merge rpath, res)
            }

          case _ => (Path.empty, es)
        }

        rec(path.elements, CNFPath.empty, es)
      }

      var result: Summary = Map.empty
      new transformers.TransformerWithPC {
        val trees: self.trees.type = self.trees
        val symbols: syms.type = syms

        type Env = Path
        val pp = Path
        val initEnv = Path.empty

        override protected def rec(e: Expr, path: Path): Expr = e match {
          case fi @ FunctionInvocation(id, tps, args) =>
            val tfd = fi.tfd
            if (tfd.tps == tfd.fd.typeArgs) {
              val s = applications(id)

              val newArgs = (tfd.params zip args).map { case (vd, e) =>
                val in = s.collect { case (input, args) if input.source == vd.toVariable => (input.selectors, args) }

                def recSelectors(e: Expr, selectors: Seq[Selector]): Expr = e match {
                  case e if containers contains e =>
                    val inputs = containers(e)

                    val newArgs = inputs.map { case input @ Input(_, selectors) =>
                      input -> in.get(selectors).map {
                        case Known(arguments) => Known(arguments.map { case (p, es) =>
                          val freshParams = tfd.params.map(_.freshen)
                          val paramSubst = (tfd.params zip freshParams.map(_.toVariable)).toMap

                          val freeVars = p.variables -- tfd.params.map(_.toVariable).toSet
                          val freeSubst = (freeVars.map(_.toVal) zip freeVars.map(_.freshen)).toMap

                          val freshBindings = p.bound.map(vd => vd.freshen)
                          val freshSubst = (p.bound zip freshBindings).toMap
                          val newSubst = paramSubst ++ freshSubst.mapValues(_.toVariable) ++ freeSubst

                          val newPath = path withBindings (freshParams zip args)  merge p.map(freshSubst, replaceFromSymbols(newSubst, _))
                          val newEs = es.map(replaceFromSymbols(newSubst, _))
                          simplifyPath(newPath, newEs)
                        })
                        case a => a
                      }
                    }

                    result = result merge (
                      if (newArgs.forall(_._2.isDefined)) newArgs.map(p => p._1 -> p._2.get).toMap
                      else inputs.map(_ -> Unknown).toMap
                    )
                    e

                  case ADT(tpe, es) =>
                    ADT(tpe, (tpe.getADT.toConstructor.fields zip es).map {
                      case (vd, e) => recSelectors(e, selectors :+ Left(vd.id))
                    })

                  case Tuple(es) =>
                    Tuple(es.zipWithIndex.map {
                      case (e, i) => recSelectors(e, selectors :+ Right(i + 1))
                    })

                  case _ => rec(e, path)
                }

                recSelectors(e, Seq.empty)
              }

              FunctionInvocation(id, tps, newArgs)
            } else {
              super.rec(e, path)
            }

          case FlatApplication(caller, args) if (containers contains caller) && !e.getType.isInstanceOf[FunctionType] =>
            val freeVars = (args.flatMap(variablesOf).toSet ++ path.variables) --
              fd.params.map(_.toVariable).toSet --
              path.bound.map(_.toVariable).toSet

            val arguments = if (freeVars.nonEmpty) Unknown else Known(Set(simplifyPath(path, args)))
            val Seq(input) = containers(caller).toSeq
            result = result merge (input -> arguments)
            FlatApplication(caller, args.map(rec(_, path)))

          case e if containers contains e =>
            for (input <- containers(e)) {
              result = result merge (input -> Unknown)
            }
            e

          case _ => super.rec(e, path)
        }
      }.transform(fd.fullBody)

      if (result != current) {
        applications(cid) = current merge result
        for (cfd <- callers(fd) if !hasSpecs(cfd.id) && !(worklist contains cfd.id)) worklist += cfd.id
      }
    }

    val preSyms = NoSymbols
      .withADTs(adtSyms.adts.values.toSeq)
      .withFunctions(for (fd <- adtSyms.functions.values.toSeq) yield {
        if (!(syms.functions contains fd.id) || hasSpecs(fd.id)) {
          fd
        } else {
          val preExtension = andJoin(for ((input, args) <- applications(fd.id).toSeq) yield (args match {
            case Empty => BooleanLiteral(true)
            case Unknown =>
              val FirstOrderFunctionType(from, to) = input.expr.getType
              val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
              implies(input.condition, forall(vds, FlatApplication.pre(input.expr, vds.map(_.toVariable))))
            case Known(arguments) =>
              implies(input.condition, andJoin(
                arguments.toSeq
                  .sortBy(_._2.map(formulaSize).sum)
                  .map { case (path, es) => path implies FlatApplication.pre(input.expr, es) }
              ))
          }))

          if (preExtension != BooleanLiteral(true)) {
            val newPre = andJoin(preExtension +: fd.precondition.toSeq)
            fd.copy(fullBody = withPrecondition(fd.fullBody, Some(newPre)))
          } else {
            fd
          }
        }
      })

    val finalSyms = NoSymbols
      .withADTs(preSyms.adts.values.toSeq)
      .withFunctions(for (fd <- preSyms.functions.values.toSeq) yield {
        // @nv: can't use postMap because of Lambda in Ensuring predicate
        def injectRequires(e: Expr): Expr = (e match {
          case Lambda(args, r @ Require(pred, body)) => Lambda(args, Require(injectRequires(pred), injectRequires(body)).copiedFrom(r))
          case Lambda(args, body) => Lambda(args, Require(preSyms.weakestPrecondition(body), injectRequires(body)))
          case Ensuring(body, l @ Lambda(args, pred)) => Ensuring(injectRequires(body), Lambda(args, injectRequires(pred)).copiedFrom(l))
          case Operator(es, recons) => recons(es.map(injectRequires))
        }).copiedFrom(e)

        fd.copy(fullBody = injectRequires(fd.fullBody))
      })

    finalSyms
  }
}
