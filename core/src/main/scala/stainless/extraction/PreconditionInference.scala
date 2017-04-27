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

    case class Input(vd: ValDef, selectors: Seq[Selector]) {
      lazy val (condition, expr): (Expr, Expr) = selectors(vd.toVariable)
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

    val hasSpecs: Map[Identifier, Boolean] = {
      def initRefs = functions.values.map(fd => fd -> exists {
        case Pre(_) => true
        case _ => false
      } (fd.fullBody)).toMap

      functions.values.map { fd =>
        fd.id -> (initRefs(fd) || transitiveCallees(fd).exists(initRefs))
      }.toMap
    }

    val applications: MutableMap[Identifier, Summary] = MutableMap.empty
    for (id <- functions.keySet if !hasSpecs(id)) {
      val fd = getFunction(id)
      val inputs = fd.params.flatMap { vd =>
        def rec(sel: Seq[Selector], tpe: Type): Seq[Input] = tpe match {
          case FunctionType(from, to) => Seq(Input(vd, sel))
          case TupleType(tps) => tps.zipWithIndex.flatMap { case (tp, i) => rec(sel :+ Right(i + 1), tp) }
          case adt: ADTType => adt.getADT match {
            case tadt if tadt.definition.isInductive => Seq.empty
            case tcons: TypedADTConstructor => tcons.fields.flatMap(vd => rec(sel :+ Left(vd.id), vd.tpe))
            case tsort: TypedADTSort => tsort.constructors.flatMap(tcons => rec(sel, tcons.toType))
          }
          case _ => Seq.empty
        }

        rec(Seq.empty, vd.tpe)
      }

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
                val in = s.collect { case (input, args) if input.vd.id == vd.id => (input.selectors, args) }

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
            Application(caller, args.map(rec(_, path)))

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
      .withADTs(adts.values.toSeq)
      .withFunctions(for (fd <- functions.values.toSeq) yield {
        if (hasSpecs(fd.id)) {
          fd
        } else {
          def preconditions(caller: Expr, args: Seq[Expr]): Expr = caller.getType match {
            case FunctionType(from, to) =>
              val (currArgs, restArgs) = args.splitAt(from.size)
              and(Application(Pre(caller), currArgs), preconditions(Application(caller, currArgs), restArgs))
            case _ => BooleanLiteral(true)
          }

          val preExtension = andJoin(for ((input, args) <- applications(fd.id).toSeq) yield (args match {
            case Empty => BooleanLiteral(true)
            case Unknown =>
              val FirstOrderFunctionType(from, to) = input.expr.getType
              val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
              implies(input.condition, Forall(vds, preconditions(input.expr, vds.map(_.toVariable))))
            case Known(arguments) =>
              implies(input.condition, andJoin(
                arguments.toSeq
                  .sortBy(_._2.map(formulaSize).sum)
                  .map { case (path, es) => path implies preconditions(input.expr, es) }
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
      .withADTs(adts.values.toSeq)
      .withFunctions(for (fd <- preSyms.functions.values.toSeq) yield {
        // @nv: can't use postMap because of Lambda in Ensuring predicate
        def injectRequires(e: Expr): Expr = e match {
          case Lambda(args, Require(pred, body)) => Lambda(args, Require(injectRequires(pred), injectRequires(body)))
          case Lambda(args, body) => Lambda(args, Require(preSyms.weakestPrecondition(body), injectRequires(body)))
          case Ensuring(body, Lambda(args, pred)) => Ensuring(injectRequires(body), Lambda(args, injectRequires(pred)))
          case Operator(es, recons) => recons(es.map(injectRequires))
        }

        fd.copy(fullBody = injectRequires(fd.fullBody))
      })

    finalSyms
  }
}
