/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox._

trait AntiAliasing extends inox.ast.SymbolTransformer { self =>
  val trees: Trees
  val s: trees.type = trees
  val t: trees.type = trees
  import trees._

  def transform(syms: Symbols): Symbols = {
    import syms._

    object effects extends {
      val trees: self.trees.type = self.trees
      val symbols: syms.type = syms
    } with EffectsAnalysis

    /* Create a new FunDef for a given FunDef in the program.
     * Adapt the signature to express its effects. In case the
     * function has no effect, this will still return the original
     * fundef.
     *
     * Also update FunctionType parameters that need to become explicit
     * about the effect they could perform (returning any mutable type that
     * they receive).
     */
    def updateFunction[T <: FunAbstraction](fd: T, bindings: Set[ValDef], rewritings: Map[ValDef, Expr]): T = {
      val aliasedParams = getAliasedParams(fd)

      //val newParams = fd.params.map(vd => vd.getType match {
      //  case (ft: FunctionType) => {
      //    val nft = makeFunctionTypeExplicit(ft)
      //    if(ft == nft) vd else ValDef(vd.id.duplicate(tpe = nft))
      //  }
      //  case (cct: CaseClassType) => ccdMap.get(cct.classDef) match {
      //    case Some(ncd) => ValDef(vd.id.duplicate(tpe = ncd.typed))
      //    case None => vd
      //  }
      //  case _ => vd
      //})

      getReturnedExpressions(fd.body).foreach {
        case v: Variable if aliasedParams.contains(v.toVal) =>
          throw FatalError("Cannot return a shared reference to a mutable object")
        case _ => ()
      }

      val newFd = fd.copy(returnType = getReturnType(fd))

      if (aliasedParams.isEmpty) {
        val (pre, body, post) = breakDownSpecs(fd.body)
        val newBody = body.map(makeSideEffectsExplicit(_, fd, Seq()))
        newFd.copy(body = reconstructSpecs(pre, newBody, post, newFd.returnType))
      } else {
        val (pre, body, post) = breakDownSpecs(fd.body)
        val freshLocals: Seq[ValDef] = aliasedParams.map(v => v.freshen)
        val freshSubst = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap

        val newBody = body.map { body =>
          val freshBody = exprOps.replaceFromSymbols(freshSubst, body)
          val explicitBody = makeSideEffectsExplicit(freshBody, fd, freshLocals)

          //WARNING: only works if side effects in Tuples are extracted from left to right,
          //         in the ImperativeTransformation phase.
          val finalBody: Expr = Tuple(explicitBody +: freshLocals.map(_.toVariable))

          freshLocals.zip(aliasedParams).foldLeft(finalBody) {
            (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd)
          }
        }

        val newPost = post.map { post =>
          val Lambda(Seq(res), postBody) = post
          val newRes = ValDef(res.freshen, newFd.returnType)
          val newBody = exprOps.replace(
            aliasedParams.zipWithIndex.map { case (id, i) => 
              (id.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap ++
            aliasedParams.map(id =>
              (Old(id), id.toVariable): (Expr, Expr)).toMap +
              (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
            postBody)
          Lambda(Seq(newRes), newBody).setPos(post)
        }

        newFd.copy(fullBody = exprOps.reconstructSpecs(pre, newBody, newPost, newFd.returnType))
      }
    }

    //We turn all local val of mutable objects into vars and explicit side effects
    //using assignments. We also make sure that no aliasing is being done.
    def makeSideEffectsExplicit(
      body: Expr,
      originalFd: FunDef,
      aliasedParams: Seq[ValDef]
    ): Expr = {

      def mapApplication(args: Seq[Expr], nfi: Expr, nfiType: Type, fiEffects: Set[Int], rewritings: Map[ValDef, Expr]): Expr = {
        if (fiEffects.nonEmpty) {
          val modifiedArgs: Seq[(Seq[Variable], Expr)] =
            args.zipWithIndex.filter { case (arg, i) => fiEffects.contains(i) }
                .map { arg =>
                  val rArg = exprOps.replaceFromSymbols(rewritings, arg._1)
                  (referencedVars(rArg).filter(v => effects.isMutableType(v.tpe)), rArg)
                }

          val allParams: Seq[Variable] = modifiedArgs.flatMap(_._1)
          val duplicatedParams = allParams.diff(allParams.distinct).distinct
          if (duplicatedParams.nonEmpty)
            throw FatalError("Illegal passing of aliased parameter: " + duplicatedParams.head)

          //TODO: The case f(A(x1,x1,x1)) could probably be handled by forbidding creation at any program point of
          //      case class with multiple refs as it is probably not useful

          val freshRes = ValDef(FreshIdentifier("res"), nfiType)

          val extractResults = Block(
            for (((varsForIndex, expr), index) <- modifiedArgs; v <- varsForIndex) yield {
              val resSelect = TupleSelect(freshRes.toVariable, index + 2)
              expr match {
                case cs: ADTSelector =>
                  val (rec, path) = fieldPath(cs)
                  Assignment(v, objectUpdateToCopy(rec, path, resSelect)).setPos(cs)

                case as: ArraySelect =>
                  val (rec, path) = fieldPath(as)
                  Assignment(v, objectUpdateToCopy(rec, path, resSelect)).setPos(as)

                case cc @ ADT(adt, es) =>
                  val (_, vd) = (es zip cct.getADT.definition.fields).find {
                    case (va: Variable, _) => va == v
                    case _ => false
                  }.get
                  Assignment(v, ADTSelector(resSelect, vd.id))
                  //TODO: this only checks for a top level modified id,
                  //      must generalize to any number of nested case classes
                  //      must also handle combination of case class and selectors

                case _ => Assignment(v, resSelect).setPos(expr)
              }
            },
            TupleSelect(freshRes.toVariable, 1))

          val newExpr = Let(freshRes, nfi, extractResults)
          newExpr
        } else {
          nfi
        }
      }

      object transformer extends inox.transformers.Transformer {
        val trees: self.trees.type = self.trees
        type Env = (Set[ValDef], Map[ValDef, Expr], Map[ValDef, LocalFunDef])
        val initEnv = (bindings ++ aliasedParams.toSet, rewritings)

        implicit class EnvWrapper(env: Env) {
          val (bindings, rewritings, locals) = env
          def withBinding(vd: ValDef): Env = (bindings + vd, rewritings, locals)
          def withRewritings(map: Map[ValDef, Expr]): Env = (bindings, rewritings ++ map, locals)
          def withLocals(fds: Seq[LocalFunDef]): Env = (bindings, rewritings, locals ++ fds.map(fd => fd.name -> fd))
        }

        protected def rec(e: Expr, env: Env): Expr = e match {
          case l @ Let(vd, e, b) if effects.isMutableType(vd.tpe) =>
            val newExpr = rec(e, env)
            val newBody = rec(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case l @ LetVar(vd, e, b) if effects.isMutableType(vd.tpe) =>
            val newExpr = rec(e, env)
            val newBody = rec(b, env withBinding vd)
            LetVar(vd, newExpr, newBody).copiedFrom(l)

          case m @ MatchExpr(scrut, cses) if effects.isMutableType(scrut.getType) =>
            val newScrut = rec(scrut, env)
            val newCases = cses.map { case mc @ MatchCase(pattern, guard, rhs) =>
              val newRewritings = mapForPattern(scrut, pattern)
              val newGuard = guard.map(rec(_, env withRewritings newRewritings))
              val newRhs = rec(rhs, env withRewritings newRewritings)
              MatchCase(pattern, newGuarded, newRhs).copiedFrom(mc)
            }
            MatchExpr(newScrut, newCases).copiedFrom(m)

          case up @ ArrayUpdate(a, i, v) =>
            val ra = exprOps.replaceFromSymbols(rewritings, a)
            val (receiver, path) = fieldPath(ra, List(ArrayIndex(i)))

            receiverVar(receiver) match {
              case None => throw FatalError("Unsupported form of array update: " + up)
              case Some(v) =>
                if (env.bindings.contains(v.toVal)) {
                  rec(Assignment(v, objectUpdateToCopy(receiver, path, v).copiedFrom(up)).copiedFrom(up), env)
                } else {
                  ArrayUpdate(rec(a, env), rec(i, env), rec(v, env)).copiedFrom(up)
                }
            }

          case as @ FieldAssignment(o, id, v) =>
            val so = exprOps.replaceFromSymbols(rewritings, o)
            val (receiver, path) = fieldPath(so, List(ADTField(id)))

            receiverVar(so) match {
              case None => throw FatalError("Unsupported form of field assignment: " + as)
              case Some(ov) =>
                if (env.bindings.contains(ov.toVal)) {
                  rec(Assignment(ov, objectUpdateToCopy(receiver, path, v).copiedFrom(as)).copiedFrom(as), env)
                } else {
                  FieldAssignment(rec(o, env), id, rec(v, env)).copiedFrom(as)
                }
            }

          //we need to replace local fundef by the new updated fun defs.
          case l @ LetRec(fds, body) =>
            val nfds = fds.map(fd => updateFunction(Inner(fd), env.bindings, env.rewritings).fd)
            LetRec(nfds, rec(body, env withLocals fds)).copiedFrom(l)

          case e @ Ensuring(body, l @ Lambda(params, post)) =>
            Ensuring(rec(body, env), Lambda(params, rec(post, env)).copiedFrom(l)).copiedFrom(e)

          case l @ Lambda(params, body) =>
            val ft @ FunctionType(_, _) = l.getType
            val ownEffects = effects.functionTypeEffects(ft)
            val aliasedParams: Seq[ValDef] = params.zipWithIndex.flatMap {
              case (vd, i) if ownEffects.contains(i) => Some(vd)
              case _ => None
            }

            if (aliasedParams.isEmpty) {
              Lambda(params, rec(body, env)).copiedFrom(l)
            } else {
              val freshLocals: Seq[ValDef] = aliasedParams.map(v => v.freshen)
              val rewritingMap: Map[Variable, Variable] = aliasedParams.zip(freshLocals).map(p => p._1.toVariable -> p._2.toVariable).toMap
              val freshBody = exprOps.replaceFromSymbols(rewritingMap, body)
              val explicitBody = makeSideEffectsExplicit(freshBody, originalFd, freshLocals)

              //WARNING: only works if side effects in Tuples are extracted from left to right,
              //         in the ImperativeTransformation phase.
              val finalBody: Expr = Tuple(explicitBody +: freshLocals.map(_.toVariable))

              val wrappedBody: Expr = freshLocalVars.zip(aliasedParams).foldLeft(finalBody) {
                (bd, vp) => LetVar(vp._1, vp._2.toVariable, bd).copiedFrom(bd)
              }
              Lambda(params, rec(wrappedBody, env)).copiedFrom(lambda)
            }

          case fi @ FunctionInvocation(id, tps, args) =>
            val fd = Outer(fi.tfd.fd)
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = FunctionInvocation(id, tps, args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(fi)
            mapApplication(args, nfi, getReturnType(fd), effects(fd), env.rewritings)

          case ApplyLetRec(fun, tparams, args) =>
            val fd = Inner(locals(fun.toVal))
            val vis: Set[Variable] = varsInScope(fd)

            args.find { case v: Variable => vis.contains(v) case _ => false }
              .foreach(aliasedArg => throw FatalError("Illegal passing of aliased parameter: " + aliasedArg))

            val nfi = ApplyLetRec(fun, tparams, args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(fi)
            mapApplication(args, nfi, getReturnType(fd), effects(fd), env.rewritings)

          case app @ Application(callee, args) =>
            val ft @ FunctionType(_, to) = callee.getType
            to match {
              case TupleType(tps) if effects.isMutableType(tps.last) =>
                val nfi = Application(rec(callee, env), args.map(arg => rec(exprOps.replaceFromSymbols(env.rewritings, arg), env))).copiedFrom(app)
                mapApplication(args, nfi, to, effects.functionTypeEffects(ft), env.rewritings)
              case _ => Application(rec(callee, env), args.map(rec(_, env)))
            }

          case Operator(es, recons) => recons(es.map(rec(_, env)))
        }
      }

      transformer.transform(body)
    }


    //convert a function type with mutable parameters, into a function type
    //that returns the mutable parameters. This makes explicit all possible
    //effects of the function. This should be used for higher order functions
    //declared as parameters.
    def makeFunctionTypeExplicit(tpe: FunctionType): FunctionType = {
      val newReturnTypes = tpe.from.filter(t => effects.isMutableType(t))
      if (newReturnTypes.isEmpty) tpe
      else FunctionType(tpe.from, TupleType(tpe.to +: newReturnTypes))
    }

    //for each fun def, all the vars the the body captures.
    //Only mutable types.
    def varsInScope(fd: FunAbstraction): Set[Variable] = {
      val allFreeVars = fd.body.map(exprOps.variablesOf _).getOrElse(Set.empty)
      val freeVars = allFreeVars -- fd.params.map(_.id)
      freeVars.filter(v => effectsAnalysis.isMutableType(v.tpe))
    }

    def getAliasedParams(fd: FunAbstraction): Seq[ValDef] = {
      val ownEffects = effects(fd)
      fd.params.zipWithIndex.flatMap {
        case (vd, i) if ownEffects.contains(i) => Some(vd)
        case _ => None
      }
    }

    def getReturnType(fd: FunAbstraction): Type = {
      val aliasedParams = getAliasedParams(fd)
      tupleTypeWrap(fd.returnType +: aliasedParams.map(_.tpe))
    }

    /* A bit hacky, but not sure of the best way to do something like that
     * currently.
     */
    def getReturnedExpressions(expr: Expr): Seq[Expr] = expr match {
      case Let(_, _, rest) => getReturnedExpressions(rest)
      case LetVar(_, _, rest) => getReturnedExpressions(rest)
      case Block(_, rest) => getReturnedExpressions(rest)
      case IfExpr(_, thenn, elze) => getReturnedExpressions(thenn) ++ getReturnedExpressions(elze)
      case MatchExpr(_, cses) => cses.flatMap{ cse => getReturnedExpressions(cse.rhs) }
      case Operator(es, _) => es
    }


    //returns a list, to check for duplicates if necessary
    def referencedVars(o: Expr): List[Variable] = o match {
      case v: Variable => List(v)
      case ADTSelector(e, _) => referencedVars(e)
      case ADT(_, es) => es.toList.flatMap(referencedVars)
      case AsInstanceOf(e, _) => referencedVars(e)
      case ArraySelect(a, _) => referencedVars(a)
      case _ => Nil
    }

    def receiverVar(o: Expr): Option[Variable] = o match {
      case v: Variable => Some(v)
      case ADTSelector(e, _) => receiverVar(e)
      case AsInstanceOf(e, _) => receiverVar(e)
      case ArraySelect(a, _) => receiverVar(a)
      case _ => None
    }


    //private def extractFieldPath(o: Expr): (Expr, List[Identifier]) = {
    //  def rec(o: Expr): List[Identifier] = o match {
    //    case CaseClassSelector(_, r, i) =>
    //      val res = toFieldPath(r)
    //      (res._1, i::res)
    //    case expr => (expr, Nil)
    //  }
    //  val res = rec(o)
    //  (res._1, res._2.reverse)
    //}

    sealed trait Field
    case class ADTField(id: Identifier) extends Field
    case class ArrayIndex(e: Expr) extends Field

    //given a nested arrayselect and class selectors, return the receiver expression along
    //with the path from left to right
    //Does not consider FieldAssignment and ArrayUpdate as they only make sense on
    //the first level, and it seems cleaner to define path only on select operators
    def fieldPath(e: Expr, accPath: List[Field] = Nil): (Expr, List[Field]) = e match {
      case ADTSelector(r, id) => fieldPath(r, ADTField(id) :: accPath)
      case ArraySelect(a, index) => fieldPath(a, ArrayIndex(index) :: accPath)
      case e => (e, accPath)
    }

    //given a receiver object (mutable class or array, usually as a reference id),
    //and a path of field/index access, build a copy of the original object, with
    //properly updated values
    def objectUpdateToCopy(receiver: Expr, path: List[Field], newValue: Expr): Expr = path match {
      case ADTField(id) :: fs =>
        val adt @ ADTType(_, _) = receiver.getType
        val rec = objectUpdateToCopy(ADTSelector(receiver, id), fs, newValue).setPos(newValue)

        ADT(adt, adt.getADT.toConstructor.definition.fields.map { vd =>
          if (vd.id == id) rec
          else ADTSelector(receiver, vd.id).copiedFrom(receiver)
        })

      case ArrayIndex(index) :: fs =>
        val rec = objectUpdateToCopy(ArraySelect(receiver, index).setPos(newValue), fs, newValue)
        ArrayUpdated(receiver, index, rec).setPos(newValue)

      case Nil => newValue
    }

    object transformer extends SelfTreeTransformer {
      def transform(tpe: Type): Type = tpe match {
        case ft: FunctionType => makeFunctionTypeExplicit(ft, effectsAnalysis)
        case _ => super.transform(tpe)
      }
    }

    val newSyms = syms.transform(transformer)

    NoSymbols
      .withADTs(syms.adts.values.toSeq)
      .withFunctions(for (fd <- newSyms.functions.values.toSeq) yield {
        updateFunction(Outer(fd), Set.empty, Map.empty).fd
      })
  }
}
