package stainless
package verification

import CoqEncoder._
import CoqExpression._

object optAdmitAll extends inox.FlagOptionDef("admit-all", false)

trait CoqEncoder {
  given givenDebugSection: DebugSectionCoq.type = DebugSectionCoq

  val p: StainlessProgram
  val ctx: inox.Context
  val st: stainless.trees.type = stainless.trees

  import st._
  import p.symbols.{given, _}
  import p.symbols.CallGraphOrderings._

  // collect the types for which we have no definitions
  // unused for now
  var undefinedTypes = Set[Type]()

  // to give unique names to the arguments we add for preconditions
  var i = 0
  val hypName = "contractHyp"

  val initTactic = CoqIdentifier(FreshIdentifier("t"))

  var lastTactic: CoqExpression = idtac
  var mainTactic: CoqIdentifier = initTactic
  var rewriteTactic: CoqExpression = idtac

  //TODO use make fresh uniformly
  def freshId(): CoqIdentifier = {
    i += 1
    CoqIdentifier(FreshIdentifier(hypName + i))
  }

  // ignore flags with an explicit warning
  def ignoreFlags(s: String, flags: Seq[Flag]) = {
    //if (!flags.isEmpty)
      //ctx.reporter.warning(s"Coq translation ignored flags for $s:\n" + flags.mkString(", ") + "\n")
  }

  def freePatterns(p: Pattern): Boolean = {
    p match {
      case WildcardPattern(_) => true
      case TuplePattern(_, es) => es forall freePatterns
      case _ => false
    }
  }

  def isExhaustive(scrut: Expr, cases: Seq[MatchCase]): Boolean = {
    val tpe: Type = scrut.getType
    tpe match {
      case adt @ ADTType(_, _) => {
        val ctorsIds: Seq[Identifier] = adt.getSort.constructors map (_.id)
        //non guarded matches without sub patterns
        val unguardedADTs: Seq[Identifier] =
          cases collect {
            case MatchCase(ADTPattern(_, id, _, subPatterns), guard, _)
              if subPatterns forall freePatterns => id
          }
        cases.forall {case MatchCase(_,g,_) => g.isEmpty} &&
          (ctorsIds forall (unguardedADTs contains _))

      }
      case _ => false
    }
  }

  // transform a Stainless expression into a Coq expression
  def transformTree(t: st.Expr): CoqExpression = t match {
    case MatchExpr(scrut, cases) =>
      if(isExhaustive(scrut, cases))
        CoqMatch(transformTree(scrut), cases map makeFunctionCase)
      else
        transformTree(matchToIfThenElse(t, false))
    case IfExpr(cond, thenn, elze) =>
      IfThenElse(
        transformTree(cond),
        transformType(t.getType),
        CoqLambda(coqUnused, transformTree(thenn)),
        CoqLambda(coqUnused, transformTree(elze))
      )
    case Variable(id,tpe,flags) =>
      ignoreFlags(t.toString, flags)
      makeFresh(id)
    case ADT(id, targs, args) =>
      Constructor(constructorIdentifier(id), targs.map(transformType) ++ args.map(transformTree))
    case FunctionInvocation(id, targs, args) =>
      val allArgs = targs.map(transformType) ++ args.map(transformTree)
      val allArgs_and_hyp =
        if (exprOps.preconditionOf(p.symbols.functions(id).fullBody).isEmpty)
          allArgs
        else
          allArgs :+ CoqUnknown

      if (exprOps.postconditionOf(p.symbols.functions(id).fullBody).isEmpty)
        CoqApplication(makeFresh(id), allArgs_and_hyp)
      else
        proj1_sig(CoqApplication(makeFresh(id), allArgs_and_hyp))
    case Application(t, ts) =>
      CoqApplication(transformTree(t), ts.map(transformTree))
    case FiniteSet(args,tpe) =>
      CoqFiniteSet(args map transformTree, transformType(tpe))
    case SetUnion(t1,t2) => CoqSetUnion(transformTree(t1), transformTree(t2))
    case SetIntersection(t1,t2) => CoqSetIntersection(transformTree(t1), transformTree(t2))
    case SetDifference(t1,t2) => CoqSetDifference(transformTree(t1), transformTree(t2))
    case SubsetOf(t1,t2 ) => CoqSetSubset(transformTree(t1), transformTree(t2))
    case ElementOfSet(t1,t2) => CoqBelongs(transformTree(t1), transformTree(t2))
    case Or(ts) => Orb(ts map transformTree)
    case And(ts) => Andb(ts map transformTree)
    case Not(t) => Negb(transformTree(t))
    case Implies(t1,t2) => implb(transformTree(t1), transformTree(t2))
    case Equals(t1,t2) if (t1.getType == IntegerType()) =>
      CoqApplication(CoqLibraryConstant("Zeq_bool"),  Seq(transformTree(t1), transformTree(t2)))
    case Equals(t1,t2) if (t1.getType == BooleanType()) =>
      CoqApplication(CoqLibraryConstant("Bool.eqb"), Seq(transformTree(t1), transformTree(t2)))
    case Equals(t1,t2) if t1.getType.isInstanceOf[SetType] =>
      CoqSetEquals(transformTree(t1),transformTree(t2))
    case Equals(t1,t2) =>
      ctx.reporter.warning(s"Equality for type ${t1.getType} got translated to equality in Coq") //remove warning for lists and other cases where this is on purpose
      propInBool(CoqEquals(transformTree(t1),transformTree(t2)))
    case BooleanLiteral(true) => trueBoolean
    case BooleanLiteral(false) => falseBoolean
    case ADTSelector(adt, selector) =>
      adt.getType match {
        case ADTType(_,args) =>
          val typeParameters = args.map(transformType)
          CoqApplication(makeFresh(selector), typeParameters :+ transformTree(adt))
        case _ =>
          ctx.reporter.fatalError(s"The translation to Coq failed because $adt does not have an ADT type but ${adt.getType}.")
      }
    case Forall(args, body) =>
      val params = args.map { case vd@ValDef(id,tpe,flags) =>
        ignoreFlags(vd.toString, flags)
        (makeFresh(id), transformType(tpe))
      }
      CoqForall(params, CoqEquals(transformTree(body),trueBoolean))
    case Annotated(body, flags) =>
      ignoreFlags(t.toString, flags)
      transformTree(body)
    case Let(vd, value, body) =>
      //without type
      CoqLet(makeFresh(vd.id), None, transformTree(value), transformTree(body))
    case Lambda(vds, body) =>
      vds.foldRight(transformTree(body))((a,b) => CoqLambda(makeFresh(a.id), b) )
    //Integer operations
    case UMinus(e) => CoqApplication(CoqLibraryConstant("Z.opp"), Seq(transformTree(e)))
    case GreaterEquals(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.geb"), Seq(transformTree(e1), transformTree(e2)))
    case GreaterThan(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.gtb"), Seq(transformTree(e1), transformTree(e2)))
    case LessEquals(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.leb"), Seq(transformTree(e1), transformTree(e2)))
    case LessThan(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.ltb"), Seq(transformTree(e1), transformTree(e2)))
    case Plus(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.add"), Seq(transformTree(e1), transformTree(e2)))
    case Minus(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.sub"), Seq(transformTree(e1), transformTree(e2)))
    case Times(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.mul"), Seq(transformTree(e1), transformTree(e2)))
    case Division(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.div"), Seq(transformTree(e1), transformTree(e2)))
    case Modulo(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.modulo"), Seq(transformTree(e1), transformTree(e2)))
    case Remainder(e1,e2) =>
      CoqApplication(CoqLibraryConstant("Z.rem"), Seq(transformTree(e1), transformTree(e2)))
    case IntegerLiteral(i: BigInt) =>
      CoqZNum(i)
    case bvl @ BVLiteral(_, _, _) => CoqZNum(bvl.toBigInt)
    case Tuple(es) =>
      CoqTuple(es.map(transformTree))

    case TupleSelect(tuple, idx) =>
      tuple.getType match  {
        case tpe @ TupleType(_) =>
          if (idx == 1)
            (1 to tpe.dimension-idx).foldRight(transformTree(tuple)) {(idx, body) => fst(body)}
          else
            snd((1 to tpe.dimension-idx).foldRight(transformTree(tuple)) {(idx, body) => fst(body)})
        case _ => ctx.reporter.fatalError("Tuple matching with incorrect type")
      }
    case IsConstructor(expr, id) =>
        CoqApplication(recognizer(id), getTParams(getConstructor(id)).map(_ => CoqUnknown) ++ Seq(transformTree(expr)))
    case Error(tpe, desc) => deriveContradiction //TODO is it ok?
    case Assume(pred, body) =>
      CoqLet(makeFresh("assumption"), None, magic(CoqEquals(transformTree(pred), trueBoolean)), transformTree(body) )
    case Assert(pred,_,body ) =>
      CoqLet(makeFresh("assertion"), Some(CoqEquals(transformTree(pred), trueBoolean)), CoqUnknown, transformTree(body) )
    case _ =>
      ctx.reporter.warning(s"The translation to Coq does not support expression `${t.getClass}` yet: $t.")
      magic(transformType(t.getType))
  }

  // creates a case for a match expression
  def makeFunctionCase(mc: MatchCase): CoqCase = mc match {
    case MatchCase(pattern, None, rhs) =>
      CoqCase(transformPattern(pattern), transformTree(rhs))
    case MatchCase(pattern, _, rhs) =>
      ctx.reporter.warning(s"Guard in match cases are not supported by the Coq translation yet:\n$mc.")
      ctx.reporter.warning(s"This guard was ignored during the translation.")
      CoqCase(transformPattern(pattern), transformTree(rhs))
  }

  // transform patterns that appear in match cases
  def transformPattern(p: Pattern): CoqPattern = p match {
    case a@ADTPattern(binder, id, _, subPatterns) =>
      for (bind <- binder) {
        ctx.reporter.warning(s"Binder $bind in pattern $a is ignored.")
      }
      val unusedTypeParameters = (1 to getTParams(constructors(id)).size).map(_ => VariablePattern(None))
      InductiveTypePattern(constructorIdentifier(id), unusedTypeParameters ++ subPatterns.map(transformPattern))
    case WildcardPattern(None) => VariablePattern(None)
    case WildcardPattern(Some(ValDef(id,tpe,flags))) =>
      ignoreFlags(p.toString, flags)
      ctx.reporter.warning(s"Ignoring type $tpe in the wildcard pattern $p.")
      VariablePattern(Some(makeFresh(id)))
    case TuplePattern(None, ps) => CoqTuplePattern(ps.map(transformPattern))
    case TuplePattern(Some(ValDef(id,tpe,flags)), ps) =>
      ignoreFlags(p.toString, flags)
      ctx.reporter.warning(s"Ignoring type $tpe in the wildcard pattern $p.")
      //TODO not tested
      CoqTuplePatternVd(ps.map(transformPattern), VariablePattern(Some(makeFresh(id))))
    case _ => ctx.reporter.fatalError(s"Coq does not support patterns such as `$p` (${p.getClass}) yet.")
  }

  // transforms an ADT into an inductive type
  def transformADT(a: st.ADTSort): CoqCommand = {
    // ignoreFlags(a.toString, a.flags)
    InductiveDefinition(
      makeFresh(a.id),
      a.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) },
      a.constructors.map(c => makeCase(a, c))
    ) $
    (if (a.constructors.size > 1) {
      buildRecognizers(a) $
      buildExistsCreators(a) $
      buildSubTypes(a) $
      buildAdtTactic(a)
    } else
      NoCommand) $
    buildAccessorsForChildren(a)
  }

  // Define for each constructor of an ADT a function that identifies such elements
  def buildRecognizers(a: ADTSort): CoqCommand = {
    manyCommands(a.constructors.map(c => buildRecognizer(a, c)))
  }

  // Define a function that identifies the case of an element of an inductive type
  // and checks that the invariant holds
  def buildRecognizer(root: ADTSort, constructor: ADTConstructor): CoqCommand = {
    val element = rawIdentifier("src")
    val tparams = getTParams(constructor).map(t => CoqIdentifier(t.id))
    val extraCase =
      if (root.constructors.size > 1) {
        Some(CoqCase(VariablePattern(None), falseBoolean))
      }
      else
        None

    NormalDefinition(
      recognizer(constructor.id),
      getTParams(constructor).map { case p => (CoqIdentifier(p.id), TypeSort) } ++
        Seq((element, Constructor(makeFresh(root.id), tparams))),
      CoqBool,
      CoqMatch(element, Seq(
        CoqCase(
          {
            val unusedTypeParameters = (1 to getTParams(constructor).size).map(_ => VariablePattern(None))
            val unusedFields = (1 to constructor.fields.size).map(_ => VariablePattern(None))
            InductiveTypePattern(constructorIdentifier(constructor.id), unusedTypeParameters ++ unusedFields)
          },
          trueBoolean
        )) ++ extraCase
      )
    ) $
    RawCommand(s"#[export] Hint Unfold  ${recognizer(constructor.id).coqString}: recognizers.\n")
  }

  def buildExistsCreators(a: ADTSort): CoqCommand =
    manyCommands(a.constructors.map(c => buildExistsCreator(c)))

  def buildExistsCreator(ctor: ADTConstructor): CoqCommand = {
    val self = makeFresh("self")
    val tParams = getTParams(ctor).map(tp => CoqIdentifier(tp.id))

    val varTypes: Seq[CoqExpression] = ctor.fields.map(vd => transformType(vd.tpe))
    val varNames: Seq[CoqIdentifier] = varTypes map (_ => makeFresh())

    val existsExpr = CoqExists(varNames zip varTypes, CoqEquals(CoqApplication(constructorIdentifier(ctor.id), tParams ++ varNames), self))
    val impl = BiArrow(
      CoqEquals(trueBoolean, CoqApplication(recognizer(ctor.id), tParams :+ self )),
      existsExpr
    )

    val body = CoqForall(
      Seq((self, CoqApplication(CoqIdentifier(ctor.sort), tParams))) ++ tParams.map(tp => (tp, TypeSort)),
      impl)
    CoqLemma(existsCreatorName(ctor.id), body, RawCommand(s"repeat ${mainTactic.coqString} || eauto."))
  }

  def existsCreatorName(id: Identifier): CoqIdentifier = {
    CoqIdentifier(new Identifier(id.name + "_exists", id.id, id.globalId))
  }

  def buildSubTypes(a: ADTSort): CoqCommand =
    manyCommands(a.constructors.map(c => buildSubType(a, c)))

  def buildSubType(root: ADTSort, constructor: ADTConstructor): CoqCommand = {
    val ttparams = root.tparams.map(p => (CoqIdentifier(p.id), TypeSort))
    val tparams = root.tparams.map(t => CoqIdentifier(t.id))
    val element = rawIdentifier("src")
    NormalDefinition(
      refinedIdentifier(constructor.id),
      ttparams,
      TypeSort,
      Refinement(
        element,
        CoqApplication(makeFresh(root.id), tparams),
        CoqApplication(recognizer(constructor.id), tparams :+ element) === trueBoolean
      )
    ) $
    RawCommand(s"#[export] Hint Unfold  ${refinedIdentifier(constructor.id).coqString}: refinements.\n")
  }

  def buildAccessorsForChildren(a: ADTSort): CoqCommand =
    manyCommands(a.constructors.map(c => buildAccessors(a, c)))

  def buildAccessors(root: ADTSort, constructor: ADTConstructor): CoqCommand = {
    manyCommands(constructor.fields.zipWithIndex.map {
      case (ValDef(id,tpe,flags), i) =>
        buildAccessor(id, tpe, i, constructor.fields.size, root, constructor)
    })
  }

  def buildAccessor(id: Identifier, tpe: Type, i: Int, n: Int, root: ADTSort, constructor: ADTConstructor): CoqCommand = {
    val element = rawIdentifier("src")
    val extraCase =
      if (root.constructors.size > 1)
        Some(CoqCase(VariablePattern(None), deriveContradiction))
      else
        None
    val tparams = root.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) }
    val refid = if (root.constructors.size > 1)
                    refinedIdentifier(constructor.id)
                else
                    CoqIdentifier (root.id)
    NormalDefinition(
      makeFresh(id),
        tparams ++
        Seq(((element, CoqApplication(refid, root.tparams.map(t => CoqIdentifier(t.id)))))),
      transformType(tpe),
      CoqMatch(element,
        Seq(
          CoqCase(
            {
              val unusedTypeParameters = (1 to getTParams(constructor).size).map(_ => VariablePattern(None))
              val fields = (0 to n-1).map(i => VariablePattern(Some(rawIdentifier("f" + i))))
              InductiveTypePattern(constructorIdentifier(constructor.id), unusedTypeParameters ++ fields)
            },
            rawIdentifier("f" + i)
          )
        ) ++ extraCase
      )
    )
  }

  // creates a case for an inductive type
  def makeCase(root: Definition, a: ADTConstructor) = {
    val fieldsTypes = a.fields.map(vd => transformType(vd.tpe))
    val arrowType = fieldsTypes.foldRight[CoqExpression](
      Constructor(makeFresh(root.id), getTParams(a).map(t => CoqIdentifier(t.id)))) // the inductive type
      { case (field, acc) => Arrow(field, acc) } // the parameters of the constructor
    InductiveCase(constructorIdentifier(a.id), arrowType)
  }

  def buildAdtTactic(sort: ADTSort): CoqCommand = {
    val newTactic = makeFresh(s"${sort.id.name}_tactic")
    val prevTactic = lastTactic
    lastTactic = newTactic
    CoqMatchTactic(newTactic,
      sort.constructors.flatMap(con => makeTacticCases(con)) :+ CoqCase(VariablePattern(None), prevTactic)
    ) $
    updateObligationTactic()
  }

  def updateObligationTactic() : CoqCommand = {
    val t1 = makeFresh("t")
    val t = makeFresh("t")
    mainTactic = t
    RawCommand(s"""Ltac ${t1.coqString} :=
                  |  t_base ||
                  |  ${lastTactic.coqString} ||
                  |  slow ||
                  |  ifthenelse_step ||
                  |  rewrite_ifthenelse ||
                  |  destruct_ifthenelse ||
                  |  (progress autorewrite with libCase in *) ||
                  |  autounfold with definitions in *.""".stripMargin) $
    RawCommand(s"""Ltac ${t.coqString} :=
                  |  ${t1.coqString} ||
                  |  ${rewriteTactic.coqString} ||
                  |  autounfold with recognizers in *.""".stripMargin) $
    RawCommand(s"\nObligation Tactic := repeat ${t.coqString}.\n")
  }

  def makeTacticCases(ctor: ADTConstructor) : Seq[CoqCase] = {
    val existsCtor = existsCreatorName(ctor.id)
    val ids: Seq[CoqIdentifier] = getTParams(ctor).map(tp => CoqIdentifier(tp.id)) :+ makeFresh("self")
    val rcg = CoqApplication(recognizer(ctor.id), ids.map(id => CoqUnboundIdentifier(id)))
    val label = poseNew(Mark(ids, ctor.id.name + "_exists"))
    val h = makeFresh("H")
    val pose = {(hyp: CoqExpression) =>
      PoseProof(CoqApplication(proj1(CoqApplication(existsCtor, Seq(CoqUnknown, CoqUnknown))), Seq(hyp)))
    }
    val h1 = makeFresh("H1")
    val h2 = makeFresh("H2")
    Seq(
      CoqCase(
        CoqTacticPattern(Map[CoqIdentifier,CoqExpression](h -> CoqEquals(trueBoolean, rcg))),
        CoqSequence(Seq(label, pose(h)))
      ),
      CoqCase(
        CoqTacticPattern(Map[CoqIdentifier,CoqExpression](h -> CoqEquals(rcg, trueBoolean))),
        CoqSequence(Seq(label, pose(eq_sym(h))))
      )
    )
  }

  // transform function definitions
  def transformFunction(fd: st.FunDef, admitObligations: Boolean = false): CoqCommand = {
    ignoreFlags(fd.toString, fd.flags)
    val mutual = p.symbols.functions.find{ case (_,fd2) => fd != fd2 && transitivelyCalls(fd, fd2) && transitivelyCalls(fd2, fd) }
    if (mutual.isDefined)
      ctx.reporter.fatalError(s"The translation to Coq does not support mutual recursion (between ${fd.id.name} and ${mutual.get._1.name})")
    else {
      val tparams: Seq[(CoqIdentifier,CoqExpression)] = fd.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) }
      val params: Seq[(CoqIdentifier,CoqExpression)] = fd.params.map { case vd => (makeFresh(vd.id), transformType(vd.tpe)) }
      val body = exprOps.withoutSpecs(fd.fullBody) match {
        case None => ctx.reporter.fatalError(s"We do not support functions with empty bodies: ${fd.id.name}")
        case Some(b) => transformTree(b)
      }
      val preconditionName = freshId()
      val preconditionParam: Seq[(CoqIdentifier,CoqExpression)] = exprOps.preconditionOf(fd.fullBody) match {
        case None => Seq()
        case Some(p) => Seq((preconditionName, transformTree(p) === trueBoolean))
      }
      val returnType = exprOps.postconditionOf(fd.fullBody) match {
        case None => transformType(fd.returnType)
        case Some(Lambda(Seq(vd), post)) =>
          Refinement(makeFresh(vd.id), transformType(vd.tpe), transformTree(post) === trueBoolean)
      }
      val allParams = tparams ++ params ++ preconditionParam
      val tmp = if (fd.isRecursive) {
        val funName = makeFresh(fd.id)

        //create a name for the return type
        val returnTypeName = makeFresh(funName.coqString  +"_rt")

        val dependentParams: Map[CoqIdentifier, CoqExpression] = (preconditionParam :+ (returnTypeName, returnType)).toMap


        val dependentParamNames: Map[CoqIdentifier, CoqIdentifier] =
          dependentParams map {case (arg, _) => (arg, makeFresh(arg.coqString + "_type"))}

        // scan left to collect heads...

        val allParamMap: Map[CoqIdentifier, CoqExpression] = (allParams :+ (returnTypeName, returnType)).toMap

        //important to keep order
        val allParamNames: Seq[CoqIdentifier] = (allParams map (_._1)) :+ returnTypeName

        val dependsOn: Map[CoqIdentifier, Seq[CoqIdentifier]] =
        (allParamNames zip allParamNames.scanLeft(Seq[CoqIdentifier]()) {(l,a) => l :+ a}).toMap

        val fullType: Map[CoqIdentifier, CoqExpression] =
          allParamMap map {
            case (x,tpe) => if (dependentParamNames contains x)
              (x, dependentParamNames(x)(dependsOn(x):_*))
              else
              (x, tpe)
          }

        val argDefs: Seq[CoqCommand] = dependentParams.toSeq map { case (x, body) =>
          NormalDefinition(dependentParamNames(x), dependsOn(x) map(y => (y, fullType(y))), typeSort, body) $
          RawCommand(s"#[export] Hint Unfold ${dependentParamNames(x).coqString}: core.\n\n")
        }

        val oldRewriteTactic = rewriteTactic
        val newRewriteTactic = makeFresh("rwrtTac")
        val phaseA = makeFresh("rwrtTac_A")
        val phaseB = makeFresh("rwrtTac_B")
        rewriteTactic = newRewriteTactic

        val ids = (tparams ++ params) map (_._1)


        val h1 = makeFresh("H1")
        val h2 = makeFresh("H2")
        val u = makeFresh("U")

        val label = poseNew(Mark(ids, "unfolding " + funName.coqString + "_equation"))
        val markedUnfolding = Marked(ids.map(CoqUnboundIdentifier(_)), "unfolding " + funName.coqString + "_equation")
        val rwrtTarget = CoqContext(CoqApplication(funName, ids.map(id => CoqUnboundIdentifier(id))))

        val let =
          CoqSequence(Seq(
            poseNew(Mark(ids, "unfolded " + funName.coqString + "_equation")),
            CoqLibraryConstant("add_equation")
              (CoqApplication(CoqLibraryConstant(s"${funName.coqString}_equation_1"), ids))
          ))

        SeparatorComment(s"Start of ${fd.id.name}") $
        RawCommand(s"Obligation Tactic := ${idtac.coqString}.") $
        manyCommands(argDefs) $
        CoqEquation(funName,
                    allParams.map {case(x, _) => (x, fullType(x)) } ,
                    fullType(returnTypeName), Seq((CoqApplication(funName, allParams map (_._1)), body)), true) $
        (if (admitObligations)
          RawCommand("\nAdmit Obligations.")
        else
          RawCommand(s"\nSolve Obligations with (repeat ${mainTactic.coqString}).")
        ) $
        RawCommand("Fail Next Obligation.\n") $
        CoqMatchTactic(phaseA, Seq(
          CoqCase(CoqTacticPattern(Map(h1 -> rwrtTarget)),
            CoqSequence(Seq(label))),
          CoqCase(CoqTacticPattern(Map(), rwrtTarget),
            CoqSequence(Seq(label)))
        )) $
        CoqMatchTactic(phaseB, Seq(
          CoqCase(CoqTacticPattern(Map(h1 -> rwrtTarget, h2 -> markedUnfolding)), let),
          CoqCase(CoqTacticPattern(Map(h2 -> markedUnfolding), rwrtTarget), let)
        )) $
        RawCommand(s"Ltac ${rewriteTactic.coqString} := ${oldRewriteTactic.coqString}; repeat ${phaseA.coqString}; repeat ${phaseB.coqString}.\n") $
        updateObligationTactic() $
        SeparatorComment(s"End of ${fd.id.name}")
      } else {
        SeparatorComment(s"Start of ${fd.id.name}") $
        NormalDefinition(makeFresh(fd.id), allParams, returnType, body) $
        RawCommand(s"#[export] Hint Unfold ${makeFresh(fd.id).coqString}: definitions.\n") $
        SeparatorComment(s"End of ${fd.id.name}")
      }
      tmp
      //if (ctx.options.findOptionOrDefault(optAdmitAll)) {
      /*if (fd.flags.contains("library")) {
        tmp $
        RawCommand("Admit Obligations.")
      } else {
        tmp
      }*/
    }
  }

  // translate a Stainless type to a Coq type
  def transformType(tpe: st.Type): CoqExpression = tpe match {
    case UnitType() => CoqUnit
    case ADTType(id, args) if (sorts.contains(id)) =>
      CoqApplication(makeFresh(id), args map transformType)
    case ADTType(id, args) =>
      refinedIdentifier(id)((args map transformType): _*)
    case TypeParameter(id,flags) =>
      ignoreFlags(tpe.toString, flags)
      CoqIdentifier(id)
    case BooleanType() => CoqBool
    case FunctionType(ts, t) =>
      val tts = ts.map(transformType)
      tts.foldRight[CoqExpression](transformType(t))
        { case (arg,acc) => Arrow(arg,acc) }
    case SetType(base) =>
      CoqSetType(transformType(base))
    case IntegerType() => CoqZ
    case BVType(_, _) =>
      ctx.reporter.warning(s"The translation to Coq currently converts the type $tpe (${tpe.getClass}) to BigInt.")
      CoqZ
    case MapType(u, v) => mapType(transformType(u), transformType(v))
    case TupleType(ts) => CoqTupleType(ts map transformType)
    case _ =>
      ctx.reporter.fatalError(s"The translation to Coq does not support the type $tpe (${tpe.getClass}).")
  }

  // finds an order in which to define the functions
  // does not work for mutually recursive functions
  // highly non optimized
  def transformFunctionsInOrder(fds: Seq[FunDef], admitObligations: Boolean = false): CoqCommand = {
    if (fds.isEmpty) NoCommand
    else {
      val f = fds.find { fd =>
        fds.forall { fd2 =>
          fd == fd2 || !transitivelyCalls(fd,fd2)
        }
      }
      f match {
        case Some(fd) =>
          transformFunction(fd, admitObligations) $ transformFunctionsInOrder(fds.filterNot(_ == fd), admitObligations)
        case None =>
          ctx.reporter.warning(s"Coq translation: mutual recursion is not supported yet (" + fds.map(_.id).mkString(",") + ").")
          NoCommand
      }
    }
  }

  def totalOrder(fds: Seq[FunDef]): Seq[FunDef] = {
    if (fds.isEmpty) Seq()
    else {
      val f = fds.find { fd =>
        fds.forall(fd2 => fd == fd2 || !transitivelyCalls(fd,fd2))
      }
      f match {
        case Some(fd) =>
          Seq(fd) ++ totalOrder(fds.filterNot(_ == fd))
        case None =>
          ctx.reporter.warning(s"Coq translation: mutual recursion is not supported yet (" + fds.map(_.id).mkString(",") + ").")
          Seq()
      }
    }
  }

  def dependentFunctions(fds: Seq[FunDef]): Seq[(FunDef, Seq[FunDef])] = {
    val to = totalOrder(fds)
    to.map((fd:FunDef) => fd -> fds.filter((fd2:FunDef) => fd != fd2 && transitivelyCalls(fd,fd2)))
  }

  def makeFilePerFunction(): Seq[(Identifier, String, CoqCommand)] = {
    // reset initial state

    val funs = p.symbols.functions.values.toSeq.sortBy(_.id.name)

    val funDeps = dependentFunctions(funs)
    funDeps
      .map {case (f, d) =>
        lastTactic = idtac
        mainTactic = initTactic
        rewriteTactic = idtac
        (f.id, makeFresh(f.id).coqString, (
          header() $
          updateObligationTactic() $
          makeTactic(p.symbols.sorts.values.toSeq)$
          manyCommands(p.symbols.sorts.values.toSeq.map(transformADT))$
          transformFunctionsInOrder(d,true) $
          transformFunction(f)))
      }

  }


  def makeTactic(adts: Seq[Definition]) = {
    NoCommand
  }

  def header(): CoqCommand = {
    RawCommand("Require Import SLC.Lib.") $
    RawCommand("Require Import SLC.PropBool.") $
    RawCommand("Require Import SLC.Booleans.") $
    RawCommand("Require Import SLC.Sets.") $
    // RawCommand("Require Import stdpp.set.") $
    // RawCommand("Require Import SLC.stdppSets.") $
    RawCommand("Require Import SLC.Tactics.") $
    RawCommand("Require Import SLC.Ints.") $
    RawCommand("Require Import SLC.Unfolding.\n") $
    RawCommand("Require Import ZArith.") $
    RawCommand("Require Import Coq.Strings.String.") $
    RawCommand("From Equations Require Import Equations.\n") $
    RawCommand("Set Program Mode.\n") $
    RawCommand("Opaque set_elem_of.") $
    RawCommand("Opaque set_union.") $
    RawCommand("Opaque set_intersection.") $
    RawCommand("Opaque set_subset.") $
    RawCommand("Opaque set_empty.") $
    RawCommand("Opaque set_singleton.") $
    RawCommand("Opaque set_difference.\n")
  }

  def transform(): CoqCommand = {
    header() $
    updateObligationTactic() $
    makeTactic(p.symbols.sorts.values.toSeq)$
    manyCommands(p.symbols.sorts.values.toSeq.map(transformADT)) $
    transformFunctionsInOrder(p.symbols.functions.values.toSeq.sortBy(_.id.name))
  }

  def getTParams(a: ADTConstructor) = a.getSort.tparams
}

object CoqEncoder {


  val freshIdName = "tmp"
  var m = Map[Identifier, CoqIdentifier] ()
  var count = Map[String, Int](("t",1))

  def makeFresh(id: Identifier): CoqIdentifier = {
    if (m.contains(id)) m(id)
    else {
      val i = count.getOrElse(id.name,0)
      val freshName = if (i == 0) id.name else id.name + i
        count = count.updated(id.name, i +1)
      val res = CoqIdentifier(new Identifier(freshName, id.id, id.globalId))
      m = m.updated(id, res)
      res
    }
  }

  def makeFresh(): CoqIdentifier = {

    val i = count.getOrElse(freshIdName,0)
    val freshName = if (i == 0) freshIdName else freshIdName + i
    count = count.updated(freshIdName, i +1)
    CoqIdentifier(FreshIdentifier(freshName))
  }

  def makeFresh(name: String): CoqIdentifier = {
    val i = count.getOrElse(name,0)
    val freshName = if (i == 0) name else name + i
    count = count.updated(name, i +1)
    CoqIdentifier(FreshIdentifier(freshName))
  }


  def deriveContradiction = RawExpression("""let contradiction: False := _ in match contradiction with end""")

  def unsupportedExpression = RawExpression("""match unsupported with end""")
  //def unsupportedExpression = RawExpression("""magic""")

  def constructorIdentifier(i: Identifier): CoqIdentifier = {
    CoqIdentifier(new Identifier(i.name + "_construct", i.id, i.globalId))
  }

  def refinedIdentifier(i: Identifier): CoqIdentifier = {
    CoqIdentifier(new Identifier(i.name + "_type", i.id, i.globalId))
  }

  def recognizer(i: Identifier): CoqIdentifier = {
    CoqIdentifier(new Identifier("is" + i.name, i.id, i.globalId))
  }

  def rawIdentifier(s: String): CoqIdentifier = {
    CoqIdentifier(new Identifier(s,0,0))
  }

  def manyCommands(l: Seq[CoqCommand]): CoqCommand = {
    if (l.isEmpty) NoCommand
    else l.tail.foldLeft(l.head)(_ $ _)
  }

  def transformProgram(program: StainlessProgram, context: inox.Context): Seq[(Identifier, String, CoqCommand)] = {
    object encoder extends CoqEncoder {
      val p = program
      val ctx = context
    }

    encoder.makeFilePerFunction() //:+ ("verif1" -> encoder.transform())
  }
}
