package stainless
package verification

import CoqEncoder._
import CoqExpression._

trait CoqEncoder {
  implicit val debugSection = DebugSectionCoq

  val p: StainlessProgram
  val ctx: inox.Context
  val st: stainless.trees.type = stainless.trees

  import st._
  import p.symbols._
  import p.symbols.CallGraphOrderings._

  // collect the types for which we have no definitions
  // unused for now
  var undefinedTypes = Set[Type]()

  // to give unique names to the arguments we add for preconditions
  var i = 0
  val hypName = "stainlessPrecondition"

  def freshId(): CoqIdentifier = {
    i += 1
    CoqIdentifier(FreshIdentifier(hypName + "i"))
  }

  // ignore flags with an explicit warning
  def ignoreFlags(s: String, flags: Set[Flag]) = {
    if (!flags.isEmpty)
      ctx.reporter.warning(s"Coq translation ignored flags for $s:\n" + flags.mkString(", ") + "\n")
  }

  // transform a Stainless expression into a Coq expression
  def transformTree(t: st.Expr): CoqExpression = t match {
    case MatchExpr(scrut, cases) => 
      CoqMatch(transformTree(scrut), cases.map(makeFunctionCase))
    case Variable(id,tpe,flags) =>
      ignoreFlags(t.toString, flags)
      CoqVariable(id)
    case ADT(ADTType(id, targs), args) =>
      Constructor(constructorIdentifier(id), targs.map(transformType) ++ args.map(transformTree))
    case FunctionInvocation(id, targs, args) =>
      CoqApplication(CoqIdentifier(id), targs.map(transformType) ++ args.map(transformTree))
    case Application(t, ts) =>
      CoqApplication(transformTree(t), ts.map(transformTree))
    case FiniteSet(args,tpe) =>
      CoqFiniteSet(args map transformTree, transformType(tpe))
    case SetUnion(t1,t2) => CoqSetUnion(transformTree(t1), transformTree(t2))
    case ElementOfSet(t1,t2) => CoqBelongs(transformTree(t1), transformTree(t2))
    case Or(ts) => Orb(ts map transformTree)
    case And(ts) => Andb(ts map transformTree)
    case Implies(t1,t2) => implb(transformTree(t1), transformTree(t2))
    case Equals(t1,t2) => CoqEquals(transformTree(t1), transformTree(t2))
    case BooleanLiteral(true) => TrueBoolean
    case BooleanLiteral(false) => FalseBoolean
    case ADTSelector(adt, selector) => 
      adt.getType match {
        case ADTType(_,args) => 
          val typeParameters = args.map(transformType)
          CoqApplication(CoqIdentifier(selector), typeParameters :+ transformTree(adt))
        case _ => 
          ctx.reporter.fatalError(s"The translation to Coq failed becuse $adt does not have an ADT type but ${adt.getType}.")
      }
    case Forall(args, body) =>
      val params = args.map { case vd@ValDef(id,tpe,flags) => 
        ignoreFlags(vd.toString, flags)
        (CoqIdentifier(id), transformType(tpe)) 
      }
      CoqForall(params, CoqEquals(transformTree(body),TrueBoolean))
    case _ => ctx.reporter.fatalError(s"The translation to Coq does not support expression `${t.getClass}` yet.")
  }

  // creates a case for a match expression
  def makeFunctionCase(mc: MatchCase): CoqCase = mc match {
    case MatchCase(pattern, None, rhs) => 
      CoqCase(transformPattern(pattern), transformTree(rhs))
    case _ => ctx.reporter.fatalError(s"Guard in match cases are not supported by the Coq translation yet ($mc).")
  }

  // transform patterns that appear in match cases
  def transformPattern(p: Pattern): CoqPattern = p match {
    case a@ADTPattern(_, adtType, subPatterns) => 
      val unusedTypeParameters = (1 to getTParams(adts(adtType.id)).size).map(_ => VariablePattern(None))
      InductiveTypePattern(constructorIdentifier(adtType.id), unusedTypeParameters ++ subPatterns.map(transformPattern))
    case WildcardPattern(None) => VariablePattern(None)
    case WildcardPattern(Some(ValDef(id,tpe,flags))) => 
      ignoreFlags(p.toString, flags)
      ctx.reporter.warning(s"Ignoring type $tpe in the wildcard pattern $p.")
      VariablePattern(Some(CoqIdentifier(id)))
    case _ => ctx.reporter.fatalError(s"Coq does not support patterns such as `$p` (${p.getClass}) yet.")
  }

  // transforms an ADT into an inductive type
  def transformADT(a: st.ADTDefinition): CoqCommand = {
    println("TRANSFORMING")
    println(a.asString(new PrinterOptions(printUniqueIds = true)))
    println(CoqIdentifier(a.id).coqString)
    if (a.root(p.symbols) != a) {
      ctx.reporter.debug(s"Skipping $a, since it is not the root of the ADT.")
      NoCommand
    } else {
      (a match {
        case a: st.ADTSort =>
          ignoreFlags(a.toString, a.flags)
          InductiveDefinition(
            CoqIdentifier(a.id),
            a.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) },
            a.cons.map(id => makeCase(a, p.symbols.adts(id)))
          )
        case a: st.ADTConstructor =>
          ignoreFlags(a.toString, a.flags)
          InductiveDefinition(
            CoqIdentifier(a.id),
            a.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) },
            Seq(makeCase(a, a))
          )
      }) $ 
      buildRecognizers(a) $ 
      buildSubTypes(a) $ 
      buildAccessorsForChildren(a)
    }
  }

  // Define for each constructor of an ADT a function that identifies such elements
  def buildRecognizers(a: ADTDefinition): CoqCommand = a match {
    case a: st.ADTSort =>
      manyCommands(a.cons.map(c => buildRecognizer(a,adts(c))))
    case _ =>
      buildRecognizer(a,a)
  }

  // Define a function that identifies the case of an element of an inductive type
  // and checks that the invariant holds
  def buildRecognizer(root: ADTDefinition, constructor: ADTDefinition): CoqCommand = constructor match {
    case a: st.ADTConstructor =>
      val element = rawIdentifier("src")
      val tparams = root.tparams.map(t => CoqIdentifier(t.id))
      val extraCase =
        if (root != constructor)
          Some(CoqCase(VariablePattern(None), falseProp))
        else
          None

      NormalDefinition(
        recognizer(a.id),
        a.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) } ++
          Seq((element, Constructor(CoqIdentifier(root.id), tparams))),
        propSort,
        CoqMatch(element, Seq(
          CoqCase(
            {
              val unusedTypeParameters = (1 to a.tparams.size).map(_ => VariablePattern(None))
              val unusedFields = (1 to a.fields.size).map(_ => VariablePattern(None))
              InductiveTypePattern(constructorIdentifier(constructor.id), unusedTypeParameters ++ unusedFields)
            },
              trueProp
          )) ++ extraCase
        )
      )
    case _ => NoCommand
  }
            // if (a.hasInvariant) 
            //   CoqApplication(CoqIdentifier(a.invariant.get.id), tparams :+ element)
            // else

  def buildSubTypes(a: ADTDefinition): CoqCommand = a match {
    case a: st.ADTSort =>
      manyCommands(a.cons.map(c => buildSubType(a,adts(c))))
    case a: st.ADTConstructor =>
      buildSubType(a,a)
  }

  def buildSubType(root: ADTDefinition, constructor: ADTDefinition): CoqCommand = constructor match {
    case a: st.ADTConstructor =>
      val ttparams = root.tparams.map(p => (CoqIdentifier(p.id), TypeSort))
      val tparams = root.tparams.map(t => CoqIdentifier(t.id))
      val element = rawIdentifier("src")
      println(a.invariant)
      NormalDefinition(
        refinedIdentifier(constructor.id),
        ttparams,
        TypeSort,
        Refinement(
          element,
          CoqApplication(CoqIdentifier(root.id), tparams),
          CoqApplication(recognizer(constructor.id), tparams :+ element)
        )
      )
    case _ => NoCommand
  }

  def buildAccessorsForChildren(a: ADTDefinition): CoqCommand = a match {
    case a: st.ADTSort =>
      manyCommands(a.cons.map(c => buildAccessors(a,adts(c))))
    case c: st.ADTConstructor =>
      buildAccessors(c,c)
  }

  def buildAccessors(root: ADTDefinition, constructor: ADTDefinition): CoqCommand = constructor match {
    case a: st.ADTConstructor =>
      manyCommands(a.fields.zipWithIndex.map{ case (ValDef(id,tpe,flags),i) => 
        buildAccessor(id,tpe,i,a.fields.size,root,constructor)
      })
    case _ => NoCommand
  }

  def buildAccessor(id: Identifier, tpe: Type, i: Int, n: Int, root: ADTDefinition, constructor: ADTDefinition): CoqCommand = {
    val element = rawIdentifier("src")
    val extraCase = 
      if (root != constructor)
        Some(CoqCase(VariablePattern(None), deriveContradiction))
      else
        None
    val tparams = root.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) } 

    NormalDefinition(
      CoqIdentifier(id),
        tparams ++
        Seq(((element, CoqApplication(refinedIdentifier(constructor.id), root.tparams.map(t => CoqIdentifier(t.id)))))),
      transformType(tpe),
      CoqMatch(element, 
        Seq(
          CoqCase(
            {
              val unusedTypeParameters = (1 to constructor.tparams.size).map(_ => VariablePattern(None))
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
  def makeCase(root: ADTDefinition, a: ADTDefinition) = a match { 
    case a: ADTConstructor =>
      ignoreFlags(a.toString, a.flags)
      val fieldsTypes = a.fields.map(vd => transformType(vd.tpe))
      val arrowType = fieldsTypes.foldRight[CoqExpression](
        Constructor(CoqIdentifier(root.id), root.tparams.map(t => CoqIdentifier(t.id)))) // the inductive type
        { case (field, acc) => Arrow(field, acc)} // the parameters of the constructor
      InductiveCase(constructorIdentifier(a.id), arrowType)
    case _ =>
      ctx.reporter.fatalError(s"The translation to Coq does not support $a as a constructor.")
  }



  // transform function definitions
  def transformFunction(fd: st.FunDef): CoqCommand = {
    ignoreFlags(fd.toString, fd.flags)
    val mutual = p.symbols.functions.find{ case (_,fd2) => fd != fd2 && transitivelyCalls(fd, fd2) && transitivelyCalls(fd2, fd) }
    if (mutual.isDefined)
      ctx.reporter.fatalError(s"The translation to Coq does not support mutual recursion (between ${fd.id.name} and ${mutual.get._1.name})")
    else {
      val tparams: Seq[(CoqIdentifier,CoqExpression)] = fd.tparams.map { case p => (CoqIdentifier(p.id), TypeSort) }
      val params: Seq[(CoqIdentifier,CoqExpression)] = fd.params.map { case vd => (CoqIdentifier(vd.id), transformType(vd.tpe)) }
      val body = exprOps.withoutSpecs(fd.fullBody) match {
        case None => ctx.reporter.fatalError(s"We do not support functions with empty bodies: ${fd.id.name}")
        case Some(b) => transformTree(b)
      }
      val preconditionName = freshId()
      val preconditionParam: Seq[(CoqIdentifier,CoqExpression)] = exprOps.preconditionOf(fd.fullBody) match {
        case None => Seq()
        case Some(p) => Seq((preconditionName, transformTree(p)))
      }
      val returnType = exprOps.postconditionOf(fd.fullBody) match {
        case None => transformType(fd.returnType)
        case Some(Lambda(Seq(vd), post)) => 
          Refinement(CoqIdentifier(vd.id), transformType(vd.tpe), transformTree(post))
      }
      val allParams = tparams ++ params ++ preconditionParam
      if (fd.isRecursive) {
        FixpointDefinition(CoqIdentifier(fd.id), allParams, returnType, body)
      } else {
        NormalDefinition(CoqIdentifier(fd.id), allParams, returnType, body)
      }
    }
    // ctx.reporter.internalError("The translation to Coq does not support Functions yet.")
  }



  // translate a Stainless type to a Coq type
  def transformType(tpe: st.Type): CoqExpression = tpe match {
    case ADTType(id, args) if (adts(id).root == adts(id)) => 
      CoqApplication(CoqIdentifier(id), args map transformType)
    case TypeParameter(id,flags) => 
      ignoreFlags(tpe.toString, flags)
      CoqIdentifier(id)
    case BooleanType() => CoqBool
    case FunctionType(t1, t2) => 
      val tt1 = t1.map(transformType)
      tt1.foldLeft[CoqExpression](transformType(t2))
        { case (acc,arg) => Arrow(arg,acc) }
    case SetType(base) =>
      CoqSetType(transformType(base))
    case _ => ctx.reporter.fatalError(s"The translation to Coq does not support the type $tpe (${tpe.getClass}).")
  }

  // finds an order in which to define the functions
  // does not work for mutually recursive functions
  // highly non optimized
  def transformFunctionsInOrder(fds: Seq[FunDef]): CoqCommand = {
    if (fds.isEmpty) NoCommand
    else {
      val f = fds.find { fd =>
        fds.forall { fd2 =>
          fd == fd2 || !transitivelyCalls(fd,fd2)
        }
      }
      f match {
        case Some(fd) => 
          println("found first function: " + fd.id)
          transformFunction(fd) $ transformFunctionsInOrder(fds.filterNot(_ == fd))
        case None => ctx.reporter.fatalError(s"Coq translation: mutual recursion is not supported yet (" + fds.map(_.id).mkString(",") + ").")
      }
    }
  }

  def makeTactic(adts: Seq[ADTDefinition]) = {
    NoCommand
// Ltac step := match goal with 
//   | [ H: match ?t with _ => _ end |- _ ] => destruct t
//   | [ H: ex _ _ |- _ ] => destruct H
//   | [ H: isCons _ ?L |- _ ] => is_var L; destruct L
//   | _ => 
//       unfold Cons_type in * ||
//       congruence || 
//       simpl in * || 
//       program_simpl || 
//       intuition || 
//       omega || 
//       eauto || 
//       discriminate
//   end.

// Obligation Tactic := repeat step.
  }

  def transform(): CoqCommand = {
    RequireImport("Coq.Program.Tactics") $
    RequireImport("Coq.Program.Program") $
    RequireImport("Coq.Lists.List") $
    RequireImport("Coq.Lists.ListSet") $
    RequireImport("Coq.Logic.Classical") $
    RequireImport("Omega") $
    OpenScope("bool_scope") $
    RawCommand("""Axiom classicT: forall P: Prop, P + ~P.""") $
    RawCommand( """Definition propInBool (P: Prop): bool :=
                  | if (classicT P) 
                  | then true
                  | else false.
                  |""".stripMargin) $
    RawCommand( """Definition boolInProp (b: bool): Prop := b = true.""") $
    RawCommand( """Coercion boolInProp: bool >-> Sortclass.""") $
    makeTactic(p.symbols.adts.values.toSeq) $
    manyCommands(p.symbols.adts.values.toSeq.map(transformADT)) $
    transformFunctionsInOrder(p.symbols.functions.values.toSeq)
  }

  def getTParams(a: ADTDefinition) = a match {
    case a: ADTConstructor => a.tparams
    case a: ADTSort => a.tparams
  }
}

object CoqEncoder {
  def deriveContradiction = RawExpression("""let contradiction: False := _ in match contradiction with end""")

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

  def transformProgram(program: StainlessProgram, context: inox.Context) = {
    object encoder extends CoqEncoder {
      val p = program
      val ctx = context
    }

    encoder.transform()
  }
}