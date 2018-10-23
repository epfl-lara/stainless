/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

/** Lift local classes (ie. class defined within a method body, such as eg. anonymous classes) to the top-level.
  *
  * Turns the following program
  *
  * ```scala
  * abstract class Test[A] {
  *   def test: A
  * }
  *
  * case class TopLevel[A](topField: A) {
  *   def topMethod[B](topParam: B, x: BigInt): Test[B] {
  *      require(x != 0)
  *      val foo = 42
  *      new Test[A] {
  *        def test: A = {
  *          val b = x + foo
  *          val c = topParam
  *          this.topField
  *        }
  *      }
  *   }
  * }
  * ```
  *
  * into
  *
  * ```scala
  * abstract class Test[A] {
  *   def test: A
  * }
  *
  * case class $anon[A, B](topField: A, topParam: B, x: BigInt, foo: BigInt, outer: TopLevel[A]) {
  *   require(this.x != 0)
  *   def test: A = {
  *      val b = this.x + this.foo
  *      val c = this.topParam
  *      this.topField
  *   }
  * }
  *
  * case class TopLevel[A](topField: A) {
  *   def topMethod[B](topParam: B, x: BigInt): Test[B] {
  *      require(x != 0)
  *      val foo = 42
  *      $anon(this.topField, topParam, x, foo, this)
  *   }
  * }
  * ```
  */
trait InnerClasses
  extends oo.CachingPhase
     with IdentitySorts
     with oo.SimpleClasses
     with oo.SimplyCachedClasses { self =>

  val trees: Trees
  import trees._

  val s: trees.type = trees
  val t: trees.type = trees

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) extends oo.TreeTransformer { ctx =>
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    import symbols._

    /** Represent a substitution for a lifted local class */
    case class ClassSubst(
      cd: ClassDef,               // Lifted classd
      methods: Seq[FunDef],       // Lifted methods
      newTypeParams: Seq[Type],   // New (closed over) type params
      newParams: Seq[ValDef],     // New (closed over) fields
      outerRefs: Seq[ValDef],     // Outer references
      classType: ClassType        // Type of lifted class
    ) {

      /** Add required type parameters to the list of explictly given ones */
      def withNewTypeParams(tps: Seq[Type]): Seq[Type] = tps ++ newTypeParams

      /** Add required constructor parameters to the list of explictly given ones,
        * based on the current context.
        *
        * @see [[ClassSubst#addOuterRefs]]
        * @see [[Context#toScope]]
        */
      def withNewParams(params: Seq[Expr], context: Context): Seq[Expr] = {
        val scope = context.toScope
        val realNewParams = newParams.map(p => scope.get(p.id).getOrElse(p.toVariable))
        val realOuterRefs = context.currentClass.toSeq.flatMap(addOuterRefs)

        params ++ realNewParams ++ realOuterRefs
      }

      /** For each outer ref to add to a local class constructor,
        * either pass `this` or pass down the corresponding outer ref from
        * the current class.
        */
      private def addOuterRefs(currentClass: ClassDef): Seq[Expr] = {
        val thiss = This(currentClass.typed.toType)
        outerRefs map {
          case ValDef(id, ct: ClassType, _) if currentClass.id == ct.id => thiss
          case ValDef(id, _, _) => ClassSelector(thiss, id)
        }
      }
    }

    /** The context in a which a local class is defined in */
    case class Context(
      currentClass: Option[ClassDef] = None, // Enclosing class
      currentFunction: Option[FunDef] = None // Enclosing method
    ) {

      /** Map each closed over field and parameters to the appropriate reference */
      def toScope: Map[Identifier, Expr] = {
        val fields = for {
          cd    <- currentClass.toSeq
          field <- cd.fields
          thiss = This(ClassType(cd.id, cd.typeArgs))
        } yield (field.id -> ClassSelector(thiss, field.id))

        val params = for {
          fd    <- currentFunction.toSeq
          param <- fd.params
        } yield (param.id -> param.toVariable)

        (fields ++ params).toMap
      }
    }

    /** Recursively lift the local classes in the given function,
     *  and store the resulting substitutions in `result`
      */
    def liftLocalClasses(fd: FunDef, context: Context): List[ClassSubst] = {
      class LocalClassCollector(context: Context) extends stainless.transformers.TransformerWithPC {
        val s: self.s.type = self.s
        val t: self.s.type = self.s

        type Env = Path
        implicit val pp = Path

        val symbols: ctx.symbols.type = ctx.symbols

        var result: List[ClassSubst] = List.empty

        override def transform(e: Expr, path: Path): Expr = e match {
          case LetClass(lcd, body) =>
            val lifted = lift(lcd, context, path)

            val subContext = Context(Some(lifted.cd), None)
            val subs = lifted.methods.toList.flatMap(liftLocalClasses(_, subContext))

            result = lifted :: subs ++ result

            transform(body, path)

          case _ => super.transform(e, path)
        }
      }

      val collector = new LocalClassCollector(context)
      collector.transform(fd.fullBody, Path.empty)
      collector.result
    }

    /** Collect applications of local functions with a method of a local class */
    def collectFreeLocalFunsCalls(fd: FunDef): Set[ApplyLetRec] = {
      class FreeLocalFunsCollector extends stainless.transformers.Transformer
        with inox.transformers.DefinitionTransformer {

        val s: self.s.type = self.s
        val t: self.s.type = self.s
        val symbols: ctx.symbols.type = ctx.symbols

        type Env = Set[Identifier]
        def initEnv = Set.empty

        var result: Set[ApplyLetRec] = Set.empty

        override def transform(e: Expr, env: Env): Expr = e match {
          case LetRec(fds, body) =>
            transform(body, env ++ fds.map(_.id).toSet)

          case app: ApplyLetRec if !env.contains(app.id) =>
            result = result + app
            super.transform(app, env)

          case _ => super.transform(e, env)
        }
      }

      val collector = new FreeLocalFunsCollector
      collector.transform(fd)
      collector.result
    }

    /** Check validity of given lifted local class, given its methods, and the variables it closes over. */
    def checkValidLiftedClass(cd: ClassDef, methods: Seq[FunDef], freeVars: Seq[Variable]): Unit = {
      val freeFunCalls = methods flatMap collectFreeLocalFunsCalls

      freeFunCalls foreach { app =>
        throw InvalidInnerClassException(app, s"Local classes cannot close over local function definitions")
      }

      freeVars.filter(_.flags contains IsVar) foreach { v =>
        throw InvalidInnerClassException(v, s"Local classes cannot close over mutable variables")
      }
    }

    /** Current path condition expressed as a class invariant, if not trivial */
    def pathConditionToInvariant(pathCondition: Expr, lcd: LocalClassDef): Option[FunDef] = {
      pathCondition match {
        case BooleanLiteral(true) => None
        case _ => Some(new FunDef(
          ast.SymbolIdentifier("inv"),
          Seq.empty,
          Seq.empty,
          BooleanType().setPos(lcd),
          pathCondition.setPos(lcd),
          Seq(IsInvariant, IsMethodOf(lcd.id))
        ).setPos(lcd))
      }
    }

    /** Convert the path condition to a (properly positioned) expression */
    def pathToClause(path: Path, lcd: LocalClassDef): Expr = {
      val pathCondition = path.toClause
      exprOps.postTraversal(_.setPos(lcd))(pathCondition)
      pathCondition
    }

    /** Lift the local class to the top, taking into account the current context and path */
    def lift(lcd: LocalClassDef, context: Context, path: Path): ClassSubst = {
      val pathCondition = pathToClause(path, lcd)

      // Compute the variables, type parameters, and outer references being closed over by the local class.
      val freeVars       = (exprOps.freeVariablesOf(lcd) ++ exprOps.variablesOf(pathCondition)).toSeq.sortBy(_.id.name)
      val freeTypeParams = exprOps.freeTypeParamsOf(lcd).toSeq.sortBy(_.id.name)
      val enclosingRef   = context.currentClass.map(cd => This(cd.typed(symbols).toType))
      val freeOuterRefs  = (enclosingRef.toSet ++ exprOps.outerThisReferences(lcd).toSet).toSeq.sortBy(_.ct.id.name)

      // New necessary fields and type parameters
      val newTypeParams  = freeTypeParams.map(TypeParameterDef(_))
      val freeVarFields  = freeVars.map(_.toVal)
      val outerRefFields = freeOuterRefs.map(r => ValDef(FreshIdentifier(s"outer${r.ct.id.name}"), r.ct))

      // Convert all parents to a ClassType
      val parents = lcd.parents map {
        case ct: ClassType       => ct
        case lct: LocalClassType => lct.toClassType
      }

      // Build the new class
      val cd = new ClassDef(
        lcd.id,
        lcd.tparams ++ newTypeParams,
        parents,
        lcd.fields ++ freeVarFields ++ outerRefFields,
        lcd.flags
      ).copiedFrom(lcd)

      // Convert the current path condition to an invariant
      val localInv = pathConditionToInvariant(pathCondition, lcd)

      val classType = ClassType(lcd.id, cd.typeArgs)

      // Map each free variable to the corresponding field selector
      val freeVarsMap = freeVars.zip(freeVarFields).map { case (v, vd) =>
        v -> ClassSelector(This(classType), vd.id).copiedFrom(v)
      }.toMap

      // Map each outer reference to the corresponding field selector
      val freeOuterRefsMap = freeOuterRefs.zip(outerRefFields).map { case (thiss, vd) =>
        thiss.ct -> ClassSelector(This(classType), vd.id).copiedFrom(thiss)
      }.toMap

      /** Rewrite the given method to access free variables through the new fields,
        * and to supply the proper arguments when constructing an instance of its own class.
        */
      def liftMethod(fd: FunDef): FunDef = {
        val body = exprOps.preMap {
          case v: Variable if freeVarsMap contains v =>
            Some(freeVarsMap(v))

          case a @ Assignment(v, e) if freeVarsMap contains v =>
            val ClassSelector(rec, sel) = freeVarsMap(v)
            Some(FieldAssignment(rec, sel, e).copiedFrom(a))

          case thiss: This if freeOuterRefsMap contains thiss.ct =>
            Some(freeOuterRefsMap(thiss.ct))

          case lcc @ LocalClassConstructor(lct, args) if lct.id == lcd.id =>
            val ct = ClassType(lcd.id, lct.tps ++ newTypeParams.map(_.tp))
            Some(ClassConstructor(ct, args ++ freeVars ++ freeOuterRefs).copiedFrom(lcc))

          case _ => None
        } (fd.fullBody)

        fd.copy(fullBody = body)
      }

      val methods = (localInv.toSeq ++ lcd.methods.map(_.toFunDef)) map liftMethod

      checkValidLiftedClass(cd, methods, freeVars)

      ClassSubst(
        cd,
        methods,
        freeTypeParams,
        freeVars.map(_.toVal),
        outerRefFields,
        classType
      )
    }

    /** Remove any references to local classes, using the given substitutions */
    class LoweringTransformer(classSubsts: Map[Identifier, ClassSubst], context: Context) extends oo.TreeTransformer {
      val s: self.s.type = self.s
      val t: s.type = s
      import s._

      override def transform(tp: Type): Type = tp match {
        case lct: LocalClassType =>
          val subst = classSubsts(lct.id)
          ClassType(lct.id, subst.withNewTypeParams(lct.tps) map transform)

        // We sometimes encounter a ClassType for a local class, which lacks the closed over type parameters.
        // eg. when we compute the parents of the lifted class in [[lift]].
        case ClassType(id, tps) if classSubsts contains id =>
          val subst = classSubsts(id)
          if (tps.size == subst.cd.tparams.size) ClassType(id, tps map transform)
          else ClassType(id, subst.withNewTypeParams(tps) map transform)

        case _ => super.transform(tp)
      }

      override def transform(e: Expr): Expr = e match {
        case LetClass(_, body) => transform(body)

        case LocalClassConstructor(lct, args) =>
          val subst = classSubsts(lct.id)
          val ct = ClassType(lct.id, subst.withNewTypeParams(lct.tps) map transform).copiedFrom(lct)
          ClassConstructor(ct, subst.withNewParams(args, context) map transform).copiedFrom(e)

        case LocalMethodInvocation(obj, m, _, tps, args) =>
          MethodInvocation(transform(obj), m.id, tps map transform, args map transform).copiedFrom(e)

        case LocalClassSelector(obj, sel, _) =>
          ClassSelector(transform(obj), sel).copiedFrom(e)

        case _ => super.transform(e)
      }
    }
  }

  override protected type FunctionResult = (t.FunDef, Seq[(t.ClassDef, Seq[t.FunDef])])

  override protected val funCache: SimpleCache[s.FunDef, FunctionResult] = new SimpleCache[s.FunDef, FunctionResult]

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult = {
    import context._

    val optClass = fd.flags.collectFirst { case IsMethodOf(cid) => symbols.classes(cid) }
    val classSubsts = liftLocalClasses(fd, Context(currentClass = optClass))
    val classMap = classSubsts.map(s => s.cd.id -> s).toMap

    // Lower a method from a top-level class
    def lowerFun(fd: FunDef): FunDef = {
      val optClass = fd.flags.collectFirst { case IsMethodOf(cid) => symbols.classes(cid) }
      val lowering = new LoweringTransformer(classMap, Context(optClass, Some(fd)))
      lowering.transform(fd)
    }

    // Lower a class, top-level or not
    def lowerClass(cd: ClassDef): ClassDef = {
      val lowering = new LoweringTransformer(classMap, Context())
      lowering.transform(cd)
    }

    // Lower a local method
    def lowerLocalMethod(fd: FunDef, cd: ClassDef): FunDef = {
      val lowering = new LoweringTransformer(classMap, Context(Some(cd), Some(fd)))
      lowering.transform(fd)
    }

    // Lower all found local classes and their methods,
    // and freshen their fields, parameters, and type parameters
    val locals = classSubsts.map { s =>
      val cd = lowerClass(s.cd)
      val methods = s.methods map (fd => lowerLocalMethod(fd, cd))
      exprOps.freshenClass(cd, methods)
    }.toSeq

    (lowerFun(fd), locals)
  }

  override protected def registerFunctions(symbols: t.Symbols, results: Seq[FunctionResult]): t.Symbols = {
    val (functions, locals) = results.unzip
    val (localClasses, localMethods) = locals.flatten.unzip

    symbols.withClasses(localClasses).withFunctions(functions ++ localMethods.flatten)
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = {
    import context._
    val lowering = new LoweringTransformer(Map.empty, Context())
    lowering.transform(cd)
  }
}

object InnerClasses {
  def apply(tr: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tr.type
    val t: tr.type
  } = new {
    override val trees: tr.type = tr
  } with InnerClasses {
    override val context = ctx
  }
}
