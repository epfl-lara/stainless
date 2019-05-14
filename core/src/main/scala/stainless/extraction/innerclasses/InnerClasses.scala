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

  val s: Trees
  val t: methods.Trees
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) extends oo.TreeTransformer { ctx =>
    override final val s: self.s.type = self.s
    override final val t: self.t.type = self.t

    import s._
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

      def withMethods(methods: Seq[FunDef]): ClassSubst = copy(methods = methods)

      /** Add required type parameters to the list of explictly given ones */
      def addNewTypeParams(tps: Seq[Type]): Seq[Type] = tps ++ newTypeParams

      /** Add required constructor parameters to the list of explictly given ones,
        * based on the current context.
        *
        * @see [[ClassSubst#addOuterRefs]]
        * @see [[Context#toScope]]
        */
      def addNewParams(params: Seq[Expr], context: Context): Seq[Expr] = {
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
      path: Path = Path.empty,                         // Current path condition
      substs: Map[Identifier, ClassSubst] = Map.empty, // Already lifted classes in scope
      currentClass: Option[ClassDef] = None,           // Enclosing class
      currentFunction: Option[FunDef] = None           // Enclosing method
    ) extends PathLike[Context] {

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

      /** Transform a local class type to a global one */
      def toGlobalType(tp: Type): ClassType = tp match {
        case lct: LocalClassType =>
          substs(lct.id).classType
        case ct: ClassType if substs.contains(ct.id) && ct.tps.size != substs(ct.id).cd.tparams.size =>
          ClassType(ct.id, substs(ct.id).addNewTypeParams(ct.tps))
        case ct: ClassType =>
          ct
      }

      def merge(that: Context): Context =
        Context(
          this.path merge that.path,
          this.substs ++ that.substs,
          that.currentClass,
          that.currentFunction
        )

      def negate: Context = this.copy(path = path.negate)
      def withBinding(p: (ValDef, Expr)): Context = this.copy(path = path.withBinding(p))
      def withBound(b: ValDef): Context = this.copy(path = path.withBound(b))
      def withCond(e: Expr): Context = this.copy(path = path.withCond(e))

      def withSubst(subst: ClassSubst) = copy(substs = substs.updated(subst.cd.id, subst))
      def withSubsts(substs: Seq[ClassSubst]) = substs.foldLeft(this)(_ withSubst _)
      def withCurrentClass(cd: ClassDef) = copy(currentClass = Some(cd))
      def withCurrentFunction(fd: FunDef) = copy(currentFunction = Some(fd))
    }

    object Context extends PathProvider[Context] {
      def empty = Context()
    }

    def liftLocalClasses(fd: FunDef, ctx: Context): FunctionResult = {
      val transformer = new LiftingTransformer
      val result = transformer.transform(fd, ctx)
      val newSymbols = transformer.result.values.toSeq map { subst =>
        (transform(subst.cd), subst.methods.map(transform))
      }
      (transform(result), newSymbols)
    }

    class LiftingTransformer extends imperative.TransformerWithPC {
      val s: self.s.type = self.s
      val t: self.s.type = self.s
      import s._

      type Env = Context
      implicit val pp = Context

      val symbols: ctx.symbols.type = ctx.symbols

      var result: Map[Identifier, ClassSubst] = Map.empty

      def transform(cd: ClassDef, ctx: Context): t.ClassDef = {
        new ClassDef(
          transform(cd.id, ctx),
          cd.tparams.map(tdef => transform(tdef, ctx)),
          cd.parents.map(ct => transform(ct, ctx).asInstanceOf[t.ClassType]),
          cd.fields.map(vd => transform(vd, ctx)),
          cd.flags.map(f => transform(f, ctx))
        ).copiedFrom(cd)
      }

      def transform(fd: FunDef, ctx: Context): t.FunDef = {
        new FunDef(
          transform(fd.id, ctx),
          fd.tparams.map(tdef => transform(tdef, ctx)),
          fd.params.map(p => transform(p, ctx)),
          transform(fd.returnType, ctx),
          transform(fd.fullBody, ctx.withCurrentFunction(fd)),
          fd.flags.map(f => transform(f, ctx))
        ).copiedFrom(fd)
      }

      override def transform(e: Expr, ctx: Context): t.Expr = e match {
        case LetClass(lcds, body) =>
          val substs = lcds.map(lift(_, ctx))
          val lifted = substs map { subst =>
            val methodCtx = ctx.withSubsts(substs).withCurrentClass(subst.cd)
            val lifted = subst.withMethods(subst.methods map (transform(_, methodCtx)))
            result = result.updated(lifted.cd.id, lifted)
            lifted
          }

          transform(body, ctx withSubsts lifted)

        case LocalClassConstructor(lct, args) =>
          val subst = ctx.substs(lct.id)
          val ct = ClassType(lct.id, subst.addNewTypeParams(lct.tps) map (transform(_, ctx))).copiedFrom(lct)
          t.ClassConstructor(ct, subst.addNewParams(args, ctx) map (transform(_, ctx))).copiedFrom(e)

        case LocalMethodInvocation(obj, m, _, tps, args) =>
          t.MethodInvocation(transform(obj, ctx), m.id, tps map (transform(_, ctx)), args map (transform(_, ctx))).copiedFrom(e)

        case LocalClassSelector(obj, sel, _) =>
          t.ClassSelector(transform(obj, ctx), sel).copiedFrom(e)

        case _ => super.transform(e, ctx)
      }

      override def transform(tp: Type, ctx: Context): t.Type = tp match {
        case lct: LocalClassType =>
          val subst = ctx.substs(lct.id)
          t.ClassType(lct.id, subst.addNewTypeParams(lct.tps) map (transform(_, ctx)))

        // We sometimes encounter a ClassType for a local class, which lacks the closed over type parameters.
        // eg. when we compute the parents of the lifted class in [[lift]].
        case ClassType(id, tps) if ctx.substs contains id =>
          val subst = ctx.substs(id)
          if (tps.size == subst.cd.tparams.size) t.ClassType(id, tps map (transform(_, ctx)))
          else t.ClassType(id, subst.addNewTypeParams(tps) map (transform(_, ctx)))

        case _ => super.transform(tp, ctx)
      }
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
    def pathConditionToInvariant(pathCondition: Expr, lcd: LocalClassDef): Option[LocalMethodDef] = {
      pathCondition match {
        case BooleanLiteral(true) => None
        case _ => Some(LocalMethodDef(
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
    def lift(lcd: LocalClassDef, context: Context): ClassSubst = {
      val pathCondition = pathToClause(context.path, lcd)

      // Compute the variables, type parameters, and outer references being closed over by the local class.
      val freeVars       = (exprOps.freeVariablesOf(lcd) ++ exprOps.variablesOf(pathCondition)).toSeq.sortBy(_.id.name)
      val freeTypeParams = exprOps.freeTypeParamsOf(lcd).toSeq.sortBy(_.id.name)
      val enclosingRef   = context.currentClass.map(cd => This(cd.typed(symbols).toType))
      val freeOuterRefs  = (enclosingRef.toSet ++ exprOps.outerThisReferences(lcd).toSet).toSeq.sortBy(_.ct.id.name)

      // New necessary fields and type parameters
      val newTypeParams  = freeTypeParams.map(TypeParameterDef(_))
      val freeVarFields  = freeVars.map(_.toVal)
      val outerRefFields = freeOuterRefs.map(r => ValDef(FreshIdentifier(s"outer${r.ct.id.name}"), context.toGlobalType(r.ct)))

      // Convert all parents to a ClassType
      val parents = lcd.parents map context.toGlobalType

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
      def liftMethod(fd: LocalMethodDef): FunDef = {
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

        new FunDef(fd.id, fd.tparams, fd.params, fd.returnType, body, fd.flags)
      }

      val methods = (localInv.toSeq ++ lcd.methods) map liftMethod

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
  }

  override protected type FunctionResult = (t.FunDef, Seq[(t.ClassDef, Seq[t.FunDef])])

  override protected val funCache: SimpleCache[s.FunDef, FunctionResult] = new SimpleCache[s.FunDef, FunctionResult]

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): FunctionResult = {
    import context._

    val optClass = fd.flags.collectFirst { case IsMethodOf(cid) => symbols.classes(cid) }
    liftLocalClasses(fd, Context(currentClass = optClass, currentFunction = Some(fd)))
  }

  override protected def registerFunctions(symbols: t.Symbols, results: Seq[FunctionResult]): t.Symbols = {
    val (functions, locals) = results.unzip
    val (localClasses, localMethods) = locals.flatten.map {
      case (cd, methods) => t.exprOps.freshenClass(cd, methods)
    }.unzip

    symbols.withClasses(localClasses).withFunctions(functions ++ localMethods.flatten)
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): t.ClassDef = {
    import context._
    context.transform((new LiftingTransformer).transform(cd, Context.empty))
  }
}

object InnerClasses {
  def apply(ts: Trees, tt: methods.Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = new InnerClasses {
    override val s: ts.type = ts
    override val t: tt.type = tt
    override val context = ctx
  }
}
