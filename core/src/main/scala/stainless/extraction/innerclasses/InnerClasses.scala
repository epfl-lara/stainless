/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

/** Lift local classes (ie. class defined within a method body,
  * such as eg. anonymous classes) to the top-level.
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
class InnerClasses(override val s: Trees, override val t: methods.Trees)
                  (using override val context: inox.Context)
  extends oo.CachingPhase
     with oo.NoSummaryPhase
     with IdentitySorts
     with oo.IdentityTypeDefs
     with oo.SimpleClasses
     with oo.SimplyCachedClasses { self =>
  import s._

  override protected def getContext(symbols: Symbols) = new TransformerContext(self.s, self.t)(using symbols)

  protected class TransformerContext(override final val s: self.s.type,
                                     override final val t: self.t.type)
                                    (using val symbols: s.Symbols)
    extends oo.ConcreteTreeTransformer(s, t) { ctx =>
    import s._
    import symbols._

    /** Represent a substitution for a lifted local class */
    case class ClassSubst(
      cd: ClassDef,               // Lifted class
      methods: Seq[FunDef],       // Lifted methods
      typeMembers: Seq[TypeDef],  // Lifted type members
      // Closed over type params: the first element of the tuple corresponds to the captured free type parameter
      // while the second to the freshened type parameter.
      newTypeParams: Seq[(TypeParameter, TypeParameterDef)],
      // Closed over fields: the first element of the tuple corresponds to the captured free variable
      // while the second to the freshened ValDef.
      newParams: Seq[(Variable, ValDef)],
      outerRefs: Seq[ValDef],     // Outer references
      classType: ClassType        // Type of lifted class
    ) {

      def withMethods(methods: Seq[FunDef]): ClassSubst = copy(methods = methods)
      def withTypeMembers(typeMembers: Seq[TypeDef]): ClassSubst = copy(typeMembers = typeMembers)

      /** Add required type parameters to the list of explicitly given ones */
      def addNewTypeParams(tps: Seq[Type], context: Context): Seq[Type] = {
        val scope = context.typeScope
        val realNewTyParams = newTypeParams.map((freeTyParam, _) => scope.getOrElse(freeTyParam, freeTyParam))

        tps ++ realNewTyParams
      }

      /** Add required constructor parameters to the list of explictly given ones,
        * based on the current context.
        *
        * @see [[ClassSubst#addOuterRefs]]
        * @see [[Context#toScope]]
        */
      def addNewParams(params: Seq[Expr], context: Context): Seq[Expr] = {
        val scope = context.termScope
        val realNewParams = newParams.map((freeVar, _) => scope.getOrElse(freeVar.id, freeVar))
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
          case ValDef(_, ct: ClassType, _) if currentClass.id == ct.id => thiss
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

      /** Map each closed over free variable and parameters to the appropriate reference */
      def termScope: Map[Identifier, Expr] = {
        val params = for {
          fd    <- currentFunction.toSeq
          param <- fd.params
        } yield param.id -> param.toVariable

        val fields = for {
          cd    <- currentClass.toSeq
          subst = substs.values.find(_.cd eq cd).get // Enclosing class is already lifted, so it must be in `substs`
          (freeVar, field) <- subst.newParams
          thiss = This(ClassType(cd.id, cd.typeArgs).copiedFrom(field)).copiedFrom(field)
        } yield freeVar.id -> ClassSelector(thiss, field.id).copiedFrom(field)

        (params ++ fields).toMap
      }

      /** Map each closed over free type parameter to the appropriate reference */
      def typeScope: Map[TypeParameter, Type] = {
        val fromFn = for {
          fd     <- currentFunction.toSeq
          tparam <- fd.tparams
        } yield tparam.tp -> tparam.tp

        val fromClass = for {
          cd    <- currentClass.toSeq
          subst = substs.values.find(_.cd eq cd).get // Enclosing class is already lifted, so it must be in `substs`
          (freeTParam, tparamDef) <- subst.newTypeParams
        } yield freeTParam -> tparamDef.tp

        (fromFn ++ fromClass).toMap
      }

      /** Transform a local class type to a global one */
      def toGlobalType(tp: Type): ClassType = tp match {
        case lct: LocalClassType =>
          substs(lct.id).classType
        case ct: ClassType if substs.contains(ct.id) && ct.tps.size != substs(ct.id).cd.tparams.size =>
          val subst = substs(ct.id)
          val tps = ct.tps ++ subst.newTypeParams.map(_._2.tp)
          ClassType(ct.id, tps).copiedFrom(ct)
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
      val lift = new LiftingTransformer
      val result = lift.transform(fd, ctx)
      val derived = Derived(Some(fd.id))

      val newSymbols = lift.result.values.toSeq map { subst =>
        val cd = transform(subst.cd.copy(flags = subst.cd.flags :+ derived))
        val methods = subst.methods
          .map(fd => fd.copy(flags = fd.flags :+ derived))
          .map(transform)
        val typeDefs = subst.typeMembers
          .map(td => td.copy(flags = td.flags :+ derived))
          .map(transform)

        (cd, methods, typeDefs)
      }

      (transform(result), newSymbols)
    }

    class LiftingTransformer(override val s: self.s.type, override val t: self.s.type)
                            (using override val symbols: ctx.symbols.type)
      extends imperative.TransformerWithPC {
      import s._

      def this() = this(self.s, self.s)(using ctx.symbols)

      type Env = Context
      val pp = Context

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

      private def flattenLets(e: Expr): (Seq[LocalClassDef], Seq[LocalFunDef], Expr) = {
        def rec(e: Expr)(classes: Seq[LocalClassDef], funs: Seq[LocalFunDef]): (Seq[LocalClassDef], Seq[LocalFunDef], Expr) = {
          e match {
            case LetClass(lcds, body) => rec(body)(classes ++ lcds, funs)
            case LetRec(lfds, body) => rec(body)(classes, funs ++ lfds)
            case other => (classes, funs, other)
          }
        }

        rec(e)(Seq.empty, Seq.empty)
      }

      override def transform(e: Expr, ctx: Context): t.Expr = e match {
        case e: LetClass =>
          val (localClasses, localFunDefs, body) = flattenLets(e)
          val substs = localClasses.map(lift(_, ctx))
          val lifted = substs map { subst =>
            val methodCtx = ctx.withSubsts(substs).withCurrentClass(subst.cd)
            val lifted = subst.withMethods(subst.methods map (transform(_, methodCtx)))
            result = result.updated(lifted.cd.id, lifted)
            lifted
          }

          transform(LetRec(localFunDefs, body).copiedFrom(e), ctx withSubsts lifted)

        case LocalThis(lct) =>
          val subst = ctx.substs(lct.id)
          val ct = ClassType(lct.id, subst.addNewTypeParams(lct.tps, ctx) map (transform(_, ctx))).copiedFrom(lct)
          t.This(ct).copiedFrom(e)

        case LocalClassConstructor(lct, args) =>
          val subst = ctx.substs(lct.id)
          val ct = ClassType(lct.id, subst.addNewTypeParams(lct.tps, ctx) map (transform(_, ctx))).copiedFrom(lct)
          t.ClassConstructor(ct, subst.addNewParams(args, ctx) map (transform(_, ctx))).copiedFrom(e)

        case LocalMethodInvocation(obj, m, _, tps, args) =>
          t.MethodInvocation(transform(obj, ctx), m.id, tps map (transform(_, ctx)), args map (transform(_, ctx))).copiedFrom(e)

        case LocalClassSelector(obj, sel, _) =>
          t.ClassSelector(transform(obj, ctx), sel).copiedFrom(e)

        case _ =>
          super.transform(e, ctx)
      }

      override def transform(tp: Type, ctx: Context): t.Type = tp match {
        case lct: LocalClassType =>
          val subst = ctx.substs(lct.id)
          t.ClassType(lct.id, subst.addNewTypeParams(lct.tps, ctx) map (transform(_, ctx))).copiedFrom(tp)

        // We sometimes encounter a ClassType for a local class, which lacks the closed over type parameters.
        // eg. when we compute the parents of the lifted class in [[lift]].
        case ClassType(id, tps) if ctx.substs contains id =>
          val subst = ctx.substs(id)
          if (tps.size == subst.cd.tparams.size) t.ClassType(id, tps map (transform(_, ctx))).copiedFrom(tp)
          else t.ClassType(id, subst.addNewTypeParams(tps, ctx) map (transform(_, ctx))).copiedFrom(tp)

        case _ => super.transform(tp, ctx)
      }
    }

    /** Collect applications of local functions with a method of a local class */
    def collectFreeLocalFunsCalls(fd: FunDef): Set[ApplyLetRec] = {
      class FreeLocalFunsCollector(override val s: self.s.type, override val t: self.s.type)
        extends stainless.transformers.Transformer
           with inox.transformers.DefinitionTransformer {
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

      val collector = new FreeLocalFunsCollector(self.s, self.s)
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
    def pathConditionToInvariant(path: Path, lcd: LocalClassDef): Option[LocalMethodDef] = {
      pathToClause(path, lcd) match {
        case BooleanLiteral(true) => None
        case pc => Some(LocalMethodDef(
          ast.SymbolIdentifier("inv"),
          Seq.empty,
          Seq.empty,
          BooleanType().setPos(lcd),
          pc.setPos(lcd),
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
      val pc = context.path
      // Compute the variables, type parameters, and outer references being closed over by the local class.
      // Free variables that are actually defined in a let-binding of the PC will not be transformed into a field.
      // Instead, these will be introduced in the body of each method, akin to what is done in FunctionClosure#closeFd.
      // For example, if we have:
      //   def test(x: BigInt): Unit = {
      //      require(x > 10)
      //      val y = x + 10
      //      // The PC is `x > 10 && let y = x + 10 in true`
      //      case class Local() {
      //        def hello: Unit = {
      //          assert(x > 10)  // OK
      //          assert(y > 20)  // OK
      //        }
      //        def empty: Unit = ()
      //      }
      //   }
      // Then we hoist `Local` as follows:
      //   case class Local(x: BigInt) {
      //     @invariant
      //     def inv: Boolean = {
      //       this.x > 10 &&
      //       { val y = x + 10; true } // Note that we do not remove unused let-binding (but could do so)
      //     }
      //     // Note that `y` is not translated into a field, only `x`
      //     // because `y` is a bound variable in the original VC
      //     def hello: Unit = {
      //       val y = @DropVCs (x + 10)
      //       assert(x > 10)  // OK
      //       assert(y > 20)  // OK
      //     }
      //     def empty: Unit = {
      //       val y = @DropVCs (x + 10)
      //     }
      //   }
      //   // `test` is transformed as usual
      val allFreeVars      = (exprOps.freeVariablesOf(lcd) ++ exprOps.variablesOf(pc.toClause))
                                .toSeq.sortBy(_.id.name)
      val freeVarsAsFields = allFreeVars.filterNot(v => pc.bindings exists (_._1.id == v.id))
      val freeTypeParams   = exprOps.freeTypeParamsOf(lcd).toSeq.sortBy(_.id.name)
      val enclosingRef     = context.currentClass.map(cd => This(cd.typed(using symbols).toType))
      val freeOuterRefs    = (enclosingRef.toSet ++ exprOps.outerThisReferences(lcd).toSet).toSeq.sortBy(_.ct.id.name)

      // New necessary fields and type parameters
      val newTypeParams  = freeTypeParams.map(tp => TypeParameterDef(tp.freshen))

      // Substitute the free type parameters to their freshened counterpart.
      class TyMap extends TreeTransformer { mapSlf =>
        override val s: self.s.type = self.s
        override val t: self.s.type = self.s
        override def transform(ty: mapSlf.s.Type): mapSlf.t.Type = ty match {
          case t: mapSlf.s.TypeParameter if freeTypeParams.indexOf(t) >= 0 =>
            newTypeParams(freeTypeParams.indexOf(t)).tp
          case t =>
            super.transform(t)
        }
        override def transform(e: mapSlf.s.Expr): mapSlf.t.Expr = e match {
          // We need to explicitly transform LetClass to ensure we go through in each local methods
          // because the deconstructor of LetClass does not deconstruct local methods.
          case mapSlf.s.LetClass(classes, body) =>
            LetClass(classes.map(transform), transform(body))
          case e =>
            super.transform(e)
        }
      }
      val tyMap = new TyMap

      val newVarFields  = freeVarsAsFields.map(_.toVal.freshen).map(tyMap.transform)
      val outerRefFields = freeOuterRefs.map { r =>
        ValDef(FreshIdentifier(s"outer${r.ct.id.name}"), context.toGlobalType(r.ct)).setPos(lcd.getPos)
      }.map(tyMap.transform)

      // Convert all parents to a ClassType
      val parents = lcd.parents.map(p => tyMap.transform(context.toGlobalType(p)).asInstanceOf[ClassType])

      // Build the new class
      val cd = new ClassDef(
        lcd.id,
        lcd.tparams ++ newTypeParams,
        parents,
        lcd.fields.map(tyMap.transform) ++ newVarFields ++ outerRefFields,
        lcd.flags
      ).copiedFrom(lcd)

      val classType = ClassType(lcd.id, cd.typeArgs)

      // Map each free variable to the corresponding field selector
      val freeVarsAsFieldsMap = freeVarsAsFields.zip(newVarFields).map { case (v, vd) =>
        v -> ClassSelector(This(classType).copiedFrom(v), vd.id).copiedFrom(v)
      }.toMap

      // Map each outer reference to the corresponding field selector
      val freeOuterRefsMap = freeOuterRefs.zip(outerRefFields).map { case (thiss, vd) =>
        thiss.ct.id -> ClassSelector(This(classType).copiedFrom(thiss), vd.id).copiedFrom(thiss)
      }.toMap

      /** Rewrite the given method to access free variables through the new fields,
        * and to supply the proper arguments when constructing an instance of its own class.
        * Introduces fresh local variables for let-bound variables in PC, and rewrite the given
        * method to use these locals.
        */
      def liftMethod(fd: LocalMethodDef): FunDef = {
        // We do something similar to what is done in FunctionClosure#closeFd, where we transform
        // each let-binding of the PC in Expr let-binding.
        // However, we do not need to do something about Path.Element.Condition (for the above example, `this.x > 10`),
        // as these are already "handled" by the ADT invariant.
        val body = Path.fold[Expr](fd.fullBody, {
          case (vd, e, acc) => Let(vd, annotated(e, DropVCs), acc).setPos(fd.fullBody)
        }, (_, acc) => acc)(pc.elements)

        doLiftMethod(fd.copy(fullBody = body))
      }

      def doLiftMethod(fd: LocalMethodDef): FunDef = {
        val freshBindings = pc.bindings.map(p => p._1.toVariable -> p._1.toVariable.freshen).toMap
        val body = exprOps.preMap {
          case v: Variable if freeVarsAsFieldsMap contains v =>
            Some(freeVarsAsFieldsMap(v))

          case v: Variable if freshBindings contains v =>
            Some(freshBindings(v))

          case Let(vd, e, rest) if freshBindings contains vd.toVariable =>
            Some(Let(freshBindings(vd.toVariable).toVal, e, rest))

          case a @ Assignment(v, e) if freeVarsAsFieldsMap contains v =>
            val ClassSelector(rec, sel) = freeVarsAsFieldsMap(v)
            Some(FieldAssignment(rec, sel, e).copiedFrom(a))

          case thiss: This if freeOuterRefsMap contains thiss.ct.id =>
            Some(freeOuterRefsMap(thiss.ct.id))

          case thiss: LocalThis if freeOuterRefsMap contains thiss.lct.id =>
            Some(freeOuterRefsMap(thiss.lct.id))

          case lcc @ LocalClassConstructor(lct, args) if lct.id == lcd.id =>
            val ct = ClassType(lcd.id, lct.tps ++ newTypeParams.map(_.tp))
            Some(ClassConstructor(ct, args ++ freeVarsAsFields ++ freeOuterRefs).copiedFrom(lcc))

          case _ => None
        } (fd.fullBody)

        tyMap.transform(new FunDef(fd.id, fd.tparams, fd.params, fd.returnType, body, fd.flags).copiedFrom(fd))
      }

      // Convert the current path condition to an invariant
      val localInv = pathConditionToInvariant(pc, lcd)
      // Because the invariant already contains the let-bound variables in its body,
      // we do not want to introduce them again and therefore use doLiftMethod instead.
      val methods = (localInv.toSeq map doLiftMethod) ++ (lcd.methods map liftMethod)
      val typeMembers = lcd.typeMembers map (_.toTypeDef) map tyMap.transform

      // We use allFreeVars to ensure no mutable variable is captured
      checkValidLiftedClass(cd, methods, allFreeVars)

      ClassSubst(
        cd,
        methods,
        typeMembers,
        freeTypeParams zip newTypeParams,
        freeVarsAsFields zip newVarFields,
        outerRefFields,
        classType
      )
    }
  }

  override protected type FunctionResult = (t.FunDef, Seq[(t.ClassDef, Seq[t.FunDef], Seq[t.TypeDef])])

  override protected val funCache: SimpleCache[s.FunDef, (FunctionResult, FunctionSummary)] = new SimpleCache

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): (FunctionResult, FunctionSummary) = {
    import context.{given, _}

    val optClass = fd.flags.collectFirst { case IsMethodOf(cid) => symbols.classes(cid) }
    (liftLocalClasses(fd, Context(currentClass = optClass, currentFunction = Some(fd))), ())
  }

  override protected def registerFunctions(symbols: t.Symbols, results: Seq[FunctionResult]): t.Symbols = {
    val (functions, locals) = results.unzip
    val (localClasses, localMethods, localTypeDefs) = locals.flatten.unzip3
    symbols
      .withClasses(localClasses)
      .withTypeDefs(localTypeDefs.flatten)
      .withFunctions(functions ++ localMethods.flatten)
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (t.ClassDef, ClassSummary) = {
    import context.{given, _}
    (context.transform((new LiftingTransformer).transform(cd, Context.empty)), ())
  }
}

object InnerClasses {
  def apply(ts: Trees, tt: methods.Trees)(using inox.Context): ExtractionPipeline {
    val s: ts.type
    val t: tt.type
  } = {
    class Impl(override val s: ts.type, override val t: tt.type) extends InnerClasses(s, t)
    new Impl(ts, tt)
  }
}
