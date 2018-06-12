/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

import scala.collection.{mutable => scm}

trait InnerClasses extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: methods.Trees

  private[this] implicit class TypeParamOps(val tp: s.TypeParameter) {
    def toDef: s.TypeParameterDef = s.TypeParameterDef(tp)
  }

  private[this] implicit class SeqOps[A](val seq: Seq[A]) {
    // I know, mutation..., but here it's local and fast :)
    def distinctBy[B](f: A => B): Seq[A] = {
      val contents = scm.Set.empty[B]
      seq filter { el =>
        val discr = f(el)
        val seen = contents contains discr
        contents += discr
        !seen
      }
    }
  }

  def transform(syms: s.Symbols): t.Symbols = {
    import s._
    import syms.Path

    case class LocalClassContext(lcd: LocalClassDef, path: Path, tparams: Set[TypeParameterDef])

    case class LiftedClass(
      cd: ClassDef,
      newArgs: Seq[Expr],
      methods: Seq[FunDef],
      localClassType: ClassType
    )

    def liftLocalClass(lCtx: LocalClassContext): (Identifier, LiftedClass) = {
      val LocalClassContext(lcd, path, tctx) = lCtx

      // Convert the path condition to a (positioned) expression
      val pathCondition = path.toClause
      exprOps.postTraversal(_.setPos(lcd))(pathCondition)

      // Current path condition expressed as a class invariant, if not trivial
      val localInv = pathCondition match {
        case BooleanLiteral(true) => None
        case _ => Some(new FunDef(
          ast.SymbolIdentifier("inv"),
          Seq.empty,
          Seq.empty,
          BooleanType().setPos(lcd),
          pathCondition,
          Seq(IsInvariant, IsMethodOf(lcd.cd.id))
        ).setPos(lcd))
      }

      // Collect all free fields in the methods
      val freeFields = (lcd.methods.flatMap { fd =>
        exprOps.collect[(ValDef, ClassType)] {
          case cs @ ClassSelector(This(outerClassType), id) if !lcd.fields.exists(_.id == id) =>
            Set(ValDef(id, cs.getType(syms)) -> outerClassType)
          case _ => Set()
        } (fd.fullBody)
      }).distinctBy(_._1.id).sortBy(_._1.id)

      // Collect all free variables in the methods
      val methodsFreeVars = lcd.methods.flatMap { fd =>
        exprOps.variablesOf(fd.fullBody).map(_.toVal) -- fd.params.toSet
      }

      // Collect free variables of the local invariant
      val invFreeVars = localInv.map { inv =>
        exprOps.variablesOf(inv.fullBody).map(_.toVal)
      }.getOrElse(Seq.empty)

      val freeVariables = (methodsFreeVars ++ invFreeVars).distinctBy(_.id).sortBy(_.id)
      val freeDefs = freeFields.map(_._1) ++ freeVariables

      val newFields = freeDefs.map(_.freshen)
      val newVarArgs = freeVariables.map(_.toVariable)
      val newFieldArgs = freeFields map { case (vd, ct) => ClassSelector(This(ct), vd.id) }
      val newArgs = newFieldArgs ++ newVarArgs

      // Collect all free type parameters of all parents, minus the local class's own
      val parentsTypeParams = lcd.cd.parents.toSet.flatMap(typeOps.typeParamsOf).map(TypeParameterDef(_)) -- lcd.cd.tparams.toSet
      val freeTypeParams = (tctx ++ parentsTypeParams).toSeq.distinctBy(_.id).sortBy(_.id)

      // Lift as a toplevel class with additional fields and type parameters
      val liftedClass = lcd.cd.copy(
        fields = lcd.cd.fields ++ newFields,
        tparams = lcd.cd.tparams ++ freeTypeParams
      )

      // Figure out which type parameters from the context need to be supplied to the constructor
      val relevantTypeParams = tctx.toSeq.sortBy(_.id).filter(liftedClass.tparams.contains)

      val typedClass = liftedClass.typed(syms)
      val localTypedClass = liftedClass.typed(relevantTypeParams.map(_.tp))(syms)

      // Rewrite any access to a free variable of the class into a field access.
      // Can't use replaceFromSymbols for some reason as it seems that the typed
      // of the free variables in the invariant are sometimes not `==` to the ones
      // in the methods, although they are of the same types.
      val subst = (freeDefs map (_.id) zip newFields).toMap
      val newMethods = (localInv.toSeq ++ lcd.methods).map { fd =>
        val body = exprOps.preMap {
          case Assignment(v, e) if subst contains v.id =>
            throw new MissformedStainlessCode(v, "Local classes cannot mutate closed-over variables")

          case v: Variable if subst contains v.id =>
            Some(ClassSelector(This(typedClass.toType), subst(v.id).id))

          case ClassSelector(This(_), id) if subst contains id =>
            Some(ClassSelector(This(typedClass.toType), subst(id).id))

          case _ => None
        } (fd.fullBody)

        fd.copy(fullBody = body)
      }

      liftedClass.id -> LiftedClass(liftedClass, newArgs, newMethods, localTypedClass.toType)
    }

    class LocalClassesCollector(tparams: Set[TypeParameterDef]) extends transformers.CollectorWithPC { self =>
      val trees: s.type = s
      val symbols: syms.type = syms
      import trees._

      type Result = LocalClassContext

      protected def step(e: Expr, path: Env): List[Result] = e match {
        case LetClass(lcd, _) => List(LocalClassContext(lcd, path, tparams))
        case LetRec(fds, body) => fds.toList flatMap { fd =>
          val collector = new LocalClassesCollector(tparams ++ fd.tparams) {
            override def initEnv = path
          }
          collector.collect(fd.body)
        }
        case _ => Nil
      }
    }

    // Because of how CollectorWithPC works (we don't control the recursion),
    // we end up collecting many times over the local class defs,
    // with a varying number of free type parameters. We must pick
    // the one with the most of them, ie. the one collected by `collector` in the
    // `LocalClassesCollector#step`.
    def collectLocalClassDefs(fd: FunDef): Seq[LocalClassContext] = {
      new LocalClassesCollector(fd.tparams.toSet)
        .collect(fd.fullBody)
        .groupBy(_.lcd.id)
        .mapValues(ctxs => ctxs.sortBy(_.tparams.size).reverse.head)
        .values
        .toSeq
    }

    val localClassDefs = syms.functions.values.toSeq.flatMap(collectLocalClassDefs(_))
    val localClasses = localClassDefs.map(liftLocalClass(_)).toMap

    for (ctx <- localClassDefs; fd <- ctx.lcd.methods) {
      // if (ctx.lcd.cd.parents.isEmpty)
      //   throw MissformedStainlessCode(ctx.lcd, "Inner classes must extend a global class")

      val hasApplyLetRec = exprOps.exists {
        case _: ApplyLetRec => true
        case _ => false
      } (fd.fullBody)

      if (hasApplyLetRec)
        throw MissformedStainlessCode(fd, "Inner classes cannot reference local functions")
    }

    object transformer extends innerclasses.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case s.LetClass(lcd, body) => transform(body)

        case s.LocalClassConstructor(ct, args) => super.transform {
          val lc = localClasses(ct.cd.id)
          s.ClassConstructor(lc.localClassType, args ++ lc.newArgs)
        }

        case s.LocalMethodInvocation(caller, method, _, tps, args) => super.transform {
          s.MethodInvocation(caller, method.id, tps, args)
        }

        case s.LocalClassSelector(expr, id, _) => super.transform {
          s.ClassSelector(expr, id)
        }

        case _ => super.transform(e)
      }

      override def transform(tpe: s.Type): t.Type = tpe match {
        case lct: s.LocalClassType =>
          val lc = localClasses(lct.cd.id)
          super.transform(lc.localClassType)

        case _ => super.transform(tpe)
      }
    }

    val newFunctions  = localClasses.values.flatMap(_.methods)
    val liftedClasses = localClasses.values.map(_.cd)

    val functions    = (newFunctions  ++ syms.functions.values).map(transformer.transform).toSeq
    val classes      = (liftedClasses ++ syms.classes.values).map(transformer.transform).toSeq
    val sorts        = syms.sorts.values.map(transformer.transform).toSeq

    val res = t.NoSymbols.withFunctions(functions).withClasses(classes).withSorts(sorts)
    // implicit val popts = new t.PrinterOptions(printUniqueIds = true, symbols = Some(res))
    // println(res.asString)
    // res.ensureWellFormed
    res
  }
}
