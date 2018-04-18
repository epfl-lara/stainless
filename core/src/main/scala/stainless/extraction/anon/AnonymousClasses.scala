/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package anon

trait AnonymousClasses extends inox.ast.SymbolTransformer { self =>
  val s: Trees
  val t: methods.Trees

  implicit class TypeParamOps(val tp: s.TypeParameter) {
    def toDef: s.TypeParameterDef = s.TypeParameterDef(tp)
  }

  def transform(syms: s.Symbols): t.Symbols = {
    import s._

    implicit val printerOpts = new PrinterOptions(printUniqueIds = true, printTypes = false)

    def collectLocalClassDefs(fd: FunDef): Set[(FunDef, LocalClassDef)] = exprOps.collect[(FunDef, LocalClassDef)] {
      case LetClass(lcd, _) => Set(fd -> lcd)
      case _ => Set()
    } (fd.fullBody)

    def liftLocalClass(fd: FunDef, lcd: LocalClassDef): (Identifier, (TypedClassDef, Seq[ValDef], Seq[FunDef], ClassType)) = {
      val methods = lcd.methods.toSeq

      // Collect all free variables in class's methods
      val freeVariables = methods.flatMap { fd =>
        exprOps.variablesOf(fd.fullBody).map(_.toVal) -- fd.params.toSet
      }.toSet.toSeq

      // Collect all free type parameters of all parents, minus the local class's own
      val freeTypeParams = (lcd.cd.parents.toSet.flatMap(typeOps.typeParamsOf).map(_.toDef) -- lcd.tparams.toSet).toSeq

      val freshTypeParams = freeTypeParams.map(_.freshen)

      val typeMap = freeTypeParams.map(_.tp).zip(freshTypeParams.map(_.tp)).toMap

      def instantiateExpr[E <: Expr](expr: E): E = typeOps.instantiateType(expr, typeMap).asInstanceOf[E]
      def instantiateType(tpe: Type): Type       = typeOps.instantiateType(tpe, typeMap)
      def instantiateVal(vd: ValDef): ValDef     = vd.copy(tpe = instantiateType(vd.tpe))

      val newFields = freeVariables.map(vd => instantiateExpr(vd.toVariable.freshen).toVal)
      val newParents = lcd.cd.parents.map(ct => instantiateType(ct).asInstanceOf[ClassType])

      val newClass = lcd.cd.copy(
        fields = lcd.cd.fields ++ newFields,
        tparams = lcd.cd.tparams ++ freshTypeParams,
        parents = newParents
      )

      val typedClass = newClass.typed(syms)
      val localTypedClass = newClass.typed(fd.tparams.map(_.tp))(syms)

      // Rewrite any access to a free variable of the class into a field access
      val newMethods = methods.map { fd =>
        val subst = (freeVariables zip newFields).map { case (fv, vd) =>
          fv -> ClassSelector(This(typedClass.toType), vd.id)
        }.toMap

        val newParams = fd.params.map(instantiateVal)
        val newBody = exprOps.replaceFromSymbols(subst, fd.fullBody)

        fd.copy(
          params = newParams,
          fullBody = instantiateExpr(newBody),
          returnType = instantiateType(fd.returnType)
        )
      }

      newClass.id -> (typedClass, freeVariables, newMethods, localTypedClass.toType)
    }

    val localClassDefs = syms.functions.values.toSet.flatMap(collectLocalClassDefs)
    val localClasses = localClassDefs.toSeq.map((liftLocalClass _).tupled).toMap

    object transformer extends anon.TreeTransformer {
      val s: self.s.type = self.s
      val t: self.t.type = self.t

      override def transform(e: s.Expr): t.Expr = e match {
        case s.LetClass(lcd, args) => super.transform {
          val (regClass, freeVars, _, ct) = localClasses(lcd.id)
          s.ClassConstructor(ct, args ++ freeVars.map(_.toVariable))
        }

        case _ => super.transform(e)
      }

      override def transform(cd: s.ClassDef): t.ClassDef = super.transform {
        cd.copy(flags = cd.flags.filterNot(_.name == "anonymous"))
      }

      def transformFun(fd: s.FunDef): t.FunDef = super.transform {
        fd.copy(flags = fd.flags.filterNot(_.name == "anonymous"))
      }
    }

    val newFunctions = localClasses.values.flatMap(_._3)
    val newClasses   = localClasses.values.map(_._1)

    val functions    = (newFunctions ++ syms.functions.values).map(transformer.transformFun).toSeq
    val classes      = (newClasses.map(_.cd) ++ syms.classes.values).map(transformer.transform).toSeq
    val sorts        = syms.sorts.values.map(transformer.transform).toSeq

    val newSyms = t.NoSymbols.withFunctions(functions).withClasses(classes).withSorts(sorts)
    println(newSyms)
    newSyms.ensureWellFormed
    newSyms
  }
}
