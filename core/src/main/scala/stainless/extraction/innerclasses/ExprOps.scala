/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

class ExprOps(override val trees: Trees) extends methods.ExprOps(trees) {
  import trees._

  def freeVariablesOf(lcd: LocalClassDef): Set[Variable] = {
    lcd.methods.flatMap(fd => freeVariablesOf(fd.toFunDef)).toSet
  }

  def freeVariablesOf(fd: FunDef): Set[Variable] = {
    exprOps.variablesOf(fd.fullBody) -- fd.params.map(_.toVariable).toSet
  }

  def freeTypeParamsOf(fd: FunDef): Set[TypeParameter] = {
    val typeParams = typeOps.typeParamsOf(FunctionType(fd.params.map(_.tpe), fd.returnType))
    typeParams -- fd.tparams.map(_.tp).toSet
  }

  def freeTypeParamsOf(lcd: LocalClassDef): Set[TypeParameter] = {
    val typeParams = {
      lcd.fields.map(_.tpe).flatMap(typeOps.typeParamsOf(_)).toSet ++
      lcd.parents.flatMap(typeOps.typeParamsOf(_)).toSet ++
      lcd.methods.flatMap(fd => freeTypeParamsOf(fd.toFunDef))
    }

    typeParams -- lcd.tparams.map(_.tp).toSet
  }

  def outerThisReferences(lcd: LocalClassDef): Set[This] = {
    lcd.methods.flatMap { fd =>
      exprOps.collect[This] {
        case t @ This(tp) if tp.id != lcd.id => Set(t)
        case t @ LocalThis(tp) if tp.id != lcd.id => Set(This(tp.toClassType))
        case _ => Set.empty
      } (fd.fullBody)
    }.toSet
  }

  /* =============================
   * Freshening of local variables
   * ============================= */

  protected class InnerClassesFreshener(freshenChooses: Boolean)
    extends ImperativeFreshener(freshenChooses) {

      def transform(lmd: LocalMethodDef, env: Env, methodsEnv: Env): LocalMethodDef = {
        val LocalMethodDef(id, tparams, params, returnType, fullBody, flags) = lmd
        val newId = methodsEnv(id)
        val newTypeParams = tparams.map(tpd => transform(tpd.freshen, env))
        val tparamsEnv = tparams.zip(newTypeParams).map {
          case (tp, ntp) => tp.id -> ntp.id
        }
        val (newParams, finalEnv) = params.foldLeft((Seq[t.ValDef](), env ++ tparamsEnv)) {
          case ((currentParams, currentEnv), vd) =>
            val freshVd = transform(vd.freshen, env)
            (currentParams :+ freshVd, currentEnv.updated(vd.id, freshVd.id))
        }
        val newReturnType = transform(returnType, finalEnv)
        val newBody = transform(fullBody, finalEnv ++ methodsEnv)
        val newFlags = flags.map(transform(_, env))
        LocalMethodDef(newId, newTypeParams, newParams, newReturnType, newBody, newFlags)
      }

      def transform(ltd: LocalTypeDef, env: Env, typesEnv: Env): LocalTypeDef = {
        val LocalTypeDef(id, tparams, rhs, flags) = ltd
        val newId = typesEnv(id)
        val newTypeParams = tparams.map(transform(_, env))
        val newRhs = transform(rhs, env ++ typesEnv)
        val newFlags = flags.map(transform(_, env))
        LocalTypeDef(newId, newTypeParams, newRhs, newFlags)
      }

      override def transform(expr: Expr, env: Env): Expr = expr match {
        case LetClass(classes, rest) =>
          val freshIds = classes.map(lc => lc.id -> lc.id.freshen).toMap
          val newClasses = for (LocalClassDef(id, tparams, parents, fields, methods, typeMembers, flags) <- classes) yield {
            val newId = freshIds(id)
            val newTypeParams = tparams.map(tpd => transform(tpd.freshen, env))
            val tparamsEnv = tparams.zip(newTypeParams).map {
              case (tp, ntp) => tp.id -> ntp.id
            }
            val newParents = parents.map(transform(_, env ++ tparamsEnv))
            val (newFields, fieldsEnv) = fields.foldLeft((Seq[ValDef](), env ++ tparamsEnv)) {
              case ((currentParams, currentEnv), vd) =>
                val freshVd = transform(vd.freshen, env)
                (currentParams :+ freshVd, currentEnv.updated(vd.id, freshVd.id))
            }
            val typesEnv = typeMembers.map(ltd => ltd.id -> ltd.id.freshen).toMap
            val newTypeMembers = typeMembers.map(transform(_, env ++ freshIds, typesEnv))
            val methodsEnv = methods.map(lmd => lmd.id -> lmd.id.freshen).toMap
            val newMethods = methods.map(transform(_, fieldsEnv ++ freshIds ++ typesEnv, methodsEnv))
            val newFlags = flags.map(transform(_, env))

            LocalClassDef(newId, newTypeParams, newParents, newFields, newMethods, newTypeMembers, newFlags)
          }
          LetClass(newClasses, transform(rest, env ++ freshIds))

        case _ =>
          super.transform(expr, env)
      }
  }

  override def freshenLocals(expr: Expr, freshenChooses: Boolean = false): Expr = {
    new InnerClassesFreshener(freshenChooses).transform(expr, Map.empty[Identifier, Identifier])
  }

}
