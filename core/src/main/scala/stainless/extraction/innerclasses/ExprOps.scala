/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package innerclasses

trait ExprOps extends methods.ExprOps {
  protected val trees: Trees
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

}
