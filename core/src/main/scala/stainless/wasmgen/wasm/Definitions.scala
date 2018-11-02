/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen.wasm

import Expressions.{Expr, Const}
import Types.Type

/** Definitions for wasm programs */
object Definitions {

  case class ValDef(name: Label, tpe: Type)

  case class Global(name: Label, isMutable: Boolean, private var init_ : Const) {
    val tpe = init_.getType
    val toVal = ValDef(name, tpe)
    def update(c: Const) = {
      require(c.getType == tpe)
      init_ = c
    }
    def init = init_
  }

  case class FunDef private
    (name: String, args: Seq[ValDef], returnType: Type, locals: Seq[ValDef], body: Expr)
  {
    override def toString: String = Printer(this)
  }

  object FunDef {
    /** Construct a [[FunDef]]
      *
      * @param codeGen A function from a [[LocalsHandler]],
      *                which is instantiated by this constructor with the function arguments,
      *                to the body of the function
      */
    def apply(name: String, args: Seq[ValDef], returnType: Type)(codeGen: LocalsHandler => Expr): FunDef = {
      val lh = new LocalsHandler(args)
      // Make code first, as it may increment the locals in lh
      val body = codeGen(lh)
      FunDef(name, args, returnType, lh.locals, body)
    }
  }

  case class Import(extModule: Label, name: Label, tpe: ImportType)

  abstract class ImportType
  case class FunSig(name: Label, args: Seq[Type], returnType: Type) extends ImportType
  case class Memory(size: Int) extends ImportType

  case class Table(funs: Seq[Label]) {
    def indexOf(fun: Label) = funs.indexOf(fun)
  }

  case class FormattedByte(byte: Byte, formatted: Boolean)
  implicit class FormatByte(byte: Byte) {
    def f = FormattedByte(byte, true)
    def r = FormattedByte(byte, false)
  }
  case class Data(offset: Int, bytes: Seq[FormattedByte])
}
