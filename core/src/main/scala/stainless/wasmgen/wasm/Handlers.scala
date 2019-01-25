/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen.wasm

import Types.Type
import Definitions._
import Expressions.Const

class GlobalsHandler(val globals: Seq[Global]) {
  def getType(l: Label): Type = globals.find(_.name == l).get.tpe
  def update(l: Label, c: Const) = {
    globals.find(_.name == l).get.update(c)
  }
  def update(l: Label, upd: Const => Const) = {
    val gl = globals.find(_.name == l).get
    gl.update(upd(gl.init))
  }
}

class LocalsHandler(args: Seq[ValDef]) {
  private var locals_ = args

  def getFreshLocal(l: Label, tpe: Type): Label = {
    locals_ :+= ValDef(l, tpe)
    l
  }
  def getType(l: Label): Type = locals_.find(_.name == l).get.tpe
  private[wasmgen] def locals: Seq[ValDef] = {
    locals_.drop(args.size)
  }
}

class DataHandler(init: Int) {
  private var data_ : Seq[Data] = Seq()
  private var offset = init
  def addNext(bytes: Seq[FormattedByte]): Int = {
    data_ :+= Data(offset, bytes)
    val current = offset
    offset += bytes.length
    current
  }
  def data = data_
  def nextFree = offset
}

