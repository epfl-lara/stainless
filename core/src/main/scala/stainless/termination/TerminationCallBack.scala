/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import extraction.xlang.{ trees => xt }

// TODO Implement TerminationCallBack
/** Callback for termination */
class TerminationCallBack(val ctx: inox.Context) extends frontend.CallBack {
  override def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = ???

  override def stop(): Unit = ()
  override def join(): Unit = ()

  override def getReports: Seq[AbstractReport] = Nil
}

