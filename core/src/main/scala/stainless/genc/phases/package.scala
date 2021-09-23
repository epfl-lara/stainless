/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

// import purescala.Common.{ Identifier }
// import purescala.Definitions.{ Definition, FunDef, ValDef, Program }
// import purescala.Types.{ TypeTree }

import extraction.throwing.trees._

/*
 * Some type aliased for readability
 */
package object phases {

  case class VarInfo(vd: ValDef, typ: Type, isVar: Boolean)

  type FunCtxDB = Map[LocalFunDef, Seq[VarInfo]]

}
