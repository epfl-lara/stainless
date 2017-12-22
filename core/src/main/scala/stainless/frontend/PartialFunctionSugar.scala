/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }

object PartialFunctionSugar {

  /**
   *  Extract `PartialFunction { (x: A) => require(pre(x)); body(x) }`
   *  into `~>( (x: A) => pre(x), (x: A) => assume(pre(x)); body(x) )`
   *
   *  Parameters:
   *   - [[pfctid]] is the identifier of the `~>` class type.
   *   - [[from]] & [[to]] are the type parameter of ~>.
   *   - [[fun]] is the raw body.
   */
  def create(pfctid: Identifier, from: xt.Type, to: xt.Type, fun: xt.Expr): xt.ClassConstructor = {
    val ct = xt.ClassType(pfctid, Seq(from, to))

    val (pre, body) = fun match {
      case xt.Lambda(Seq(vd), body0) =>
        val preOpt = xt.exprOps.preconditionOf(body0)
        val bareBody = xt.exprOps.withPrecondition(body0, None)
        val modifiedBody = preOpt match {
          case None => bareBody
          case Some(pre) => xt.Assume(pre, bareBody)
        }

        val pre = xt.Lambda(Seq(vd), preOpt getOrElse xt.BooleanLiteral(true))
        val body = xt.Lambda(Seq(vd), modifiedBody)

        (pre, body)

      case x =>
        throw new frontend.UnsupportedCodeException(fun.getPos, s"Unexpected $x [${x.getClass}] instead of a lambda when unapply syntactic sugar for partial function creation.")
    }

    xt.ClassConstructor(ct, Seq(pre, body))
  }

}

