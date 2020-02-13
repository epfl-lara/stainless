/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.codegen.runtime

/** Such exceptions are thrown when the evaluator encounters a runtime error,
  * for instance `.get` with an undefined key on a map. */
class CodeGenRuntimeException(msg: String) extends Exception(msg)
