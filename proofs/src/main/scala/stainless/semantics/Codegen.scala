/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package semantics

import java.nio.file.Path

/** Generates the Scala evaluator of `proofs/semantics.md`, with Inox's generator: `sbt stainless-proofs/run`. */
object Codegen {
  val source = "semantics.md"
  val scalaOutput = "src/test/scala/stainless/semantics/generated/Semantics.scala"
  val scalaPackage = "stainless.semantics.generated"

  def scala: String = inox.semantics.Codegen.scala(Path.of(source), scalaPackage)

  def main(args: Array[String]): Unit =
    inox.semantics.Codegen.main(Array(source, scalaOutput, scalaPackage))
}
