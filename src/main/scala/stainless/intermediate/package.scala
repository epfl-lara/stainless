/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

/** Provides definitions for a hierarchy of languages above stainless,
  * topped by xlang, which is the extended input language of stainless.
  *
  * The traits [[intermediate.Trees]], [[intermediate.TreeDeconstructor]]
  * and [[intermediate.ExprOps]] (defined in the [[intermediate]] package
  * object) provide the unification point of all different stainless tree
  * types that can appear once extraction and pre-processing has finished.
  *
  * The hierarhcy is
  *   intermediate < innerfuns < imperative < holes < oo < xlang
  *
  * Innerfuns adds inner functions.
  * Imperative adds imperative features.
  * Holes adds the hole (???) synthesis construct.
  * OO adds object-oriented features.
  * xlang adds imports and module structure.
  */
package object intermediate {

  /** Unifies all stainless tree definitions */
  trait Trees extends ast.Trees with termination.Trees

  /** Unifies all stainless tree extractors */
  trait TreeDeconstructor extends ast.TreeDeconstructor with termination.TreeDeconstructor

  /** Unifies all stainless expression operations */
  trait ExprOps extends ast.ExprOps with termination.ExprOps
}
