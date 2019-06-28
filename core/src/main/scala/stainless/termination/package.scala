/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

package object termination {

  type TerminationProgram = Program { val trees: stainless.trees.type }
}
