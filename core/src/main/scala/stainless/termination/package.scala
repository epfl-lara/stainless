/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

package object termination {

  type TerminationProgram = Program { val trees: stainless.trees.type }
}
