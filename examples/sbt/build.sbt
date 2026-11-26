val stainlessVersion = "0.10.6"

name := "stainless-example"

// The Scala 3 compiler of the lab, with which Stainless is built
scalaOrganization := "ch.epfl.lara"
scalaVersion := "3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY"

// The Stainless library, as a binary dependency
libraryDependencies += "ch.epfl.lara" %% "stainless-library" % stainlessVersion

// Stainless itself, as a compiler plugin. It verifies the program and removes its ghost code, and
// enables the compiler options Stainless needs. Programs with qualified types may also need
// `scalacOptions += "-Yqualified-types-anf"`.
addCompilerPlugin(("ch.epfl.lara" % "stainless-dotty-plugin" % stainlessVersion).cross(CrossVersion.full))
