val stainlessVersion = "0.10.6"

name := "stainless-example"

// The Scala 3 compiler of the lab, with which Stainless is built
scalaOrganization := "ch.epfl.lara"
scalaVersion := "3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY"

// The Stainless library, as a binary dependency
libraryDependencies += "ch.epfl.lara" %% "stainless-library" % stainlessVersion

// Stainless itself, as a compiler plugin
addCompilerPlugin(("ch.epfl.lara" % "stainless-dotty-plugin" % stainlessVersion).cross(CrossVersion.full))

scalacOptions ++= Seq(
  // Lets Stainless extract the definitions of the library from its TASTy files
  "-Yretain-trees",
  "-language:experimental.qualifiedTypes",
  "-language:experimental.qualifiedTypes.silent",
  "-Yqualified-types-anf",
  "-P:stainless:verify:true",
  "-P:stainless:ghost-elim:true",
)
