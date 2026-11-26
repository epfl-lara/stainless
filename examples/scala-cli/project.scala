// The Scala 3 compiler of the lab, with which Stainless is built
//> using scalaOrganization ch.epfl.lara
//> using scala 3.10.1-RC1-bin-20260903-e1f9361-NIGHTLY
// The Stainless library, as a binary dependency, and Stainless itself, as a compiler plugin
//> using dep ch.epfl.lara::stainless-library:0.10.6
//> using plugin ch.epfl.lara:::stainless-dotty-plugin:0.10.6
// The plugin verifies the program and removes its ghost code, and enables the compiler options
// Stainless needs. Programs with qualified types may also need `//> using options -Yqualified-types-anf`.
