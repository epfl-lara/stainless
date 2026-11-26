addSbtPlugin("com.typesafe.sbt" % "sbt-site" % "1.3.2")

addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.10.0")

// Signs the artifacts published to Maven Central (`publishSigned`)
addSbtPlugin("com.github.sbt" % "sbt-pgp" % "2.3.1")

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.4.0")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "1.1.0")
