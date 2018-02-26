libraryDependencies += { "org.scala-sbt" % "scripted-plugin" % sbtVersion.value }

addSbtPlugin("com.typesafe.sbt" % "sbt-site" % "0.8.1")
addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.7.0")
addSbtPlugin("org.foundweekends" % "sbt-bintray" % "0.5.3")
addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "0.9.3")
