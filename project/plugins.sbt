addSbtPlugin("com.typesafe.sbt" % "sbt-site" % "1.3.2")

addSbtPlugin("com.eed3si9n" % "sbt-buildinfo" % "0.10.0")

// Signs the artifacts published to Maven Central (`publishSigned`)
addSbtPlugin("com.github.sbt" % "sbt-pgp" % "2.3.1")

addSbtPlugin("com.github.sbt" % "sbt-git" % "3.0.0")

// sbt-git 3.0.0 still bundles JGit 5.13, which cannot resolve linked-worktree
// commondir metadata. JGit 7.8.1 supports that layout and requires Java 17+.
dependencyOverrides += "org.eclipse.jgit" % "org.eclipse.jgit" % "7.8.1.202611041320-r"

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.4.0")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "1.1.0")
