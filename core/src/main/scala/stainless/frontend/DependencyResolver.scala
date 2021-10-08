/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import coursier._
import coursier.parse.DependencyParser

import java.io.File
import java.nio.file.{Files, Path, StandardCopyOption}
import java.util.zip.{ZipFile, ZipEntry}
import java.util.stream.Collectors

import scala.annotation.tailrec
import scala.util.Properties

object DebugSectionExtraDeps extends inox.DebugSection("extra-deps")

object optExtraDeps extends inox.OptionDef[Set[Dependency]] {
    import inox.OptionParsers._

    val name     = "extra-deps"
    val default  = Set.empty[Dependency]
    val usageRhs = "org:name:version,..."

    private val depParser: OptionParser[Dependency] =
      DependencyResolver.parseDependency(_).toOption

    val parser: String => Option[Set[Dependency]] =
      setParser(depParser)
}

object optExtraResolvers extends inox.OptionDef[Set[Repository]] {
    import inox.OptionParsers._

    val name     = "extra-resolvers"
    val default  = Set.empty[Repository]
    val usageRhs = "URL,..."

    private val repoParser: OptionParser[Repository] =
      DependencyResolver.parseRepository(_).toOption

    val parser: String => Option[Set[Repository]] =
      setParser(repoParser)
}

class DependencyResolver(ctx: inox.Context, repositories: Set[Repository]) {
  import DependencyResolver._
  import ctx.{reporter, options}

  private val defaultRepositories: Set[Repository] = Set(
    Repositories.bintray("epfl-lara", "maven")
  )

  private given givenDebugSection: DebugSectionExtraDeps.type = DebugSectionExtraDeps

  def fetchAll(deps: Set[Dependency]): Seq[String] = {
    val repos = defaultRepositories ++ repositories

    val fetch = Fetch()
      .withDependencies(deps.map(_.withTransitive(false)).toSeq)
      .addRepositories(repos.toSeq: _*)
      .withClassifiers(Set(Classifier.sources))

    reporter.debug(s"Fetching ${deps map prettyName mkString ", "}...")

    val jars = fetch.run()

    reporter.debug(s" => DONE")

    val rootCacheDir = options.findOptionOrDefault(utils.Caches.optCacheDir)
    val cacheDir = rootCacheDir.toPath.resolve("extra-sources")

    val files = jars map { jar =>
      val dest = cacheDir.resolve(safeName(jar.getName)).toFile

      if (dest.exists) {
        reporter.debug(s"Destination '$dest' exists already, skipping JAR unpacking.")
      } else {
        reporter.debug(s"Unpacking '${jar.getPath}' into '$dest'...")
        unjar(jar, dest.toPath)
        reporter.debug(s" => DONE")
      }

      dest
    }

    val sources = allScalaSources(files.map(_.toPath))

    reporter.ifDebug { debug =>
      debug("Extra sources:")
      sources foreach { s => debug(s" - $s") }
    }

    sources.map(_.getAbsolutePath)
  }

  private def fileName(fullName: String): String = {
    if (fullName.indexOf(".") > 0) {
       fullName.substring(0, fullName.lastIndexOf("."))
    } else {
       fullName
    }
  }

  private def safeName(name: String): String = {
    fileName(name).replaceAll("[^a-zA-Z0-9\\.]", "-")
  }

  private def prettyName(dep: Dependency): String = {
    s"${dep.module}:${dep.version}"
  }

}

object DependencyResolver {

  def parseRepository(input: String): Either[String, Repository] = {
    Right(MavenRepository(input))
  }

  def parseDependency(input: String): Either[String, Dependency] = {
    DependencyParser.dependency(input, Properties.versionNumberString)
  }

  def unjar(jar: File, destPath: Path): Unit = {
    import scala.jdk.CollectionConverters._

    var archive: ZipFile = null

    try {
      archive = new ZipFile(jar)
      val entries = archive.stream().collect(Collectors.toList()).asScala.toList

      entries foreach { entry =>
        val entryDest = destPath.resolve(entry.getName())
        if (!entry.isDirectory()) {
          Files.createDirectories(entryDest.getParent)
          Files.copy(archive.getInputStream(entry), entryDest, StandardCopyOption.REPLACE_EXISTING)
        }
      }
    }
    finally {
      archive.close()
    }
  }

  def allScalaSources(folders: Seq[Path]): Seq[File] = {
    import scala.jdk.CollectionConverters._

    @tailrec
    def go(sourcesSoFar: Seq[File])(folders: Seq[Path]): Seq[File] = folders match {
      case Nil =>
        sourcesSoFar
      case folder +: rest =>
        val paths = Files.list(folder).collect(Collectors.toList()).asScala
        val dirs = paths.filter(_.toFile.isDirectory).toSeq
        val sources = for {
          path <- paths
          file = path.toFile
          if file.getName.endsWith("scala")
        } yield file
        go(sources.toSeq ++ sourcesSoFar)(dirs ++ rest)
    }
    go(Nil)(folders)
  }
}
