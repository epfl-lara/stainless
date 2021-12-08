/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import inox.{Reporter, Options, OptionDef, OptionValue}

import java.io.File
import java.nio.file.{FileSystems, Path}
import scala.util.Try

import com.typesafe.config.{ConfigFactory, ConfigValue, ConfigValueType, ConfigException}

sealed abstract class OptionOrDefault[+A]
object OptionOrDefault {
  case class  Some[A](get: A) extends OptionOrDefault[A]
  case object None            extends OptionOrDefault[Nothing]
  case object Default         extends OptionOrDefault[Nothing]
}

object optConfigFile extends OptionDef[OptionOrDefault[File]] {
  override val name = "config-file"

  override val parser = {
    case ""      => Some(OptionOrDefault.None)
    case "false" => Some(OptionOrDefault.None)
    case path    => Try(OptionOrDefault.Some(new File(path))).toOption
  }

  override val default: OptionOrDefault[File] = OptionOrDefault.Default

  override val usageRhs = "FILE"
}

object Configuration {

  import scala.jdk.CollectionConverters._

  val ConfigName: String = "stainless.conf"

  private def isConfigFile(file: File): Boolean = {
    file.getName == ConfigName ||
    file.getName == s".$ConfigName"
  }

  def findConfigFile(): Option[File] = {
    RecursiveFileFinder.find(isConfigFile)
  }

  val empty: Seq[OptionValue[_]] = Seq.empty

  def get(options: Options, keys: Seq[inox.OptionDef[_]])(using Reporter): Seq[OptionValue[_]] = {
    import OptionOrDefault._
    options.findOptionOrDefault(optConfigFile) match {
      case Some(file) => parse(file, keys)
      case Default    => parseDefault(keys)
      case None       => empty
    }
  }

  def parseDefault(options: Seq[OptionDef[_]])(using Reporter): Seq[OptionValue[_]] = {
    findConfigFile() map { file =>
      parse(file, options)
    } getOrElse Seq.empty
  }

  def parse(file: File, options: Seq[OptionDef[_]])(using reporter: Reporter): Seq[OptionValue[_]] = try {
    if (!file.exists()) {
      reporter.fatalError(s"Configuration file does not exists: ${file.getAbsolutePath}")
    }
    else if (!file.canRead()) {
      reporter.fatalError(s"Configuration file is not readable: ${file.getAbsolutePath}")
    }

    val conf = ConfigFactory.parseFile(file)
    val entries = conf.entrySet.asScala.map { entry =>
      entry.getKey -> convert(entry.getKey, entry.getValue)
    }.toMap

    val optDefMap = options.view.groupBy(_.name).view.mapValues(_.head).toMap

    val optValues = entries map { case (name, str) =>
      optDefMap.get(name) map { optDef =>
        optDef.parse(str)
      } getOrElse {
        reporter.fatalError(s"Unknown option: $name")
      }
    }

    optValues.toSeq
  } catch {
    case e: ConfigException =>
      reporter.error(s"Invalid configuration file at '$file': ${e.getMessage}")
      Seq.empty
  }

  private def convert(name: String, config: ConfigValue)(using reporter: Reporter): String = {
    val unwrapped = config.unwrapped

    config.valueType match {
      case ConfigValueType.BOOLEAN => unwrapped.toString
      case ConfigValueType.NUMBER => unwrapped.toString
      case ConfigValueType.STRING => unwrapped.toString
      case ConfigValueType.LIST =>
        val values = unwrapped.asInstanceOf[java.util.List[Any]].iterator.asScala.toList
        values.map(_.toString).mkString(",")
      case _ =>
        reporter.fatalError(s"Unsupported option type for option '$name': $config")
    }
  }
}

object RecursiveFileFinder {
  import scala.jdk.CollectionConverters._

  def currentDirectory(): File = {
    FileSystems.getDefault().getPath(".").normalize.toAbsolutePath().toFile
  }

  def find(pred: File => Boolean): Option[File] = {
    findIn(pred, currentDirectory())
  }

  def findIn(pred: File => Boolean, directory: File): Option[File] = {
    findWithin(pred, directory) orElse {
      val parent = Option(directory.toPath.getParent).map(_.toFile)
      parent flatMap (p => findIn(pred, p))
    }
  }

  private def findWithin(pred: File => Boolean, directory: File): Option[File] = {
    directory.listFiles().toList
      .filter(_.isFile)
      .find(pred)
  }
}
