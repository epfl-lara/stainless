package stainless
package verification

import scala.sys.process._
import scala.language.postfixOps // for the !! notation

import java.io.FileWriter

object CoqIO {
  // this global variable makes sure that no two files with the same name are created
  var i = 0

  val fileName = "verif"
  
  implicit val debugSection = DebugSectionCoq

  def writeToCoqFile(file: String, c: CoqCommand): Unit = {
    val s = new FileWriter(file)
    s.write(c.coqString)
    s.close()
  }

  def makeFilename(name: String): String = s"tmp/$name.v"

  def writeToCoqFile(c: CoqCommand): String = {
    this.synchronized {
      i += 1 // we atomically increment this variable
    }
    val file = s"$fileName$i.v"
    writeToCoqFile(file,c)
    file
  }

  def writeToCoqFile(m: Seq[(String, CoqCommand)]): Seq[String] = {
    val filenames = m.map {case (name, command) => (makeFilename(name), command)}
    filenames.foreach {case (fname, command) => writeToCoqFile(fname, command)}
    filenames.map(_._1)
  }

  def coqc(fileName: String, ctx: inox.Context) = { 
    ctx.reporter.debug(s"Invoking: coqc $fileName")
    val output = new collection.mutable.ListBuffer[String]
    val proc = s"coqc -R slc-lib SLC $fileName" ! ProcessLogger(output += _)
    if (output.isEmpty)
      ctx.reporter.info(s"No output from Coq for file $fileName. Your program is valid.")
    else {
      ctx.reporter.info(s"Coq gave some output for file $fileName:")
      for (l <- output) {
        if (l.contains("Error"))
          ctx.reporter.error(l)
        else if (l.trim != "")
          ctx.reporter.warning(l)
      }
    }
  }
}