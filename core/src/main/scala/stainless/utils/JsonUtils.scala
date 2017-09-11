/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package utils

import java.io.{ File, PrintWriter }
import java.util.Scanner

import org.json4s.JValue
import org.json4s.native.JsonMethods._

object JsonUtils {

  def parseFile(file: File): JValue = {
    val sc = new Scanner(file)
    val sb = new StringBuilder
    while (sc.hasNextLine) { sb ++= sc.nextLine + "\n" }
    val json = parse(sb.toString)
    json
  }

  def writeFile(file: File, json: JValue): Unit = {
    val string = compact(render(json))
    val pw = new PrintWriter(file)
    try pw.write(string) finally pw.close()
  }

}

