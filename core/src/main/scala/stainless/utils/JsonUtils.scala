/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package utils

import java.io.{ File, PrintWriter }
import java.util.Scanner

import scala.util.{ Left, Right }

import io.circe.Json
import io.circe.parser._

object JsonUtils {

  def parseString(str: String): Json = parse(str) match {
    case Right(json) => json
    case Left(error) => throw error
  }

  def parseFile(file: File): Json = {
    val sc = new Scanner(file)
    val sb = new StringBuilder
    while (sc.hasNextLine) { sb ++= sc.nextLine + "\n" }
    parseString(sb.toString)
  }

  def writeFile(file: File, json: Json): Unit = {
    val string = json.noSpaces
    val pw = new PrintWriter(file)
    try pw.write(string) finally pw.close()
  }

}

