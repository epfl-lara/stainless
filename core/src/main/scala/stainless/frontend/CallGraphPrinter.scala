/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt}

import inox.utils.Graphs._
import inox.utils.GraphPrinters.DotPrinter

object CallGraphPrinter {

  import xt._

  def apply(symbols: Symbols): Unit = {
    val displayedFds = symbols.functions.values.filter { fd =>
      !fd.flags.exists(_.name.contains("inline")) &&
      !fd.flags.contains(Ghost) &&
      !fd.isAccessor &&
      !fd.isInvariant &&
      !fd.isSynthetic &&
      !fd.getPos.file.toString.contains("stainless_")
    }.toSet
    val map = displayedFds.groupBy(fd => fd.getPos.file)

    val fw = new java.io.FileWriter("CallGraph.dot")

    fw.write("digraph G {\n")

    val nodes = scala.collection.mutable.Set[String]()
    var edges = scala.collection.mutable.Set[(String, String)]()

    // print dependencies within each file
    for ((fullName, fds) <- map) {
      val fdSet = fds.map(_.id).toSet
      val name0 = fullName.getName.takeWhile(c => c != '.')
      val name = if (name0.isEmpty) "Unknown" else name0

      fw.write(s"  subgraph cluster_$name {\n")
      fw.write(s"    label = $name;\n")
      for (fd1 <- fds) {
        val c = if (fd1.flags.contains(DropVCs)) "crimson"
          else if (fd1.flags.exists(_.name == "cCode.export")) "cornflowerblue"
          else if (fd1.flags.exists(_.name == "cCode.drop")) "gray"
          else if (fd1.flags.exists(_.name == "cCode.function")) "gray"
          else if (fd1.flags.exists(_.name == "extern")) "gray"
          else "darkolivegreen2"

        val name1 = fd1.id.toString
        if (!nodes.contains(name1)) {
          nodes += name1
          fw.write(s"    $name1 [style=filled,color=$c];\n")
        }
      }

      for (fd1 <- fds)
        for (id2 <- symbols.dependencies(fd1.id) & fdSet) {
          val name1 = fd1.id.toString
          val name2 = id2.toString
          if (!edges.contains((name1, name2))) {
            edges += ((name1, name2))
            fw.write(s"    $name1 -> $name2;\n")
          }
        }

      fw.write("  }\n")
    }

    fw.write("\n\n")
    // print dependencies across files
    for ((fullName, fds) <- map) {
      val fdSet = fds.map(_.id).toSet
      for (fd1 <- fds)
        for (id2 <- (symbols.dependencies(fd1.id) & displayedFds.map(_.id)) -- fdSet) {
          val name1 = fd1.id.toString
          val name2 = id2.toString
          if (!edges.contains((name1, name2))) {
            edges += ((name1, name2))
            fw.write(s"  $name1 -> $name2;\n")
          }
        }
    }

    fw.write("}\n")
    fw.close()
  }

}
