/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import utils._

trait ComponentBuilder {
  def getComponents[T](graph : Map[T,Set[T]]) : List[Set[T]] = SCC.scc(graph)
}
