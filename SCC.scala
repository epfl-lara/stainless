/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package termination

/** This could be defined anywhere, it's just that the
    termination checker is the only place where it is used. */
object SCC {
  def scc[T](graph : Map[T,Set[T]]) : (Array[Set[T]],Map[T,Int],Map[Int,Set[Int]]) = {
    // The first part is a shameless adaptation from Wikipedia
    val allVertices : Set[T] = graph.keySet ++ graph.values.flatten

    var index = 0
    var indices  : Map[T,Int] = Map.empty
    var lowLinks : Map[T,Int] = Map.empty
    var components : List[Set[T]] = Nil
    var s : List[T] = Nil

    def strongConnect(v : T) {
      indices  = indices.updated(v, index)
      lowLinks = lowLinks.updated(v, index)
      index += 1
      s = v :: s

      for(w <- graph.getOrElse(v, Set.empty)) {
        if(!indices.isDefinedAt(w)) {
          strongConnect(w)
          lowLinks = lowLinks.updated(v, lowLinks(v) min lowLinks(w))
        } else if(s.contains(w)) {
          lowLinks = lowLinks.updated(v, lowLinks(v) min indices(w))
        }
      }

      if(lowLinks(v) == indices(v)) {
        var c : Set[T] = Set.empty
        var stop = false
        do {
          val x :: xs = s
          c = c + x
          s = xs
          stop = (x == v)
        } while(!stop);
        components = c :: components
      }
    }

    for(v <- allVertices) {
      if(!indices.isDefinedAt(v)) {
        strongConnect(v)
      }  
    }

    // At this point, we have our components.
    // We finish by building a graph between them.
    // In the graph, components are represented as arrays indices.
    val asArray = components.toArray
    val cSize = asArray.length

    val vertIDs : Map[T,Int] = allVertices.map(v =>
      v -> (0 until cSize).find(i => asArray(i)(v)).get
    ).toMap

    val bigCallGraph : Map[Int,Set[Int]] = (0 until cSize).map({ i =>
      val dsts = asArray(i).flatMap(v => graph.getOrElse(v, Set.empty)).map(vertIDs(_))
      i -> dsts
    }).toMap

    (asArray,vertIDs,bigCallGraph)
  }
}
