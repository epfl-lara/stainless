/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.wasmgen

import stainless.Identifier
import stainless.trees._
import stainless.utils.{DefinitionIdFinder, DependenciesFinder}

class WasmDefIdFinder(val s: Symbols) extends DefinitionIdFinder { outer =>
  val trees = stainless.trees
  private val lib: LibProvider { val trees: outer.trees.type } = new LibProvider {
    protected val trees = outer.trees
  }
  private def fun(name: String) = lib.fun(name)(s).id
  private def sort(name: String) = lib.sort(name)(s).id
  private lazy val setIds = Set(sort("Set"), fun("SNil$0ToString"), fun("SCons$0ToString"))
  private lazy val bagIds = Set(sort("Bag"), fun("BNil$0ToString"), fun("BCons$0ToString"))
  private lazy val mapIds = Set(sort("Map"), fun("MNil$0ToString"), fun("MCons$0ToString"))

  override def traverse(expr: Expr, env: Env): Unit = {
    expr match {
      // Tuples
      case Tuple(elems) =>
        ids += sort(s"Tuple${elems.size}")
      case TupleSelect(tuple, _) =>
        val TupleType(ts) = tuple.getType(s)
        ids += sort(s"Tuple${ts.size}")
      // Sets
      case FiniteSet(_, _) | SetAdd(_, _) =>
        ids += fun("setAdd")
        ids ++= setIds
      case ElementOfSet(_, _) =>
        ids += fun("elementOfSet")
        ids ++= setIds
      case SubsetOf(_, _) =>
        ids += fun("subsetOf")
        ids ++= setIds
      case SetIntersection(_, _) =>
        ids += fun("setIntersection")
        ids ++= setIds
      case SetUnion(_, _) =>
        ids += fun("setUnion")
        ids ++= setIds
      case SetDifference(_, _) =>
        ids += fun("setDifference")
        ids ++= setIds
      // Bags
      case FiniteBag(_, _) | BagAdd(_, _) =>
        ids += fun("bagAdd")
        ids ++= bagIds
      case MultiplicityInBag(_, _) =>
        ids += fun("bagMultiplicity")
        ids ++= bagIds
      case BagIntersection(_, _) =>
        ids += fun("bagIntersection")
        ids ++= bagIds
      case BagUnion(_, _) =>
        ids += fun("bagUnion")
        ids ++= bagIds
      case BagDifference(_, _) =>
        ids += fun("bagDifference")
        ids ++= bagIds
      // Maps
      case FiniteMap(_, _, _, _) | MapUpdated(_, _, _) =>
        ids += fun("mapUpdated")
        ids ++= mapIds
      case MapApply(_, _) =>
        ids += fun("mapApply")
        ids ++= mapIds
      case _ =>
    }
    super.traverse(expr, env)
  }
}


class WasmDependenciesFinder extends DependenciesFinder {
  val t: stainless.trees.type = stainless.trees
  def traverser(s: Symbols): DefinitionIdFinder { val trees: t.type } = new WasmDefIdFinder(s)
  private val lib: LibProvider { val trees: t.type } = new LibProvider {
    protected val trees = t
  }
  override def findDependencies(roots: Set[Identifier], s: Symbols): Symbols = {
    super.findDependencies(roots, s)
      .withFunctions(Seq(
        "toString", "digitToStringL", "digitToStringI",
        "i32ToString", "i64ToString", "f64ToString",
        "booleanToString", "funToString", "unitToString"
      ).map(lib.fun(_)(s)))
  }
}

