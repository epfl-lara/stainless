package stainless
package utils

trait DefinitionIdFinder extends transformers.DefinitionTraverser {
  val s: trees.Symbols

  private lazy val idsMap = {
    s.functions.keys.map(id => id -> id) ++
    s.sorts.values.flatMap { s =>
      s.constructors.map(c => c.id -> s.id) ++ Seq(s.id -> s.id)
    }
  }.toMap

  def initEnv = ()
  type Env = Unit

  protected var ids: Set[Identifier] = Set()
  override def traverse(id: Identifier, env: Env): Unit = {
    ids ++= idsMap.get(id)
  }

  def doTraverse(fd: trees.FunDef): Set[Identifier] = {
    ids = Set()
    traverse(fd)
    ids
  }

  def doTraverse(sort: trees.ADTSort): Set[Identifier] = {
    ids = Set()
    traverse(sort)
    ids
  }
}

trait DependenciesFinder {
  val t: stainless.ast.Trees
  protected def traverser(s: t.Symbols): DefinitionIdFinder { val trees: t.type }

  def findDependencies(roots: Set[Identifier], s: t.Symbols): t.Symbols = {
    val tr = traverser(s)
    var found = Set[Identifier]()
    var toExplore = roots

    while(toExplore.nonEmpty) {
      val fIds = s.functions.values.view.force.filter(f => toExplore(f.id))
        .flatMap((fd: t.FunDef) => tr.doTraverse(fd)).toSet
      val sIds = s.sorts.values.view.force.filter(s => toExplore(s.id))
        .flatMap((s: t.ADTSort) => tr.doTraverse(s)).toSet
      found ++= toExplore
      toExplore = (fIds ++ sIds) -- found
    }

    t.NoSymbols
      .withFunctions(s.functions.values.toSeq.filter(f => found(f.id)))
      .withSorts(s.sorts.values.toSeq.filter(f => found(f.id)))
  }
}

