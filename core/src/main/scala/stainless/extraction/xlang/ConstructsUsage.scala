package stainless
package extraction
package xlang

// This phases collect all constructs for which we should warn about
// These are then displayed in the final extraction summary report
class ConstructsUsage(override val s: Trees)(override val t: s.type)(using override val context: inox.Context)
  extends oo.CachingPhase
    with SimplyCachedFunctions
    with SimpleFunctions
    with IdentitySorts
    with oo.IdentityTypeDefs
    with oo.SimpleClasses
    with oo.SimplyCachedClasses { self =>
  import ConstructsUsage._

  override protected type TransformerContext = s.Symbols
  override protected type FunctionResult = t.FunDef

  override protected type FunctionSummary = SummaryData
  override protected type SortSummary = Unit
  override protected type ClassSummary = SummaryData
  override protected type TypeDefSummary = Unit

  override protected def getContext(symbols: s.Symbols): s.Symbols = symbols

  override protected def extractFunction(symbols: s.Symbols, fd: s.FunDef): (t.FunDef, SummaryData) = {
    val sc = new Scanner(s)(symbols, fd.id)
    sc.traverse(fd)
    (fd, sc.buildSummary)
  }

  override protected def extractClass(symbols: s.Symbols, cd: s.ClassDef): (t.ClassDef, SummaryData) = {
    val sc = new Scanner(s)(symbols, cd.id)
    sc.traverse(cd)
    (cd, sc.buildSummary)
  }

  override protected def combineSummaries(summaries: AllSummaries): ExtractionSummary = {
    val combined = summaries.fnsSummary.foldLeft(SummaryData())(_ ++ _) ++
      summaries.asInstanceOf[OOAllSummaries].classesSummaries.foldLeft(SummaryData())(_ ++ _)
    ExtractionSummary.Leaf(ConstructsUsage)(combined)
  }

  private class Scanner(override val trees: self.s.type)(syms: trees.Symbols, outermostId: Identifier) extends oo.DefinitionTraverser {
    import trees._

    private val isLib = syms.lookupClass(outermostId).map(_.flags)
      .getOrElse(syms.functions(outermostId).flags)
      .contains(Library)
    private var freeFnsUsage = Map.empty[UsedConstruct, Set[FreeFunction]]
    private var classesUsage = Map.empty[UsedConstruct, Set[Identifier]]
    private var methodsOrInnerUsage = Map.empty[(UsedConstruct, Identifier), Set[MethodOrInner]]
    private var fieldsUsage = Map.empty[(UsedConstruct, Identifier), Set[Identifier]]

    enum Env {
      case OuterFreeFun // Outermost function i.e. `outermostId`
      case InnerFreeFun(lfd: LocalFunDef)
      case Method(fd: FunDef, cls: Identifier) // Method of the outermost class or an inner class
      case InnerOfMethod(lfd: LocalFunDef, method: Identifier, cls: Identifier) // Inner function within a method
      case OuterClass // Outermost class i.e. `outermostId`
      case InnerClass(id: Identifier)
      case Field(id: Identifier, cls: Identifier)

      def visitingLocalFunDef(lfd: LocalFunDef): Env = this match {
        case OuterFreeFun | InnerFreeFun(_) => InnerFreeFun(lfd)
        case Method(m, cls) => InnerOfMethod(lfd, m.id, cls)
        case InnerOfMethod(_, m, cls) => InnerOfMethod(lfd, m, cls)
        case InnerClass(_) =>
          sys.error("Impossible, visiting an inner class proceeds to visit local methods (expecting an env of Method)")
        case OuterClass =>
          sys.error("Impossible, visiting a top-level class only proceed to visiting the fields. Methods are traversed as function")
        case Field(_, _) => sys.error("Impossible")
      }

      def visitingLocalMethodDef(lmd: LocalMethodDef): Env = this match {
        case OuterClass => Env.Method(lmd.toFunDef, outermostId)
        case InnerClass(id) => Env.Method(lmd.toFunDef, id)
        case _ => sys.error(s"Expected to be in OuterClass or InnerClass env (but is in $this)")
      }

      def visitingLocalClassDef(lcd: LocalClassDef): Env = {
        assert(!this.isInstanceOf[Field])
        Env.InnerClass(lcd.id)
      }

      def visitingField(vd: ValDef): Env = this match {
        case OuterClass => Env.Field(vd.id, outermostId)
        case InnerClass(id) => Env.Field(vd.id, id)
        case _ => sys.error(s"Expected to be in OuterClass or InnerClass env (but is in $this)")
      }

      def isExternFunction: Boolean = {
        val flags = this match {
          case OuterFreeFun => syms.functions(outermostId).flags
          case InnerFreeFun(lfd) => lfd.flags
          case Method(m, _) => m.flags
          case InnerOfMethod(lmd, _, _) => lmd.flags
          case _ => Seq.empty
        }
        flags.contains(Extern)
      }
    }

    def buildSummary: SummaryData = {
      def buildForConstruct(c: UsedConstruct): SummaryData = {
        val freeFns = freeFnsUsage.getOrElse(c, Set.empty)
        // All classes ids for which there is at least one field, method or definition itself that uses `c`
        val allClassesIds = classesUsage.getOrElse(c, Set.empty) ++
          methodsOrInnerUsage.keySet.filter(_._1 == c).map(_._2) ++
          fieldsUsage.keySet.filter(_._1 == c).map(_._2)
        if (freeFns.isEmpty && allClassesIds.isEmpty) SummaryData()
        else {
          val classes = allClassesIds.map { clsId =>
            val clsDeclAffected = classesUsage.getOrElse(c, Set.empty)(clsId)
            val methods = methodsOrInnerUsage.getOrElse((c, clsId), Set.empty)
            val fields = fieldsUsage.getOrElse((c, clsId), Set.empty)
            Class(clsId, clsDeclAffected, methods, fields)
          }
          val usage = Map(c -> ConstructsOccurrences(freeFns, classes))
          if (isLib) SummaryData(libUsage = usage)
          else SummaryData(userUsage = usage)
        }
      }

      UsedConstruct.values.foldLeft(SummaryData())(_ ++ buildForConstruct(_))
    }

    override def initEnv: Env = {
      if (syms.lookupClass(outermostId).isDefined) Env.OuterClass
      else {
        assert(syms.lookupFunction(outermostId).isDefined)
        val fd = syms.functions(outermostId)
        fd.flags.collectFirst { case IsMethodOf(cls) => cls }
          .map(Env.Method(syms.functions(outermostId), _))
          .getOrElse(Env.OuterFreeFun)
      }
    }

    override def traverse(e: Expr, env: Env): Unit = e match {
      case Choose(_, _) =>
        addUsedConstruct(UsedConstruct.Choose, env)
        super.traverse(e, env)
      case NoTree(_) =>
        // Note that @extern function have their bodies replaced with "???" by the frontend.
        // Therefore, we do not report @extern functions (as they are already reported for being @extern).
        if (!env.isExternFunction) {
          addUsedConstruct(UsedConstruct.NotImplemented, env)
        }
        super.traverse(e, env)
      case LetClass(classes, body) =>
        classes.foreach(traverse(_, env))
        traverse(body, env)
      case LetRec(fds, body) =>
        fds.foreach(traverse(_, env))
        traverse(body, env)
      case _ => super.traverse(e, env)
    }

    override def traverse(fd: FunDef): Unit = {
      assert(fd.id == outermostId)
      val env = initEnv
      if (isExternNonAccessor(fd)) {
        addUsedConstruct(UsedConstruct.Extern, env)
      }
      traverse(fd.fullBody, env)
    }

    override def traverse(cd: ClassDef): Unit = {
      assert(cd.id == outermostId)
      val env = initEnv
      if (cd.flags.contains(Extern)) {
        addUsedConstruct(UsedConstruct.Extern, env)
      }
      cd.fields.foreach(traverseField(_, env))
    }

    def traverse(lcd: LocalClassDef, env: Env): Unit = {
      val newEnv = env.visitingLocalClassDef(lcd)
      if (lcd.flags.contains(Extern)) {
        addUsedConstruct(UsedConstruct.Extern, newEnv)
      }
      lcd.fields.foreach(traverseField(_, newEnv))
      lcd.methods.foreach(traverse(_, newEnv))
    }

    def traverse(lmd: LocalMethodDef, env: Env): Unit = {
      val newEnv = env.visitingLocalMethodDef(lmd)
      if (isExternNonAccessor(lmd.toFunDef)) {
        addUsedConstruct(UsedConstruct.Extern, newEnv)
      }
      traverse(lmd.fullBody, newEnv)
    }

    def traverse(lfd: LocalFunDef, env: Env): Unit = {
      val newEnv = env.visitingLocalFunDef(lfd)
      if (lfd.flags.contains(Extern)) {
        addUsedConstruct(UsedConstruct.Extern, newEnv)
      }
      traverse(lfd.fullBody, newEnv)
    }

    def traverseField(field: ValDef, env: Env): Unit = {
      val newEnv = env.visitingField(field)
      if (field.flags.contains(Extern)) {
        addUsedConstruct(UsedConstruct.Extern, newEnv)
      }
    }

    def addUsedConstruct(c: UsedConstruct, env: Env): Unit = {
      env match {
        case Env.OuterFreeFun =>
          val curr = freeFnsUsage.getOrElse(c, Set.empty)
          freeFnsUsage += c -> (curr + FreeFunction.Outer(outermostId))
        case Env.InnerFreeFun(lfd) =>
          val curr = freeFnsUsage.getOrElse(c, Set.empty)
          freeFnsUsage += c -> (curr + FreeFunction.Inner(lfd.id, outermostId))
        case Env.Method(m, cls) =>
          val curr = methodsOrInnerUsage.getOrElse((c, cls), Set.empty)
          methodsOrInnerUsage += (c, cls) -> (curr + MethodOrInner.Method(m.id))
        case Env.InnerOfMethod(lfd, method, cls) =>
          val curr = methodsOrInnerUsage.getOrElse((c, cls), Set.empty)
          methodsOrInnerUsage += (c, cls) -> (curr + MethodOrInner.Inner(lfd.id, method))
        case Env.OuterClass =>
          val curr = classesUsage.getOrElse(c, Set.empty)
          classesUsage += c -> (curr + outermostId)
        case Env.InnerClass(id) =>
          val curr = classesUsage.getOrElse(c, Set.empty)
          classesUsage += c -> (curr + id)
        case Env.Field(id, cls) =>
          val curr = fieldsUsage.getOrElse((c, cls), Set.empty)
          fieldsUsage += (c, cls) -> (curr + id)
      }
    }

    // Do not report accessor functions for @extern field since these will be reported separately.
    def isExternNonAccessor(fd: FunDef): Boolean =
      fd.flags.contains(Extern) && !fd.flags.exists(_.isInstanceOf[IsAccessor])
  }
}

object ConstructsUsage extends ExtractionPipelineCreator {
  enum UsedConstruct {
    case Choose
    case Extern
    case NotImplemented
  }

  case class FunctionUsedConstructs(fn: Identifier, constructs: Set[UsedConstruct], innerFns: Map[Identifier, Set[UsedConstruct]]) {
    def hasExplicitChoose: Boolean = hasConstruct(UsedConstruct.Choose)
    def hasMissingImpl: Boolean = hasConstruct(UsedConstruct.NotImplemented)
    def hasExtern: Boolean = hasConstruct(UsedConstruct.Extern)

    def hasConstruct(c: UsedConstruct): Boolean = constructs.contains(c) || innerFns.values.exists(_.contains(c))
  }

  // All free functions and classes that use a particular construct
  case class ConstructsOccurrences(freeFns: Set[FreeFunction], classes: Set[Class]) {
    // `classes` must be unique by the identifier
    assert(classes.map(_.id).size == classes.size)

    def isAffected: Boolean = freeFns.nonEmpty || classes.exists(_.isAffected)

    def ++(other: ConstructsOccurrences): ConstructsOccurrences = {
      val thisClasses = classes.map(c => c.id -> c).toMap
      val otherClasses = other.classes.map(c => c.id -> c).toMap
      val combinedClasses = merge(thisClasses, otherClasses) { (c1, c2) =>
        assert(c1.id == c2.id)
        Class(c1.id, c1.clsDeclAffected || c2.clsDeclAffected, c1.methods ++ c2.methods, c1.fields ++ c2.fields)
      }.values.toSet
      ConstructsOccurrences(freeFns ++ other.freeFns, combinedClasses)
    }
  }

  // Methods and fields of a class that use a certain construct.
  // The `clsDeclAffected` flag specifies whether the class itself uses a construct.
  // For example with the @extern construct, if the class is annotated with it, the flag will be true.
  // If, on the other hand, the class is not @extern-annotated but one of its method is, `clsDeclAffected` will be false
  // (and the corresponding method will be in `methods`)
  case class Class(id: Identifier, clsDeclAffected: Boolean, methods: Set[MethodOrInner], fields: Set[Identifier]) {
    def isAffected: Boolean = clsDeclAffected || methods.nonEmpty || fields.nonEmpty
  }

  enum FreeFunction {
    case Outer(id: Identifier)
    case Inner(id: Identifier, outer: Identifier) // Note: `outer` refers to the outermost function
  }

  enum MethodOrInner {
    case Method(id: Identifier)
    case Inner(id: Identifier, outerMethod: Identifier)
  }

  case class SummaryData(userUsage: Map[UsedConstruct, ConstructsOccurrences] = Map.empty,
                         libUsage: Map[UsedConstruct, ConstructsOccurrences] = Map.empty) {
    // If an occurrence is not affected, then it should not be present in the map
    assert(userUsage.values.forall(_.isAffected))
    assert(libUsage.values.forall(_.isAffected))
    def ++(other: SummaryData): SummaryData =
      SummaryData(merge(userUsage, other.userUsage)(_ ++ _), merge(libUsage, other.libUsage)(_ ++ _))
    def hasExplicitChoose: Boolean = userUsage.contains(UsedConstruct.Choose)
    def hasMissingImpl: Boolean = userUsage.contains(UsedConstruct.NotImplemented)
    def hasExtern: Boolean = userUsage.contains(UsedConstruct.Extern)
  }

  private def merge[K, V](m1: Map[K, V], m2: Map[K, V])(f: (V, V) => V): Map[K, V] = {
    (m1.keySet ++ m2.keySet).foldLeft(Map.empty[K, V]) {
      case (acc, k) => acc + (k -> ((m1.get(k), m2.get(k)) match {
        case (Some(v1), Some(v2)) => f(v1, v2)
        case (Some(v1), None) => v1
        case (None, Some(v2)) => v2
        case (None, None) => sys.error("Impossible")
      }))
    }
  }

  override val name: String = "ConstructsUsage"

  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ConstructsUsage(s)(t)
    new Impl(trees, trees)
  }

}
