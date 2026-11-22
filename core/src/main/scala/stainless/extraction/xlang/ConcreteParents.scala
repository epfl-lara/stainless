/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

import stainless.ast.SymbolIdentifier
import scala.collection.mutable.{Map => MutableMap}

/** Encodes the extension of concrete classes, as later phases only let abstract classes be extended.
 *
 *  The frontend extracts the arguments that a class passes to the constructor of a concrete parent as
 *  overrides of the accessors of the parent's fields, with the `@parentArgument` annotation (see
 *  `extractParentArguments` in the frontend). For example,
 *
 * {{{
 * class C(val x: BigInt) { def m: BigInt = x + 1 }
 * case class D(y: BigInt) extends C(y * 2) { override def m: BigInt = y }
 * def test = new C(5).x + D(3).x
 * }}}
 *
 *  is extracted as
 *
 * {{{
 * class C(x: BigInt) { def x: BigInt = this.x; def m: BigInt = this.x + 1 } // `x` is a field and its accessor
 * case class D(y: BigInt) extends C { @parentArgument override def x: BigInt = this.y * 2; override def m: BigInt = y }
 * def test = new C(5).x + D(3).x
 * }}}
 *
 *  This phase makes each extended concrete class `C` abstract, with abstract accessors for its fields. It
 *  moves the fields to a new subclass of `C`, also named `C`, which stands for the instances of `C` that
 *  are not instances of its subclasses, and constructs it in place of `C`:
 *
 * {{{
 * abstract class C { def x: BigInt; def m: BigInt = this.x + 1 }
 * case class C'(x: BigInt) extends C { override def x: BigInt = this.x }
 * case class D(y: BigInt) extends C { override def x: BigInt = this.y * 2; override def m: BigInt = y }
 * def test = C'(5).x + D(3).x
 * }}}
 *
 *  Selections of the fields of `C` become calls to their accessors. As in Scala, the invariant of `C`
 *  holds for the instances of its subclasses, which are instances of `C`. Unless `C` is sealed, it may
 *  have subclasses that the program doesn't show (see [[methods.Sealing]]), like other abstract classes.
 *
 *  As the arguments to the constructor of `C` only refer to the fields of the subclass, they are evaluated
 *  at each access of the fields of `C` rather than once. The phase rejects extended concrete classes with
 *  mutable fields, whose values may diverge from these arguments, as well as extended member classes,
 *  local classes extending concrete classes and patterns on extended case classes.
 */
class ConcreteParents(override val s: Trees)(override val t: s.type)
                     (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  // Identifiers are stable across runs
  private val plainIds = MutableMap[Identifier, Identifier]()
  private val plainAccessorIds = MutableMap[Identifier, SymbolIdentifier]()

  private def isParentArgument(flag: Flag): Boolean = flag match {
    case Annotation("parentArgument", Seq()) => true
    case _ => false
  }

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    val extended: Set[Identifier] = symbols.classes.values.toSeq
      .flatMap(_.parents.map(_.id))
      .filter(id => !symbols.getClass(id).flags.contains(IsAbstract))
      .toSet

    if (extended.isEmpty) {
      val functions = symbols.functions.values.map(fd => fd.copy(flags = fd.flags.filterNot(isParentArgument)))
      return (symbols.withFunctions(functions.toSeq), ExtractionSummary.NoSummary)
    }

    for (id <- extended) {
      val cd = symbols.getClass(id)
      if (cd.flags.exists(_.isInstanceOf[IsMemberOf]))
        context.reporter.fatalError(cd.getPos, s"Stainless does not support extending the concrete member class ${cd.id.asString}")
      if (cd.flags.contains(IsObject))
        context.reporter.fatalError(cd.getPos, s"Objects cannot be extended (${cd.id.asString})")
      cd.fields.find(_.flags.contains(IsVar)).foreach { vd =>
        context.reporter.fatalError(vd.getPos, s"Stainless does not support mutable fields in extended concrete classes (${vd.id.asString} of ${cd.id.asString})")
      }
    }

    def plainId(id: Identifier): Identifier = plainIds.getOrElseUpdate(id, FreshIdentifier(id.name))

    // The extended class that declares each field
    val fieldOwner: Map[Identifier, Identifier] = extended.toSeq.flatMap { id =>
      symbols.getClass(id).fields.map(_.id -> id)
    }.toMap

    // The accessors of the fields of the extended classes
    val accessors: Map[Identifier, FunDef] = extended.toSeq.flatMap { id =>
      val cd = symbols.getClass(id)
      cd.methods.map(symbols.getFunction).flatMap { fd =>
        fd.flags.collectFirst { case IsAccessor(Some(fid)) if fieldOwner.get(fid) == Some(id) && fd.params.isEmpty => fid -> fd }
      }
    }.toMap

    for ((fid, cid) <- fieldOwner if !accessors.contains(fid))
      context.reporter.internalError(s"No accessor for field ${fid.asString} of ${cid.asString}")

    object transformer extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      override def transform(e: Expr): Expr = e match {
        case ClassConstructor(ct, args) if extended(ct.id) =>
          ClassConstructor(
            ClassType(plainId(ct.id), ct.tps.map(transform)).copiedFrom(ct),
            args.map(transform)
          ).copiedFrom(e)

        case ClassSelector(recv, field) if fieldOwner.contains(field) =>
          MethodInvocation(transform(recv), accessors(field).id, Seq.empty, Seq.empty).copiedFrom(e)

        case LetClass(lcds, _) if lcds.exists(_.parents.exists { case ct: ClassType => extended(ct.id) case _ => false }) =>
          context.reporter.fatalError(e.getPos, "Stainless does not support local or anonymous classes extending concrete classes")

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case ClassPattern(_, ct, _) if extended(ct.id) =>
          context.reporter.fatalError(pat.getPos, s"Stainless does not support patterns on the extended case class ${ct.id.asString}")
        case _ => super.transform(pat)
      }

      override def transform(flag: Flag): Flag = flag match {
        case ClassParamInit(cid) if extended(cid) => ClassParamInit(plainId(cid))
        case _ => super.transform(flag)
      }
    }

    // The accessors of the fields of extended classes become abstract
    def abstractAccessor(fd: FunDef): FunDef = fd.copy(
      fullBody = NoTree(fd.returnType).copiedFrom(fd),
      flags = (fd.flags.filter {
        case Final | Private | Inline | IsAccessor(_) => false
        case _ => true
      } ++ Seq(IsAbstract, IsAccessor(None))).distinct
    ).copiedFrom(fd)

    val functions = symbols.functions.values.toSeq.map { fd =>
      val fd1 = fd.copy(flags = fd.flags.filterNot(isParentArgument))
      val accessorOf = fd.flags.collectFirst { case IsAccessor(Some(fid)) if accessors.get(fid).exists(_.id == fd.id) => fid }
      transformer.transform(if (accessorOf.isDefined) abstractAccessor(fd1) else fd1)
    }

    val classes = symbols.classes.values.toSeq.map { cd =>
      if (!extended(cd.id)) transformer.transform(cd)
      else transformer.transform(cd.copy(fields = Seq.empty, flags = (cd.flags :+ IsAbstract).distinct).copiedFrom(cd))
    }

    // The subclasses standing for the instances of the extended classes that are not instances of their subclasses
    val (plainClasses, plainAccessors) = extended.toSeq.map { id =>
      val cd = symbols.getClass(id)
      val tps = exprOps.freshenTypeParams(cd.typeArgs)
      val instantiator = new typeOps.TypeInstantiator((cd.typeArgs zip tps).toMap)
      val pid = plainId(id)
      val pct = ClassType(pid, tps).copiedFrom(cd)

      val plain = new ClassDef(
        pid,
        tps.map(tp => TypeParameterDef(tp).copiedFrom(tp)),
        Seq(ClassType(id, tps).copiedFrom(cd)),
        cd.fields.map(vd => instantiator.transform(transformer.transform(vd))),
        (cd.flags.filter {
          case IsSealed | IsAbstract => false
          case _ => true
        } :+ Synthetic).map(transformer.transform).distinct
      ).copiedFrom(cd)

      val accessorDefs = cd.fields.map { vd =>
        val accessor = accessors(vd.id)
        val accessorId = plainAccessorIds.getOrElseUpdate(accessor.id, accessor.id match {
          case sid: SymbolIdentifier => SymbolIdentifier(sid.symbol)
          case _ => context.reporter.internalError(s"Unexpected accessor identifier ${accessor.id.asString}")
        })
        new FunDef(
          accessorId,
          Seq.empty,
          Seq.empty,
          instantiator.transform(transformer.transform(vd.tpe)),
          ClassSelector(This(pct).copiedFrom(vd), vd.id).copiedFrom(vd),
          Seq(Synthetic, IsAccessor(Some(vd.id)), IsMethodOf(pid))
        ).copiedFrom(vd)
      }

      (plain, accessorDefs)
    }.unzip

    val newSymbols = NoSymbols
      .withFunctions(functions ++ plainAccessors.flatten)
      .withSorts(symbols.sorts.values.toSeq)
      .withClasses(classes ++ plainClasses)
      .withTypeDefs(symbols.typeDefs.values.map(transformer.transform).toSeq)

    (newSymbols, ExtractionSummary.NoSummary)
  }
}

object ConcreteParents {
  def apply(trees: xlang.Trees)(using inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = {
    class Impl(override val s: trees.type, override val t: trees.type) extends ConcreteParents(s)(t)
    new Impl(trees, trees)
  }
}
