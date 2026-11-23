/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package xlang

import stainless.ast.SymbolIdentifier
import scala.collection.mutable.{Map => MutableMap}

/** Encodes the extension of concrete classes, as later phases only let abstract classes be extended.
 *
 *  The frontend flags the concrete classes that may be extended, which aren't final, with [[IsExtensible]].
 *  This phase drops the flag from the classes that stay concrete, and [[oo.AdtSpecialization]] drops it from
 *  the extended classes, which this phase makes abstract. The frontend also extracts the arguments that a
 *  class passes to the constructor of a concrete parent as overrides of the accessors of the parent's fields
 *  (see `extractParentArguments` in the frontend), so it doesn't mark these accessors as final. This phase
 *  marks them as final in the classes that stay concrete. For example,
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
 * @extensible class C(x: BigInt) { def x: BigInt = this.x; def m: BigInt = this.x + 1 } // `x` is a field and its accessor
 * case class D(y: BigInt) extends C { override def x: BigInt = this.y * 2; override def m: BigInt = y }
 * def test = new C(5).x + D(3).x
 * }}}
 *
 *  This phase makes each extended concrete class `C` abstract, with abstract accessors for its fields. It
 *  moves the fields to a new final subclass of `C`, also named `C`, which stands for the instances of `C` that
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
 *  mutable fields, whose values may diverge from these arguments, and patterns on extended case classes.
 *  The new subclass of a member class is a member of the same class, and that of a local class is defined
 *  next to it.
 */
class ConcreteParents(override val s: Trees)(override val t: s.type)
                     (using override val context: inox.Context) extends ExtractionPipeline { self =>
  import s._

  override def invalidate(id: Identifier): Unit = ()

  // Identifiers are stable across runs
  private val plainIds = MutableMap[Identifier, Identifier]()
  private val plainAccessorIds = MutableMap[Identifier, SymbolIdentifier]()

  override def extract(symbols: s.Symbols): (t.Symbols, ExtractionSummary) = {
    given s.Symbols = symbols

    // The parents of local classes, which may be global classes
    val localParents: Seq[Identifier] = symbols.functions.values.toSeq.flatMap { fd =>
      exprOps.collect[Identifier] {
        case LetClass(lcds, _) => lcds.flatMap(_.parents.collect { case ct: ClassType => ct.id }).toSet
        case _ => Set.empty
      } (fd.fullBody)
    }.filter(symbols.lookupClass(_).isDefined)

    val extended: Set[Identifier] = (symbols.classes.values.toSeq.flatMap(_.parents.map(_.id)) ++ localParents)
      .filter(id => !symbols.getClass(id).flags.contains(IsAbstract))
      .toSet

    // The extended concrete local classes, which are encoded in the same way within their `LetClass`
    val localClasses: Map[Identifier, LocalClassDef] = symbols.functions.values.toSeq.flatMap { fd =>
      exprOps.collect[LocalClassDef] {
        case LetClass(lcds, _) => lcds.toSet
        case _ => Set.empty
      } (fd.fullBody)
    }.map(lcd => lcd.id -> lcd).toMap

    val localExtended: Set[Identifier] = localClasses.values.toSeq
      .flatMap(_.parents.collect { case ct: ClassType => ct.id case lct: LocalClassType => lct.id })
      .filter(id => localClasses.get(id).exists(!_.flags.contains(IsAbstract)))
      .toSet

    def checkFields(id: Identifier, fields: Seq[ValDef]): Unit =
      fields.find(_.flags.contains(IsVar)).foreach { vd =>
        context.reporter.fatalError(vd.getPos, s"Stainless does not support mutable fields in extended concrete classes (${vd.id.asString} of ${id.asString})")
      }

    for (id <- extended) {
      val cd = symbols.getClass(id)
      if (cd.flags.contains(IsObject))
        context.reporter.fatalError(cd.getPos, s"Objects cannot be extended (${cd.id.asString})")
      checkFields(id, cd.fields)
    }
    for (id <- localExtended) checkFields(id, localClasses(id).fields)

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

    // The same for local classes
    val localFieldOwner: Map[Identifier, Identifier] = localExtended.toSeq.flatMap { id =>
      localClasses(id).fields.map(_.id -> id)
    }.toMap

    val localAccessors: Map[Identifier, LocalMethodDef] = localExtended.toSeq.flatMap { id =>
      localClasses(id).methods.flatMap { fd =>
        fd.flags.collectFirst { case IsAccessor(Some(fid)) if localFieldOwner.get(fid) == Some(id) && fd.params.isEmpty => fid -> fd }
      }
    }.toMap

    for ((fid, cid) <- localFieldOwner if !localAccessors.contains(fid))
      context.reporter.internalError(s"No accessor for field ${fid.asString} of ${cid.asString}")

    def plainAccessorId(id: Identifier): SymbolIdentifier = plainAccessorIds.getOrElseUpdate(id, id match {
      case sid: SymbolIdentifier => SymbolIdentifier(sid.symbol)
      case _ => context.reporter.internalError(s"Unexpected accessor identifier ${id.asString}")
    })

    def abstractFlags(flags: Seq[Flag]): Seq[Flag] = (flags.filter {
      case Final | Private | Inline | IsAccessor(_) => false
      case _ => true
    } ++ Seq(IsAbstract, IsAccessor(None))).distinct

    def plainFlags(flags: Seq[Flag]): Seq[Flag] = (flags.filter {
      case IsSealed | IsAbstract | IsExtensible => false
      case _ => true
    } :+ Synthetic).distinct

    // The type parameters of the new local subclasses
    val localPlainTparams: Map[Identifier, Seq[TypeParameterDef]] = localExtended.toSeq.map { id =>
      id -> exprOps.freshenTypeParams(localClasses(id).typeArgs).map(tp => TypeParameterDef(tp).copiedFrom(tp))
    }.toMap

    def localPlainType(lct: LocalClassType): LocalClassType =
      LocalClassType(plainId(lct.id), localPlainTparams(lct.id), lct.tps, Seq(lct)).copiedFrom(lct)

    /** The local class `lcd`, made abstract, and its new subclass. */
    def localEncoding(lcd: LocalClassDef): Seq[LocalClassDef] = {
      val abstractLcd = lcd.copy(
        fields = Seq.empty,
        methods = lcd.methods.map { fd =>
          if (!fd.flags.exists { case IsAccessor(Some(fid)) => localAccessors.get(fid).exists(_.id == fd.id) case _ => false }) fd
          else fd.copy(fullBody = NoTree(fd.returnType).copiedFrom(fd), flags = abstractFlags(fd.flags)).copiedFrom(fd)
        },
        flags = (lcd.flags :+ IsAbstract).distinct
      ).copiedFrom(lcd)

      val tparams = localPlainTparams(lcd.id)
      val instantiator = new typeOps.TypeInstantiator((lcd.typeArgs zip tparams.map(_.tp)).toMap)
      val lct = LocalClassType(lcd.id, lcd.tparams, tparams.map(_.tp), lcd.parents).copiedFrom(lcd)
      val plainLct = localPlainType(lct)
      val pid = plainLct.id

      val accessorDefs = lcd.fields.map { vd =>
        val tpe = instantiator.transform(vd.tpe)
        LocalMethodDef(
          plainAccessorId(localAccessors(vd.id).id),
          Seq.empty,
          Seq.empty,
          tpe,
          LocalClassSelector(LocalThis(plainLct).copiedFrom(vd), vd.id, tpe).copiedFrom(vd),
          Seq(Synthetic, IsAccessor(Some(vd.id)), IsMethodOf(pid))
        ).copiedFrom(vd)
      }

      val plainLcd = LocalClassDef(
        pid, tparams, Seq(lct.toClassType), lcd.fields.map(instantiator.transform), accessorDefs, Seq.empty, plainFlags(lcd.flags)
      ).copiedFrom(lcd)

      Seq(abstractLcd, plainLcd)
    }

    // The classes that stay concrete are no longer extensible
    def staysConcrete(id: Identifier, flags: Seq[Flag]): Boolean =
      flags.contains(IsExtensible) && !extended(id) && !localExtended(id)

    def concreteFlags(id: Identifier, flags: Seq[Flag]): Seq[Flag] =
      if (staysConcrete(id, flags)) flags.filterNot(_ == IsExtensible) else flags

    // The frontend doesn't mark the accessors of the fields of extensible classes as final, as the arguments
    // to the constructors of their subclasses override them. They are final if their class stays concrete.
    def methodFlags(fd: FunDef, cid: Identifier, cflags: Seq[Flag], fields: Seq[ValDef]): Seq[Flag] = {
      val isFieldAccessor = fd.flags.exists { case IsAccessor(Some(fid)) => fields.exists(_.id == fid) case _ => false }
      if (isFieldAccessor && staysConcrete(cid, cflags)) (fd.flags :+ Final).distinct else fd.flags
    }

    def stripLocal(lcd: LocalClassDef): LocalClassDef = lcd.copy(
      methods = lcd.methods.map(md => md.copy(flags = methodFlags(md.toFunDef, lcd.id, lcd.flags, lcd.fields)).copiedFrom(md)),
      flags = concreteFlags(lcd.id, lcd.flags)
    ).copiedFrom(lcd)

    object transformer extends ConcreteOOSelfTreeTransformer(self.s, self.s) {
      override def transform(e: Expr): Expr = e match {
        case ClassConstructor(ct, args) if extended(ct.id) =>
          ClassConstructor(
            ClassType(plainId(ct.id), ct.tps.map(transform)).copiedFrom(ct),
            args.map(transform)
          ).copiedFrom(e)

        // The new subclass of a member class is a member of the same class (see [[MemberClasses]])
        case PathClassConstructor(path, ct, args) if extended(ct.id) =>
          PathClassConstructor(
            transform(path),
            ClassType(plainId(ct.id), ct.tps.map(transform)).copiedFrom(ct),
            args.map(transform)
          ).copiedFrom(e)

        case ClassSelector(recv, field) if fieldOwner.contains(field) =>
          MethodInvocation(transform(recv), accessors(field).id, Seq.empty, Seq.empty).copiedFrom(e)

        // The deconstructor of `LetClass` doesn't transform the methods of local classes with this transformer
        case LetClass(lcds, body) =>
          // The accessors of the new subclasses select their fields
          val newLcds = lcds.map(stripLocal).flatMap { lcd =>
            val tlcd = lcd.copy(methods = lcd.methods.map(md => LocalMethodDef(transform(md.toFunDef)))).copiedFrom(lcd)
            if (localExtended(lcd.id)) localEncoding(tlcd) else Seq(tlcd)
          }
          super.transform(LetClass(newLcds, body).copiedFrom(e))

        case LocalClassConstructor(lct, args) if localExtended(lct.id) =>
          LocalClassConstructor(transform(localPlainType(lct)).asInstanceOf[LocalClassType], args.map(transform)).copiedFrom(e)

        case LocalClassSelector(recv, field, _) if localFieldOwner.contains(field) =>
          val accessor = localAccessors(field)
          LocalMethodInvocation(
            transform(recv),
            ValDef(accessor.id, transform(FunctionType(Seq.empty, accessor.returnType))).toVariable,
            Seq.empty, Seq.empty, Seq.empty
          ).copiedFrom(e)

        case _ => super.transform(e)
      }

      override def transform(pat: Pattern): Pattern = pat match {
        case ClassPattern(_, ct, _) if extended(ct.id) || localExtended(ct.id) =>
          context.reporter.fatalError(pat.getPos, s"Stainless does not support patterns on the extended case class ${ct.id.asString}")
        case PathClassPattern(_, _, ct, _) if extended(ct.id) =>
          context.reporter.fatalError(pat.getPos, s"Stainless does not support patterns on the extended case class ${ct.id.asString}")
        case _ => super.transform(pat)
      }

      override def transform(flag: Flag): Flag = flag match {
        case ClassParamInit(cid) if extended(cid) => ClassParamInit(plainId(cid))
        case _ => super.transform(flag)
      }
    }

    // The accessors of the fields of extended classes become abstract
    def abstractAccessor(fd: FunDef): FunDef =
      fd.copy(fullBody = NoTree(fd.returnType).copiedFrom(fd), flags = abstractFlags(fd.flags)).copiedFrom(fd)

    val functions = symbols.functions.values.toSeq.map { fd =>
      val fd1 = fd.getClassId.map(symbols.getClass) match {
        case Some(cd) => fd.copy(flags = methodFlags(fd, cd.id, cd.flags, cd.fields))
        case None => fd
      }
      val accessorOf = fd.flags.collectFirst { case IsAccessor(Some(fid)) if accessors.get(fid).exists(_.id == fd.id) => fid }
      transformer.transform(if (accessorOf.isDefined) abstractAccessor(fd1) else fd1)
    }

    val classes = symbols.classes.values.toSeq.map(cd => cd.copy(flags = concreteFlags(cd.id, cd.flags)).copiedFrom(cd)).map { cd =>
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
        plainFlags(cd.flags).map(transformer.transform)
      ).copiedFrom(cd)

      val accessorDefs = cd.fields.map { vd =>
        val accessor = accessors(vd.id)
        val accessorId = plainAccessorId(accessor.id)
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
