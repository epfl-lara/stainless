/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package methods

trait Trees extends throwing.Trees { self =>

  override protected def unapplyScrut(scrut: Expr, up: UnapplyPattern)(using s: Symbols): Expr =
    if (s.lookupFunction(up.id).exists(_.flags.exists { case IsMethodOf(_) => true case _ => false }) && up.recs.size == 1) {
      MethodInvocation(up.recs.head, up.id, up.tps, Seq(scrut))
    } else {
      super.unapplyScrut(scrut, up)
    }

  override protected def unapplyAccessor(unapplied: Expr, id: Identifier, up: UnapplyPattern)(using s: Symbols): Expr =
    if (s.lookupFunction(id).exists(_.flags.exists { case IsMethodOf(_) => true case _ => false })) {
      MethodInvocation(unapplied, id, Seq(), Seq())
    } else {
      super.unapplyAccessor(unapplied, id, up)
    }

  /** $encodingof `this` */
  case class This(ct: ClassType) extends Expr with Terminal {
    def getType(using Symbols): Type = ct.getType
  }

  /** $encodingof `super` */
  case class Super(ct: ClassType) extends Expr with Terminal {
    def getType(using Symbols): Type = ct.getType
  }

  /** $encodingof `receiver.id[tps](args)` */
  case class MethodInvocation(receiver: Expr, id: Identifier, tps: Seq[Type], args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(using s: Symbols): Type = widenTypeParameter(receiver) match {
      case ct: ClassType =>
        val optTfd = s.lookupFunction(id)
          .filter(fd => tps.size == fd.tparams.size && args.size == fd.params.size)
          .map(_.typed(tps))

        val optTcd = s.lookupClass(ct.id)
          .filter(cd => ct.tps.size == cd.tparams.size)
          .map(_.typed(ct.tps))

        (optTfd zip optTcd).headOption.flatMap { case (tfd, ctcd) =>
          tfd.fd.flags.collectFirst { case IsMethodOf(cid) => cid }
            .flatMap(cid => (ctcd +: ctcd.ancestors).find(_.id == cid))
            .map { tcd =>
              val tpSubst = tcd.tpSubst ++ tfd.tpSubst
              val it = new InstantiateThis(ctcd.toType)

              val instParams = tfd.fd.params.map { vd =>
                it.transform(typeOps.instantiateType(vd.getType, tpSubst))
              }

              val fdTpe = it.transform(typeOps.instantiateType(tfd.fd.getType, tpSubst))
              checkParamTypes(args, instParams, fdTpe)
            }
        }.getOrElse(Untyped)

      case _ => Untyped
    }
  }

  private[this] class InstantiateThis(override val s: self.type,
                                      override val t: self.type,
                                      thisType: ClassType) extends oo.ConcreteTreeTransformer(s, t) {

    def this(thisType: ClassType) = this(self, self, thisType)

    override def transform(tpe: Type): Type = tpe match {
      case TypeSelect(Some(This(_)), sel) =>
        super.transform(TypeSelect(Some(This(thisType)), sel))

      case _ => super.transform(tpe)
    }
  }


  type Symbols >: Null <: MethodsAbstractSymbols

  trait MethodsAbstractSymbols
    extends ImperativeAbstractSymbols
       with methods.DependencyGraph
       with methods.TypeOps { self0: Symbols =>

    // The only value that can be assigned to `trees`, but that has to be
    // done in a concrete class explicitly overriding `trees`
    // Otherwise, we can run into initialization issue.
    protected val trees: self.type
    // More or less the same here
    protected val symbols: this.type
    import symbols.given

    override protected def ensureWellFormedFunction(fd: FunDef): Unit = {
      val res = fd.getClassDef.fold(fd) { cd =>
        val it = new InstantiateThis(cd.typed.toType)
        it.transform(fd)
      }

      super.ensureWellFormedFunction(res)
    }

    override protected def ensureWellFormedClass(cd: ClassDef) = {
      super.ensureWellFormedClass(cd)

      val methods = cd.methods.map(getFunction)
      val fds = methods.filter(fd => !fd.getFieldDefPosition.isEmpty && fd.isField(isLazy = false))
      val fids = fds.map(_.id).toSet

      for (fd <- fds) {
        val fid = fd.id
        val position = fd.getFieldDefPosition.get

        exprOps.fold[Unit] {
          // allow access to fields defined previously
          case (MethodInvocation(This(_), xid, _, Seq()), _)
            if fids(xid) && lookupFunction(xid).forall {
              fd => (fd.isAccessor || fd.isField) && fd.getFieldDefPosition.forall(_ < position)
            } =>

          // allways allow access to constructor params
          case (ClassSelector(This(_), xid), _) =>

          // check that methods and functions don't access fields defined previously
          case (MethodInvocation(rec, xid, _, _), subs) =>
            val _ = subs.toList // force visit to children
            for (tid <- ((transitiveCallees(xid) + xid) & fids).find(tid => getFunction(tid).getFieldDefPosition.exists(_ >= position)))
              throw NotWellFormedException(fd,
                Some(s"field `$fid` can only refer to previous fields, not to `$tid`")
              )

          case (FunctionInvocation(xid, _, _), subs) =>
            val _ = subs.toList // force visit to children
            for (tid <- (transitiveCallees(xid) & fids).find(tid => getFunction(tid).getFieldDefPosition.exists(_ >= position)))
              throw NotWellFormedException(fd,
                Some(s"field `$fid` can only refer to previous fields, not to `$tid`")
              )

          case (_, subs) =>
            val _ = subs.toList // force visit to children
            ()
        }(fd.fullBody)
      }

      // Check that abstract methods are overridden by a method, a lazy val, or a constructor parameter (but not by a val)
      if (!cd.isAbstract) {
        val remainingAbstract = (cd +: cd.ancestors.map(_.cd)).reverse.foldLeft(Set.empty[Symbol]) {
          case (abstractSymbols, acd) =>
            val concreteSymbols = acd.methods
              .map(id => id.symbol -> getFunction(id))
              .filter { case (_, fd) => !fd.isAbstract }
              // fd.getFieldDefPosition is empty for lazy val's, non-empty for val's
              .filter { case (_, fd) =>
                (!fd.isAccessor || fd.isAccessorOfParam(acd)) && fd.getFieldDefPosition.isEmpty
              }
              .map(_._1).toSet
            val newAbstractSymbols = acd.methods.filter(id => getFunction(id).isAbstract).map(_.symbol).toSet
            abstractSymbols -- concreteSymbols ++ newAbstractSymbols
        }

        if (remainingAbstract.nonEmpty) {
          throw NotWellFormedException(cd,
            Some("abstract methods " + remainingAbstract.map(_.name).mkString(", ") + " were not overridden by a method, a lazy val, or a constructor parameter"))
        }
      }

      val ancestors = cd.ancestors(using this).map(cd => cd.id -> cd).toMap

      // Check that type members overrides are well-typed
      cd.typeMembers.foreach { id =>
        firstSuperTypeMember(id).foreach { sid =>
          val td = getTypeDef(id)
          val std = getTypeDef(sid)
          val cid = std.flags
            .collectFirst { case IsTypeMemberOf(cid) => cid }
            .getOrElse(throw NotWellFormedException(std, Some(s"must be a type member")))

          if (!(ancestors contains cid))
            throw NotWellFormedException(std, Some(s"first super is not a method of an ancestor"))

          val acd = ancestors(cid)

          if (td.isAbstract && !std.isAbstract)
            throw NotWellFormedException(td, Some(s"cannot override concrete type with abstract type."))

          if (std.isFinal)
            throw NotWellFormedException(td, Some(s"cannot override final type: $std"))

          if (td.tparams.size != std.tparams.size)
            throw NotWellFormedException(td, Some(s"type parameters length are not equal"))
        }
      }

      // Check that method overrides are well-typed
      cd.methods.foreach { id =>
        firstSuperMethod(id).foreach { sid =>
          val sfd = getFunction(sid)
          val cid = sfd.flags
            .collectFirst { case IsMethodOf(cid) => cid }
            .getOrElse(throw NotWellFormedException(sfd, Some(s"must be a method")))

          if (!(ancestors contains cid))
            throw NotWellFormedException(sfd, Some(s"first super is not a method of an ancestor"))

          val acd = ancestors(cid)

          val fd = getFunction(id)

          if (fd.isAbstract && !sfd.isAbstract)
            throw NotWellFormedException(fd, Some(s"cannot override concrete function with abstract function."))

          if (sfd.isFinal)
            throw NotWellFormedException(fd, Some(s"cannot override final function:\n$sfd"))

          if (fd.tparams.size != sfd.tparams.size)
            throw NotWellFormedException(fd, Some(s"type parameters length are not equal"))

          val it = new InstantiateThis(cd.typed.toType)

          val tpSubst = (fd.typeArgs zip sfd.typeArgs).toMap

          (fd.typeArgs zip sfd.typeArgs).foreach { case (tp, stp) =>
            val TypeBounds(lo, hi, _) = tp.bounds
            val TypeBounds(slo, shi, _) = stp.bounds

            if (!isSubtypeOf(
              it.transform(typeOps.instantiateType(lo, tpSubst)),
              it.transform(typeOps.instantiateType(slo, acd.tpSubst)))) {
                throw NotWellFormedException(fd, Some(s"TODO"))
              }

            if (!isSubtypeOf(
              it.transform(typeOps.instantiateType(shi, acd.tpSubst)),
              it.transform(typeOps.instantiateType(hi, tpSubst)))) {
                throw NotWellFormedException(fd, Some("TODO"))
              }
          }

          if (fd.params.size != sfd.params.size)
            throw NotWellFormedException(fd, Some("Method override does not have the same number of parameters as parent"))

          (fd.params zip sfd.params).foreach { case (vd, svd) =>
            val aTpe = it.transform(typeOps.instantiateType(svd.getType, acd.tpSubst))
            val tpe = it.transform(typeOps.instantiateType(vd.getType, tpSubst))
            if (!isSubtypeOf(aTpe, tpe))
              throw NotWellFormedException(fd, Some(s"Parameter ${vd.id} of type $tpe is not a subtype of ancestor $aTpe"))
          }

          val t1 = it.transform(typeOps.instantiateType(fd.getType, tpSubst))
          val t2 = it.transform(typeOps.instantiateType(sfd.getType, acd.tpSubst))

          if (!isSubtypeOf(t1.getType, t2.getType))
            throw NotWellFormedException(fd, Some(s"return type ${t1} is not a subtype of ${t2}"))
        }
      }
    }
  }


  case class IsAccessor(id: Option[Identifier]) extends Flag("accessor", id.toSeq)
  case class IsMethodOf(id: Identifier) extends Flag("method", Seq(id))

  case object ValueClass extends Flag("valueClass", Seq.empty)
  case class FieldDefPosition(i: Int) extends Flag("fieldDefPosition", Seq(i))

  implicit class ClassDefWrapper(cd: ClassDef) {
    def isSealed: Boolean = cd.flags contains IsSealed
    def isAbstract: Boolean = cd.flags contains IsAbstract
    def isLibrary: Boolean = cd.flags contains Library
    def isGhost: Boolean = cd.flags contains Ghost
    def isValueClass: Boolean = cd.flags contains ValueClass

    def methods(using s: Symbols): Seq[SymbolIdentifier] = {
      s.functions.values
        .filter(_.flags contains IsMethodOf(cd.id))
        .map(_.id.asInstanceOf[SymbolIdentifier]).toSeq
    }

    def invariant(using s: Symbols): Option[FunDef] = {
      methods map s.functions find (_.flags contains IsInvariant)
    }
  }

  extension (fd: FunDef) {
    def isMethod: Boolean =
      fd.flags exists { case IsMethodOf(_) => true case _ => false }

    def isGhost: Boolean = fd.flags contains Ghost

    def isSynthetic: Boolean = fd.flags contains Synthetic

    def getClassId: Option[Identifier] =
      fd.flags collectFirst { case IsMethodOf(id) => id }

    def getFieldDefPosition: Option[Int] =
      fd.flags collectFirst { case FieldDefPosition(i) => i }

    def getClassDef(using s: Symbols): Option[ClassDef] =
      getClassId flatMap s.lookupClass

    def isAccessor: Boolean =
      fd.flags exists { case IsAccessor(_) => true case _ => false }

    def isAccessorOfParam(cd: ClassDef)(using Symbols): Boolean =
      fd.flags exists {
        case IsAccessor(Some(id)) => cd.fields.map(_.id).contains(id)
        case _ => false
      }

    def isAccessor(id: Identifier): Boolean =
      fd.flags exists { case IsAccessor(Some(id2)) if id == id2 => true case _ => false }

    def isField: Boolean =
      fd.flags exists { case IsField(_) => true case _ => false }

    def isField(isLazy: Boolean): Boolean =
      fd.flags exists { case IsField(`isLazy`) => true case _ => false }

    def isSetter: Boolean = isAccessor && fd.id.name.endsWith("_=") && fd.params.size == 1
    def isGetter: Boolean = isAccessor && fd.params.isEmpty

    def isFinal: Boolean = fd.flags contains Final

    def isAbstract(using Symbols): Boolean = {
      (fd.flags contains IsAbstract) ||
      (!isExtern && !hasBody && !isSynthetic && fd.getClassDef.forall(_.isAbstract))
    }

    def hasBody: Boolean = exprOps.BodyWithSpecs(fd.fullBody).hasBody

    def isInvariant: Boolean = fd.flags contains IsInvariant
    def isExtern: Boolean = fd.flags contains Extern
    def isLaw: Boolean = fd.flags contains Law
    def isLibrary: Boolean = fd.flags contains Library
  }

  override def getDeconstructor(that: inox.ast.Trees): inox.ast.TreeDeconstructor { val s: self.type; val t: that.type } = that match {
    case tree: (Trees & that.type) => // The `& that.type` trick allows to convince scala that `tree` and `that` are actually equal...
      class DeconstructorImpl(override val s: self.type, override val t: tree.type & that.type) extends ConcreteTreeDeconstructor(s, t)
      new DeconstructorImpl(self, tree)

    case _ => super.getDeconstructor(that)
  }
}

class ExprOps(override val trees: Trees) extends throwing.ExprOps(trees)

trait Printer extends throwing.Printer {
  protected val trees: Trees
  import trees._

  override def ppBody(tree: Tree)(using ctx: PrinterContext): Unit = tree match {
    case cd: ClassDef =>
      super.ppBody(cd)
      ctx.opts.symbols.foreach { case (given Symbols) =>
        if (cd.methods.nonEmpty || cd.typeMembers.nonEmpty) {
          p""" {
            |  ${typeDefs(cd.typeMembers)}
            |
            |  ${functions(cd.methods)}
          |}"""
        }
      }

    case MethodInvocation(caller, id, tps, args) =>
      p"$caller.$id${nary(tps, ", ", "[", "]")}"
      if (args.nonEmpty) {
        // TODO: handle implicit arguments and/or default values
        p"($args)"
      }

    case This(_) => p"this"

    case Super(_) => p"super"

    case _ => super.ppBody(tree)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(MethodInvocation(_, _, _, args))) => !args.contains(ex)
    case _ => super.requiresParentheses(ex, within)
  }
}

trait TreeDeconstructor extends throwing.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): Deconstructed[t.Expr] = e match {
    case s.MethodInvocation(rec, id, tps, args) =>
      (Seq(id), Seq(), rec +: args, tps, Seq(), (ids, _, es, tps, _) => t.MethodInvocation(es(0), ids.head, tps, es.tail))

    case s.This(ct) =>
      (Seq(), Seq(), Seq(), Seq(ct), Seq(), (_, _, _, tps, _) => t.This(tps.head.asInstanceOf[t.ClassType]))

    case s.Super(ct) =>
      (Seq(), Seq(), Seq(), Seq(ct), Seq(), (_, _, _, tps, _) => t.Super(tps.head.asInstanceOf[t.ClassType]))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(f: s.Flag): DeconstructedFlag = f match {
    case s.IsMethodOf(id) => (Seq(id), Seq(), Seq(), (ids, _, _) => t.IsMethodOf(ids.head))
    case s.IsAccessor(id) => (id.toSeq, Seq(), Seq(), (ids, _, _) => t.IsAccessor(ids.headOption))
    case s.ValueClass => (Seq(), Seq(), Seq(), (_, _, _) => t.ValueClass)
    case s.FieldDefPosition(i) => (Seq(), Seq(), Seq(), (_, _, _) => t.FieldDefPosition(i))
    case _ => super.deconstruct(f)
  }
}

class ConcreteTreeDeconstructor(override val s: Trees, override val t: Trees) extends TreeDeconstructor