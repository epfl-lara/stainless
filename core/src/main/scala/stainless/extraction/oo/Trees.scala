/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction
package oo

import scala.collection.mutable.{Map => MutableMap}

trait Trees extends holes.Trees { self =>

  /* ========================================
   *         EXPRESSIONS AND TYPES
   * ======================================== */

  /** $encodingof `receiver.id[tps](args)` */
  case class MethodInvocation(receiver: Expr, id: Identifier, tps: Seq[Type], args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = receiver.getType match {
      case ct: ClassType => (s.lookupFunction(id, tps), s.lookupClass(ct.id)) match {
        case (Some(tfd), Some(cd)) => s.instantiateType(tfd.returnType, (cd.typeArgs zip ct.tps).toMap)
        case _ => Untyped
      }
      case _ => Untyped
    }
  }

  /** $encodingof `new id(args)` */
  case class ClassConstructor(ct: ClassType, args: Seq[Expr]) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = ct.lookupClass match {
      case Some(tcd) => checkParamTypes(args.map(_.getType), tcd.fields.map(_.tpe), ct)
      case _ => Untyped
    }
  }

  /** $encodingof `expr.selector` */
  case class ClassSelector(expr: Expr, selector: Identifier) extends Expr with CachingTyped {
    protected def computeType(implicit s: Symbols): Type = expr.getType match {
      case ct: ClassType =>
        ct.getField(selector).map(_.tpe).orElse((s.lookupFunction(selector), s.lookupClass(ct.id, ct.tps)) match {
          case (Some(fd), Some(tcd)) =>
            Some(s.instantiateType(fd.returnType, (tcd.cd.tparams.map(_.tp) zip tcd.tps).toMap))
          case _ =>
            None
        }).getOrElse(Untyped)
      case _ => Untyped
    }
  }

  /** $encodingof `this` */
  case class This(ct: ClassType) extends Expr {
    def getType(implicit s: Symbols): Type = ct
  }

  /** Type associated to instances of [[ClassConstructor]] */
  class ClassType(id: Identifier, tps: Seq[Type]) extends ADTType(id, tps) {
    def lookupClass(implicit s: Symbols): Option[TypedClassDef] = s.lookupClass(id, tps)
    def tcd(implicit s: Symbols): TypedClassDef = s.getClass(id, tps)

    def getField(selector: Identifier)(implicit s: Symbols): Option[ValDef] = {
      def rec(tcd: TypedClassDef): Option[ValDef] =
        tcd.fields.collectFirst { case vd @ ValDef(`selector`, _, _) => vd }.orElse(tcd.parent.flatMap(rec))
      lookupClass.flatMap(rec)
    }
  }

  /** Companion object of [[ClassType]].
    *
    * As [[ClassType]] extends the [[ADTType]] case class, we provide the [[apply]]
    * and [[unapply]] methods for [[ClassType]] here. 
    */
  object ClassType {
    def apply(id: Identifier, tps: Seq[Type]): ClassType = new ClassType(id, tps)
    def unapply(tpe: Type): Option[(Identifier, Seq[Type])] = tpe match {
      case ct: ClassType => Some((ct.id, ct.tps))
      case _ => None
    }
  }


  /* ========================================
   *              EXTRACTORS
   * ======================================== */

  override def getDeconstructor(that: inox.ast.Trees) = that match {
    case tree: Trees => new TreeDeconstructor {
      protected val s: self.type = self
      protected val t: tree.type = tree
    }.asInstanceOf[TreeDeconstructor { val s: self.type; val t: that.type }]

    case _ => super.getDeconstructor(that)
  }


  /* ========================================
   *             DEFINITIONS
   * ======================================== */

  class ClassDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val parent: Option[Identifier],
    val fields: Seq[ValDef],
    val methods: Seq[SymbolIdentifier],
    val flags: Set[Flag]
  ) extends Definition {

    def root(implicit s: Symbols): ClassDef = parent.map(id => s.getClass(id).root).getOrElse(this)

    def ancestors(implicit s: Symbols): Seq[ClassDef] = parent.map(id => s.getClass(id)) match {
      case Some(pcd) => pcd +: pcd.ancestors
      case None => Seq.empty
    }

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[Type])(implicit s: Symbols): TypedClassDef = TypedClassDef(this, tps)
    def typed(implicit s: Symbols): TypedClassDef = typed(tparams.map(_.tp))

    def copy(
      id: Identifier = this.id,
      tparams: Seq[TypeParameterDef] = this.tparams,
      parent: Option[Identifier] = this.parent,
      fields: Seq[ValDef] = this.fields,
      methods: Seq[SymbolIdentifier] = this.methods,
      flags: Set[Flag] = this.flags
    ): ClassDef = new ClassDef(id, tparams, parent, fields, methods, flags)
  }

  case class TypedClassDef(cd: ClassDef, tps: Seq[Type])(implicit val symbols: Symbols) extends Tree {
    lazy val id: Identifier = cd.id
    lazy val root: TypedClassDef = cd.root.typed(tps)
    lazy val ancestors: Seq[TypedClassDef] = cd.ancestors.map(_.typed(tps))

    lazy val parent: Option[TypedClassDef] = cd.parent.map(id => symbols.getClass(id, tps))

    lazy val fields: Seq[ValDef] = {
      lazy val tmap = (cd.typeArgs zip tps).toMap
      if (tmap.isEmpty) cd.fields
      else cd.fields.map(vd => vd.copy(tpe = symbols.instantiateType(vd.tpe, tmap)))
    }

    def toType = ClassType(id, tps)
  }

  case class ClassLookupException(id: Identifier) extends LookupException(id, "class")


  type Symbols >: Null <: AbstractSymbols

  trait AbstractSymbols extends super.AbstractSymbols with TypeOps { self0: Symbols =>
    val classes: Map[Identifier, ClassDef]

    private val typedClassCache: MutableMap[(Identifier, Seq[Type]), Option[TypedClassDef]] = MutableMap.empty
    def lookupClass(id: Identifier): Option[ClassDef] = classes.get(id)
    def lookupClass(id: Identifier, tps: Seq[Type]): Option[TypedClassDef] =
      typedClassCache.getOrElseUpdate(id -> tps, lookupClass(id).map(_.typed(tps)))

    def getClass(id: Identifier): ClassDef = lookupClass(id).getOrElse(throw ClassLookupException(id))
    def getClass(id: Identifier, tps: Seq[Type]): TypedClassDef = lookupClass(id, tps).getOrElse(throw ClassLookupException(id))

    override def asString(implicit opts: PrinterOptions): String = {
      classes.map(p => prettyPrint(p._2, opts)).mkString("\n\n") +
        "\n\n-----------\n\n" +
        super.asString
    }

    override def transform(t: inox.ast.TreeTransformer { val s: self.type }): t.t.Symbols = t.t match {
      case tree: Trees =>
        val tt = t.asInstanceOf[inox.ast.TreeTransformer { val s: self.type; val t: tree.type }]
        SymbolTransformer(tt).transform(this).asInstanceOf[t.t.Symbols]
      case _ => super.transform(t)
    }

    override def equals(that: Any): Boolean = super.equals(that) && (that match {
      case sym: AbstractSymbols => classes == sym.classes
      case _ => false
    })

    override def hashCode: Int = super.hashCode + 31 * classes.hashCode

    def withClasses(classes: Seq[ClassDef]): Symbols
  }

  case object IsInvariant extends Flag("invariant", Seq.empty)
  case object IsAbstract extends Flag("abstract", Seq.empty)
  case object IsMethod extends Flag("method", Seq.empty)


  /* ========================================
   *               PRINTERS
   * ======================================== */

  protected def withSymbols[T <: Tree](elems: Seq[Either[T, Identifier]], header: String)
                                      (implicit ctx: PrinterContext): Unit = {
    new StringContext("" +: (List.fill(elems.size - 1)("\n\n") :+ "") : _*).p((for (e <- elems) yield e match {
      case Left(d) => d
      case Right(id) => {
        implicit pctx2: PrinterContext =>
          p"<unknown> $header $id"(pctx2)
      }: PrintWrapper
    }) : _*)
  }

  protected def functions(funs: Seq[Identifier]): PrintWrapper = {
    implicit pctx: PrinterContext =>
      withSymbols(funs.map(id => pctx.opts.symbols.flatMap(_.lookupFunction(id)) match {
        case Some(cd) => Left(cd)
        case None => Right(id)
      }), "def")
  }

  override def ppBody(tree: Tree)(implicit ctx: PrinterContext): Unit = tree match {

    case cd: ClassDef =>
      p"class ${cd.id}"
      p"${nary(cd.tparams, ", ", "[", "]")}"
      if (cd.fields.nonEmpty) p"(${cd.fields})"

      cd.parent.foreach { id =>
        p" extends $id${nary(cd.tparams, ", ", "[", "]")}"
      }

      if (cd.methods.nonEmpty) {
        p""" {
            |  ${functions(cd.methods)}
            |}"""
      }

    case ClassConstructor(ct, args) =>
      p"$ct($args)"

    case ClassSelector(cls, selector) =>
      p"$cls.$selector"

    case MethodInvocation(caller, id, tps, args) =>
      p"$caller.$id${nary(tps, ", ", "[", "]")}"
      if (args.nonEmpty) {
        // TODO: handle implicit arguments and/or default values
        p"($args)"
      }

    case This(_) => p"this"

    case (tcd: TypedClassDef) => p"typed class ${tcd.id}[${tcd.tps}]"

    case _ => super.ppBody(tree)
  }

  override protected def requiresParentheses(ex: Tree, within: Option[Tree]): Boolean = (ex, within) match {
    case (_, Some(_: ClassConstructor)) => false
    case (_, Some(MethodInvocation(_, _, _, args))) => !args.contains(ex)
    case _ => super.requiresParentheses(ex, within)
  }
}


trait TypeOps extends ast.TypeOps {
  protected val trees: Trees
  import trees._

  override protected def instantiationConstraints(toInst: Type, bound: Type, isUpper: Boolean): Seq[Subtyping] = (toInst, bound) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => unsolvable
    case (ct1: ClassType, ct2: ClassType) =>
      val cd1 = ct1.tcd.cd
      val cd2 = ct2.tcd.cd
      val (cl, ch) = if (isUpper) (cd1, cd2) else (cd2, cd1)
      if (!((cl == ch) || (cl.ancestors contains ch))) unsolvable
      else {
        for {
          (tp, (t1, t2)) <- cd1.typeArgs zip (ct1.tps zip ct2.tps)
          variance <- if (tp.isCovariant) Seq(isUpper) else if (tp.isContravariant) Seq(!isUpper) else Seq(true, false)
          constr <- instantiationConstraints(t1, t2, variance)
        } yield constr
      }

    case _ => super.instantiationConstraints(toInst, bound, isUpper)
  }

  override protected def typeBound(tp1: Type, tp2: Type, upper: Boolean): Type = (tp1, tp2) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => Untyped
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => Untyped
    case (ct1: ClassType, ct2: ClassType) =>
      if (ct1.tps.size != ct2.tps.size) Untyped
      else {
        val cd1 = ct1.tcd.cd
        val cd2 = ct2.tcd.cd
        val an1 = cd1 +: cd1.ancestors
        val an2 = cd2 +: cd2.ancestors

        val tps = (cd1.typeArgs zip (ct1.tps zip ct2.tps)).map { case (tp, (t1, t2)) =>
          if (tp.isCovariant) typeBound(t1, t2, upper)
          else if (tp.isContravariant) typeBound(t1, t2, !upper)
          else if (t1 == t2) t1
          else Untyped
        }

        val bound = if (upper) {
          // Upper bound
          (an1.reverse zip an2.reverse)
            .takeWhile(((_: ClassDef) == (_: ClassDef)).tupled)
            .lastOption.map(_._1)
        } else {
          // Lower bound
          if (an1 contains cd2) Some(cd1)
          else if (an2 contains cd1) Some(cd2)
          else None
        }

        bound.map(_.typed(tps).toType).getOrElse(Untyped).unveilUntyped
      }

    case _ => super.typeBound(tp1, tp2, upper)
  }

  override protected def unificationConstraints(t1: Type, t2: Type, free: Seq[TypeParameter]): List[(TypeParameter, Type)] = (t1, t2) match {
    case (ct: ClassType, _) if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) if ct.lookupClass.isEmpty => unsolvable
    case (ct1: ClassType, ct2: ClassType) if ct1.tcd.cd == ct2.tcd.cd =>
      (ct1.tps zip ct2.tps).toList flatMap (p => unificationConstraints(p._1, p._2, free))
    case _ => super.unificationConstraints(t1, t2, free)
  }

  override protected def unificationSolution(const: List[(Type, Type)]): List[(TypeParameter, Type)] = const match {
    case (ct: ClassType, _) :: tl if ct.lookupClass.isEmpty => unsolvable
    case (_, ct: ClassType) :: tl if ct.lookupClass.isEmpty => unsolvable
    case (ct1: ClassType, ct2: ClassType) :: tl if ct1.tcd.cd == ct2.tcd.cd =>
      unificationSolution((ct1.tps zip ct2.tps).toList ++ tl)
    case _ => super.unificationSolution(const)
  }
}

trait TreeDeconstructor extends holes.TreeDeconstructor {
  protected val s: Trees
  protected val t: Trees

  override def deconstruct(e: s.Expr): (Seq[s.Variable], Seq[s.Expr], Seq[s.Type], (Seq[t.Variable], Seq[t.Expr], Seq[t.Type]) => t.Expr) = e match {
    case s.MethodInvocation(rec, id, tps, args) =>
      (Seq(), rec +: args, tps, (_, es, tps) => t.MethodInvocation(es(0), id, tps, es.tail))

    case s.ClassConstructor(ct, args) =>
      (Seq(), args, Seq(ct), (_, es, tps) => t.ClassConstructor(tps.head.asInstanceOf[t.ClassType], es))

    case s.ClassSelector(expr, selector) =>
      (Seq(), Seq(expr), Seq(), (_, es, _) => t.ClassSelector(es.head, selector))

    case s.This(ct) =>
      (Seq(), Seq(), Seq(ct), (_, _, tps) => t.This(tps.head.asInstanceOf[t.ClassType]))

    case _ => super.deconstruct(e)
  }

  override def deconstruct(tpe: s.Type): (Seq[s.Type], Seq[s.Flag], (Seq[t.Type], Seq[t.Flag]) => t.Type) = tpe match {
    case s.ClassType(id, tps) => (tps, Seq(), (tps, _) => t.ClassType(id, tps))
    case _ => super.deconstruct(tpe)
  }

  override def deconstruct(f: s.Flag): (Seq[s.Expr], Seq[s.Type], (Seq[t.Expr], Seq[t.Type]) => t.Flag) = f match {
    case s.IsInvariant => (Seq(), Seq(), (_, _) => t.IsInvariant)
    case s.IsAbstract => (Seq(), Seq() ,(_, _) => t.IsAbstract)
    case s.IsMethod => (Seq(), Seq(), (_, _) => t.IsMethod)
    case _ => super.deconstruct(f)
  }
}

trait SimpleSymbolTransformer extends inox.ast.SimpleSymbolTransformer {
  val s: Trees
  val t: Trees

  protected def transformClass(cd: s.ClassDef): t.ClassDef

  override def transform(syms: s.Symbols): t.Symbols = super.transform(syms)
    .withClasses(syms.classes.values.toSeq.map(transformClass))
}

object SymbolTransformer {
  def apply(trans: inox.ast.TreeTransformer { val s: Trees; val t: Trees }): inox.ast.SymbolTransformer {
    val s: trans.s.type
    val t: trans.t.type
  } = new SimpleSymbolTransformer {
    val s: trans.s.type = trans.s
    val t: trans.t.type = trans.t

    protected def transformFunction(fd: s.FunDef): t.FunDef = trans.transform(fd)
    protected def transformADT(adt: s.ADTDefinition): t.ADTDefinition = trans.transform(adt)
    protected def transformClass(cd: s.ClassDef): t.ClassDef = new t.ClassDef(
      cd.id,
      cd.tparams.map(tdef => trans.transform(tdef)),
      cd.parent,
      cd.fields.map(vd => trans.transform(vd)),
      cd.methods,
      cd.flags.map(f => trans.transform(f))
    )
  }
}
