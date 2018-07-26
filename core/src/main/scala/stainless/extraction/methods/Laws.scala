/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction
package methods

import scala.language.postfixOps

import stainless.ast.SymbolIdentifier
import stainless.ast.SymbolIdentifier.IdentifierOps

trait Laws extends oo.CachingPhase
  with SimpleFunctions
  with DependentlyCachedFunctions
  with oo.DependentlyCachedClasses
  with IdentitySorts { self =>

  val s: methods.Trees
  val t: methods.Trees

  private[this] object transformer extends oo.TreeTransformer {
    val s: self.s.type = self.s
    val t: self.t.type = self.t
  }

  override protected type ClassResult = (t.ClassDef, Seq[t.FunDef])
  override protected def registerClasses(symbols: t.Symbols, classes: Seq[(t.ClassDef, Seq[t.FunDef])]): t.Symbols = {
    val (cls, funs) = classes.unzip
    symbols.withClasses(cls).withFunctions(funs.flatten)
  }

  override protected def getContext(symbols: s.Symbols) = new TransformerContext(symbols)

  protected class TransformerContext(val symbols: s.Symbols) extends oo.TreeTransformer {
    override val s: self.s.type = self.s
    override val t: self.t.type = self.t

    import s._
    import symbols._

    private[this] object IsLaw {
      def apply(law: Expr) = Annotation("law", Seq(law))
    }

    def isLaw(fd: FunDef): Boolean = fd.flags exists (_.name == "law")

    def getClass(fd: FunDef): Option[ClassDef] = {
      fd.flags collectFirst { case IsMethodOf(cid) => symbols.classes(cid) }
    }

    def getLaws(cd: ClassDef): Seq[FunDef] = {
      cd.methods(symbols).map(symbols.functions).filter(isLaw)
    }

    def getParentLaws(cd: ClassDef): Seq[FunDef] = for {
      parent <- cd.ancestors(symbols).headOption.toSeq
      method <- parent.cd.methods(symbols).map(symbols.functions) if isLaw(method)
    } yield method

    def bodyAsPost(body: Expr): Expr = {
      val vd = ValDef(FreshIdentifier("res"), BooleanType(), Seq.empty).setPos(body)
      val post = Lambda(Seq(vd), And(vd.toVariable, body).setPos(body)).setPos(body)
      Ensuring(NoTree(BooleanType()).setPos(body), post).setPos(body)
    }

    def rewriteLaw(fd: FunDef): FunDef = {
      val cd = getClass(fd).get
      val parentClass = cd.ancestors(symbols).headOption
      val parentFun = parentClass.flatMap(_.cd.methods(symbols).find(_.name == fd.id.name)).map(symbols.functions)
      val parentExpr = parentFun.map(_.fullBody).flatMap(exprOps.withoutSpecs)
      val fullExpr = parentExpr.map(And(_, fd.fullBody).setPos(fd)).getOrElse(fd.fullBody)
      val newBody = bodyAsPost(fullExpr).setPos(fd)
      val newFlags = (fd.flags.filterNot(_.name == "law") ++ Seq(IsLaw(fullExpr), IsAbstract)).distinct

      fd.copy(fullBody = newBody, flags = newFlags).copiedFrom(fd)
    }

    def missingLawOverride(fd: FunDef, cd: ClassDef): FunDef = {
      val parent = cd.ancestors(symbols).head
      val args = fd.params map { vd =>
        vd.freshen.copy(tpe = typeOps.instantiateType(vd.tpe, parent.tpSubst))
      }

      val id = SymbolIdentifier(fd.id.unsafeToSymbolIdentifier.symbol)

      val funOverride = new FunDef(
        id,
        fd.tparams.map(_.freshen),
        args,
        BooleanType(),
        BooleanLiteral(true).setPos(fd),
        Seq(IsMethodOf(cd.id)) ++ cd.flags.find(_ == IsAbstract).toSeq
      ).copiedFrom(fd)

      if (funOverride.flags.exists(_ == IsAbstract)) rewriteLaw(funOverride) else funOverride
    }

    def missingLawOverrides(cd: ClassDef): Seq[FunDef] = {
      val methods = cd.methods(symbols).map(_.symbol).toSet
      getParentLaws(cd)
        .filterNot(methods contains _.id.unsafeToSymbolIdentifier.symbol)
        .map(missingLawOverride(_, cd))
    }
  }

  override protected def extractClass(context: TransformerContext, cd: s.ClassDef): (t.ClassDef, Seq[t.FunDef]) = {
    val lawOverrides = context.missingLawOverrides(cd)
    transformer.transform(cd) -> lawOverrides.map(transformer.transform)
  }

  override protected def extractFunction(context: TransformerContext, fd: s.FunDef): t.FunDef = {
    transformer.transform {
      if (context isLaw fd) context rewriteLaw fd else fd
    }
  }

}

object Laws {
  def apply(trees: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: trees.type
    val t: trees.type
  } = new Laws {
    override val s: trees.type = trees
    override val t: trees.type = trees
    override val context = ctx
  }
}
