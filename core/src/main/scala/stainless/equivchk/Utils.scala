package stainless
package equivchk

import stainless.extraction.trace.Trees
import stainless.{FreshIdentifier, Identifier}

import scala.collection.immutable.SeqMap

trait Utils {
  val trees: Trees
  val context: inox.Context

  import trees._
  import exprOps.{BodyWithSpecs, Postcondition, PostconditionKind}

  class Specializer(origFd: FunDef,
                    newId: Identifier,
                    tsubst: Map[Identifier, Type],
                    vsubst: Map[Identifier, Expr],
                    replacement: Map[Identifier, (Identifier, Seq[Int])]) // replace function calls
    extends ConcreteSelfTreeTransformer {

    override def transform(expr: Expr): Expr = expr match {
      case v: Variable =>
        vsubst.getOrElse(v.id, super.transform(v))

      case fi: FunctionInvocation if fi.id == origFd.id =>
        val fi1 = FunctionInvocation(newId, tps = fi.tps, args = fi.args)
        super.transform(fi1.copiedFrom(fi))

      case fi: FunctionInvocation if replacement.contains(fi.id) =>
        val (repl, perm) = replacement(fi.id)
        val fi1 = FunctionInvocation(repl, tps = fi.tps, args = perm.map(fi.args))
        super.transform(fi1.copiedFrom(fi))

      case _ => super.transform(expr)
    }

    override def transform(tpe: Type): Type = tpe match {
      case tp: TypeParameter =>
        tsubst.getOrElse(tp.id, super.transform(tp))

      case _ => super.transform(tpe)
    }
  }

  // make a copy of the 'model'
  // combine the specs of the 'lemma'
  // 'suffix': only used for naming
  // 'replacement': function calls that are supposed to be replaced according to given mapping and permutation
  def inductPattern(symbols: Symbols, model: FunDef, lemma: FunDef, suffix: String, replacement: Map[Identifier, (Identifier, Seq[Int])]) = {
    import exprOps._
    import symbols.{_, given}

    val indPattern = exprOps.freshenSignature(model).copy(id = FreshIdentifier(s"${lemma.id}$$$suffix"))
    val newParamTps = indPattern.tparams.map { tparam => tparam.tp }
    val newParamVars = indPattern.params.map { param => param.toVariable }

    val fi = FunctionInvocation(model.id, newParamTps, newParamVars)

    val tpairs = model.tparams zip fi.tps
    val tsubst = tpairs.map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
    val subst = (model.params.map(_.id) zip fi.args).toMap
    val specializer = new Specializer(model, indPattern.id, tsubst, subst, replacement)

    val fullBodySpecialized = specializer.transform(exprOps.withoutSpecs(model.fullBody).get)

    val specsSubst = (lemma.params.map(_.id) zip newParamVars).toMap ++ (model.params.map(_.id) zip newParamVars).toMap
    val specsTsubst = ((lemma.tparams zip fi.tps) ++ (model.tparams zip fi.tps)).map { case (tparam, targ) => tparam.tp.id -> targ }.toMap
    val specsSpecializer = new Specializer(indPattern, indPattern.id, specsTsubst, specsSubst, Map())

    val specs = BodyWithSpecs(model.fullBody).specs ++ BodyWithSpecs(lemma.fullBody).specs.filterNot(_.kind == MeasureKind)
    val pre = specs.filterNot(_.kind == PostconditionKind).map(spec => spec match {
      case Precondition(cond) => Precondition(specsSpecializer.transform(cond)).setPos(spec)
      case LetInSpec(vd, expr) => LetInSpec(vd, specsSpecializer.transform(expr)).setPos(spec)
      case Measure(measure) => Measure(specsSpecializer.transform(measure)).setPos(spec)
      case s => context.reporter.fatalError(s"Unsupported specs: $s")
    })

    val withPre = exprOps.reconstructSpecs(pre, Some(fullBodySpecialized), indPattern.returnType)

    val speccedLemma = BodyWithSpecs(lemma.fullBody).addPost
    val speccedOrig = BodyWithSpecs(model.fullBody).addPost
    val postLemma = speccedLemma.getSpec(PostconditionKind).map(post =>
      specsSpecializer.transform(post.expr))
    val postOrig = speccedOrig.getSpec(PostconditionKind).map(post => specsSpecializer.transform(post.expr))

    (postLemma, postOrig) match {
      case (Some(Lambda(Seq(res1), cond1)), Some(Lambda(Seq(res2), cond2))) =>
        val res = ValDef.fresh("res", indPattern.returnType)
        val freshCond1 = exprOps.replaceFromSymbols(Map(res1 -> res.toVariable), cond1)
        val freshCond2 = exprOps.replaceFromSymbols(Map(res2 -> res.toVariable), cond2)

        val cond = andJoin(Seq(freshCond1, freshCond2))
        val post = Postcondition(Lambda(Seq(res), cond))

        indPattern.copy(
          fullBody = BodyWithSpecs(withPre).withSpec(post).reconstructed,
          flags = Seq(Derived(Some(lemma.id)), Derived(Some(model.id)))
        ).copiedFrom(indPattern)

      case _ => indPattern
    }
  }

  case class ElimTraceInduct(updatedFd: FunDef, helper: Option[FunDef])

  def elimTraceInduct(symbols: Symbols, fds: Seq[FunDef]): Map[Identifier, ElimTraceInduct] =
  // SeqMap to have deterministic traversal
    SeqMap.from(fds.flatMap(fd => elimTraceInduct(symbols, fd).map(res => fd.id -> res)))

  def elimTraceInduct(symbols: Symbols, fd: FunDef): Option[ElimTraceInduct] = {
    def findModel(funNames: Seq[Any]): Option[FunctionInvocation] = {
      var funInv: Option[FunctionInvocation] = None

      BodyWithSpecs(fd.fullBody).getSpec(PostconditionKind) match {
        case Some(Postcondition(post)) =>
          exprOps.preTraversal {
            case _ if funInv.isDefined => // do nothing
            case fi@FunctionInvocation(tfd, tps, args) if fi.id != fd.id && symbols.isRecursive(tfd) && (funNames.contains(StringLiteral(tfd.name)) || funNames.contains(StringLiteral(""))) =>
              val paramVars = fd.params.map(_.toVariable)
              val argCheck = args.forall(paramVars.contains) && args.toSet.size == args.size
              if (argCheck) funInv = Some(fi)
            case _ =>
          }(post)
        case _ =>
      }

      funInv
    }

    fd.flags.collectFirst {
      case Annotation("traceInduct", funNames) =>
        findModel(funNames) match {
          case Some(finv) =>
            // make a helper lemma:
            val helper = inductPattern(symbols, symbols.functions(finv.id), fd, "indProof", Map.empty).setPos(fd.getPos)

            // transform the main lemma
            val proof = FunctionInvocation(helper.id, finv.tps, fd.params.map(_.toVariable))
            val returnType = typeOps.instantiateType(helper.returnType, (helper.typeArgs zip fd.typeArgs).toMap)

            val body = Let(ValDef.fresh("ind$proof", returnType), proof, exprOps.withoutSpecs(fd.fullBody).get)
            val withPre = exprOps.reconstructSpecs(BodyWithSpecs(fd.fullBody).specs, Some(body), fd.returnType)

            val updFn = fd.copy(
              fullBody = BodyWithSpecs(withPre).reconstructed,
              flags = fd.flags.filterNot(f => f.name == "traceInduct")
            )
            ElimTraceInduct(updFn, Some(helper))

          case None => // there are no recursive calls - no model function
            val updFn = fd.copy(flags = fd.flags.filterNot(f => f.name == "traceInduct"))
            ElimTraceInduct(updFn, None)
        }
    }
  }
}
