/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction
package termination

trait SizeInjection extends CachingPhase
  with SimpleFunctions
  with SimplyCachedFunctions
  with SimplyCachedSorts
  { self =>
  val s: Trees
  val t: s.type

  /* ====================================
   *       Context and caches setup
   * ==================================== */

  import s._
  import s.exprOps._
  import dsl._

  private val sizeFunctionId = new utils.ConcurrentCache[Identifier, Identifier]
  protected class TransformerContext(implicit symbols: Symbols) extends transformers.TreeTransformer {
    val s: self.s.type = self.s
    val t: s.type = s

    for ((id, _ ) <- symbols.sorts if !sizeFunctionId.contains(id)) {
      sizeFunctionId(id) = FreshIdentifier(id.name + "PrimitiveSize")
    }

    val sizeFunction: Map[Identifier, FunDef] = {
      symbols.sorts.map { case (id, sort) =>
        val tpe = ADTType(sort.id, sort.typeArgs)
        val tparams = sort.tparams.map(_.tp)
        val v = Variable.fresh("x", tpe)
        val fd =
          new FunDef(
            sizeFunctionId(id),
            sort.tparams,
            Seq(v.toVal),
            IntegerType(),
            Ensuring(MatchExpr(v, sort.typed(tparams).constructors.map { cons =>
              val arguments = cons.fields.map(_.freshen)
              val argumentPatterns = arguments.map(vd => WildcardPattern(Some(vd)))
              val base: Expr = if (cons.fields.nonEmpty) IntegerLiteral(1) else IntegerLiteral(0)
              val rhsValues: Seq[Expr] = arguments.map(vd => size(vd.toVariable))
              val rhs = rhsValues.foldLeft[Expr](base)(_ + _)
              MatchCase(ADTPattern(None, cons.id, cons.tps, argumentPatterns), None, rhs)
            }), \("res" :: IntegerType())(res => res >= E(BigInt(0)))).copiedFrom(sort),
            Seq(Synthetic)
          )
        id -> fd
      }
    }

    private def size(v: Variable): Expr = v.getType match {
      case ADTType(id, tps) => FunctionInvocation(sizeFunctionId(id), tps, Seq(v)).setPos(v)
      case _ => IntegerLiteral(0)
    }

    override def transform(e: Expr) = e match {
      case Decreases(v: Variable, body) if v.getType.isInstanceOf[ADTType] =>
        Decreases(size(v), transform(body))
      case Decreases(Tuple(ts), body) =>
        Decreases(Tuple(ts.map {
          case v: Variable if v.getType.isInstanceOf[ADTType] => size(v)
          case e => transform(e)
        }), transform(body))
      case _ => super.transform(e)
    }
  }

  override protected def getContext(syms: Symbols) = new TransformerContext()(syms)

  // For each sort, we define a size function
  override protected type SortResult = (ADTSort, FunDef)

  override protected def extractFunction(context: TransformerContext, fd: FunDef): FunDef = {
    context.transform(fd)
  }

  override protected def extractSort(context: TransformerContext, sort: ADTSort): SortResult = {
    (sort, context.sizeFunction(sort.id))
  }

  override protected def registerSorts(syms: Symbols, results: Seq[SortResult]): Symbols = {
    syms
      .withSorts(results.map(_._1))
      .withFunctions(results.map(_._2))
  }
}

object SizeInjection {
  def apply(tt: Trees)(implicit ctx: inox.Context): ExtractionPipeline {
    val s: tt.type
    val t: tt.type
  } = new SizeInjection {
    override val s: tt.type = tt
    override val t: tt.type = tt
    override val context = ctx
  }
}
