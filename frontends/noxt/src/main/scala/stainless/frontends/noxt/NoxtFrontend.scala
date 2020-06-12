/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package frontends.noxt

import frontend.{ Frontend, ThreadedFrontend, FrontendFactory, CallBack }
import extraction.xlang.{trees => xt}

import java.io.{File, FileInputStream, InputStream}

object NoxtFrontend {
object xtTransformer extends xt.SelfTreeTransformer {
    import scala.collection.mutable.HashMap
    var newIds: HashMap[Identifier, Identifier] = HashMap.empty

    // Since Identifiers in the given deserialized symbols were created externally, we need
    // to avoid Stainless from potentially creating duplicate ids at a later point.
    // We therefore replace replace all the deserialized ids by fresh ones.
    override def transform(id: Identifier): Identifier = {
      newIds.getOrElseUpdate(id, {
        id match {
          case id: xt.SymbolIdentifier =>
            new xt.SymbolIdentifier(FreshIdentifier(id.name), ast.Symbol(id.symbol.path))
          case _ =>
            FreshIdentifier(id.name)
        }
      })
    }

    override def transform(e: xt.Expr): xt.Expr = e match {
      case xt.ADT(id, tps, args) =>
        val newId = transform(id)
        xt.ClassConstructor(xt.ClassType(newId, tps.map(transform)), args.map(transform)).copiedFrom(e)
      case xt.MatchExpr(scrut, cases) =>
        xt.MatchExpr(transform(scrut), cases.map(arm => {
          xt.MatchCase(transform(arm.pattern), arm.optGuard.map(transform), transform(arm.rhs)).copiedFrom(arm)
        })).copiedFrom(e)
      case _ => super.transform(e)
    }

    override def transform(tpe: xt.Type): xt.Type = tpe match {
      case xt.ADTType(id, tps) =>
        val newId = transform(id)
        xt.ClassType(newId, tps.map(transform))
      case _ => super.transform(tpe)
    }

    override def transform(pat: xt.Pattern): xt.Pattern = pat match {
      case xt.ADTPattern(binder, id, tps, subs) =>
        val newId = transform(id)
        // FIXME: The rustc frontend produces `tps` here even though the ADT doesn't have any type parameters
        // val ct = xt.ClassType(newId, tps.map(transform))
        val ct = xt.ClassType(newId, Seq.empty)  // Temporary workaround (remove once fixed)
        xt.ClassPattern(binder, ct, subs.map(transform))
      case _ => super.transform(pat)
    }

    def adtsToClassDefs(adts: Seq[xt.ADTSort]): Seq[xt.ClassDef] = {
      adts.flatMap(sort => {
        assert(sort.tparams.isEmpty) // NOTE: type parameters are not supported yet
        assert(sort.flags.isEmpty)

        val newSortId = transform(sort.id)
        val parentCd = new xt.ClassDef(
          newSortId, Seq.empty, Seq.empty, Seq.empty, Seq(xt.IsAbstract, xt.IsSealed))
        val parentType = new xt.ClassType(newSortId, Seq.empty)
        parentCd +: sort.constructors.map { cons =>
          val newConsId = transform(cons.id)
          val fields = cons.fields.map(transform)
          new xt.ClassDef(newConsId, Seq.empty, Seq(parentType), fields, Seq.empty)
        }
      })
    }
  }

  def toExtractionTrees(syms: xt.Symbols): (Seq[xt.ClassDef], Seq[xt.FunDef]) = {
    val classes = xtTransformer.adtsToClassDefs(syms.sorts.values.toSeq)
    val funs = syms.functions.values.toSeq.map(fd => xtTransformer.transform(fd))
    (classes, funs)
  }

  class Factory(
    override val extraCompilerArguments: Seq[String],
    override val libraryPaths: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
      new Frontend(callback) {
        var isRunning = false

        override val sources = compilerArgs

        private def readUnit(): Option[xt.Symbols] = {
          def deserialize(in: InputStream): Option[xt.Symbols] = {
            def fail(e: Throwable) = {
              ctx.reporter.error(s"Failed to deserialize stainless program:\n$e")
              e.printStackTrace()
              None
            }
            val serializer = utils.Serializer(xt)
            import serializer._
            try {
              Some(serializer.deserialize[xt.Symbols](in))
            } catch {
              case e: java.lang.reflect.InvocationTargetException => fail(e.getCause)
              case e: Throwable => fail(e)
            }
          }

          if (sources.isEmpty) {
            ctx.reporter.info("No source .inoxser file given, expecting data on standard input...")
            deserialize(System.in)
          } else {
            val file = new File(sources.head)
            if (file.exists) {
              ctx.reporter.info(s"Reading stainless program from $file")
              val in = new FileInputStream(file)
              val result = deserialize(in)
              in.close()
              result
            } else {
              ctx.reporter.error(s"Couldn't open input file $file.")
              None
            }
          }
        }

        override def run(): Unit = {
          isRunning = true
          callback.beginExtractions()
          readUnit() match {
            case Some(syms) =>
              val (classes, funs) = toExtractionTrees(syms)

              val name = sources.headOption.getOrElse("stdin")
              val ud = xt.UnitDef(
                FreshIdentifier(name), Seq.empty, classes.map(_.id), Seq.empty, false)

              callback(name, ud, classes, funs, Seq.empty)
            case None =>
              callback.failed()
          }
          callback.endExtractions()
          isRunning = false
        }

        override protected def onStop(): Unit = {
          isRunning = false
        }

        override protected def onJoin(): Unit = {
          isRunning = false
        }
      }
  }
}