/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package frontends.noxt

import frontend.{ Frontend, ThreadedFrontend, FrontendFactory, CallBack }
import extraction.xlang.{trees => xt}

import java.io.{File, FileInputStream, InputStream}

object NoxtFrontend {
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
              val name = sources.headOption.getOrElse("stdin")
              val ud = xt.UnitDef(
                FreshIdentifier(name), Seq.empty, Seq.empty, Seq.empty, false)
              // TODO: Generate classes/functions/typedefs per compilation unit
              callback(name, ud, Seq.empty, syms.functions.values.toSeq, Seq.empty)
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