/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc.{Global,Settings=>NSCSettings}
import scala.reflect.internal.Positions

class FullScalaCompiler(settings: NSCSettings, ctx: LeonContext) extends Global(settings, new SimpleReporter(settings, ctx.reporter)) with Positions {

  class Run extends super.Run {
    override def progress(current: Int, total: Int) {
      ctx.reporter.onCompilerProgress(current, total)
    }
  }
}
