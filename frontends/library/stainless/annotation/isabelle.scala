/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.annotation

import scala.annotation.StaticAnnotation

object isabelle {

  @ignore
  class typ(name: String) extends StaticAnnotation

  @ignore
  class constructor(name: String) extends StaticAnnotation

  @ignore
  class function(term: String) extends StaticAnnotation

  @ignore
  class script(name: String, source: String) extends StaticAnnotation

  @ignore
  class proof(method: String, kind: String = "") extends StaticAnnotation

  @ignore
  class fullBody() extends StaticAnnotation

  @ignore
  class noBody() extends StaticAnnotation

  @ignore
  class lemma(about: String) extends StaticAnnotation

}
