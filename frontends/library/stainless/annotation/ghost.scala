package stainless.annotation

import scala.annotation.StaticAnnotation
import scala.annotation.meta._

/**
 * Code annotated with @ghost is removed after stainless extraction.
 *
 * Code that can be annotated with @ghost: classes, method and value definitions, method parameters.
 *
 * See the Stainless specification for details.
 */
@ignore @field @getter @setter @param
class ghost extends StaticAnnotation
