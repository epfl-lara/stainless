/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.annotation

import scala.annotation.meta._
import scala.annotation.{Annotation, StaticAnnotation}

object cCode {

  /*
   * Allows the user to manually define the implementation for a C function.
   *
   * The optional parameter `includes` can hold a colon separated list of
   * required C99 include header files.
   *
   * For convenience, the C implementation generated by ``code`` is represented
   * using a String and not an Abstract Syntax Tree. The user is responsible
   * for the correctness of the provided C99 code. Because GenC might rename
   * the function, e.g. to deal with overloading, the special ``__FUNCTION__``
   * token should be used instead of the original name. Furthermore, the
   * parameters and return type should match the signature automatically
   * generated by GenC.
   *
   * Note that this annotation doesn't imply @extern but they can be
   * combined if needed.
   *
   * Example:
   * --------
   *
   *    // Print a 32-bit integer using the *correct*
   *    // format for printf in C99
   *    @cCode.function(
   *      code = """
   *        |void __FUNCTION__(int32_t x) {
   *        |  printf("%"PRIi32, x);
   *        |}
   *        """,
   *      includes = "inttypes.h:stdio.h"
   *    )
   *    def myprint(x: Int): Unit = {
   *      print(x)
   *    }
   *
   *
   * TODO in a later stage, when generics are supported, the instanciated type
   *      should be given to `code` somehow.
   *
   * NOTE As of April 2016, static annotation only supports literal parameters.
   */
  @ignore
  class function(
    code: String,
    includes: String
  ) extends StaticAnnotation

  /* Export function into a header file for GenC translation */
  @ignore
  class export extends StaticAnnotation

  /*
   * Allows the user to define a type (e.g. case class) as a typeDef to an
   * existing type with an optional include file.
   *
   * Example:
   * --------
   *
   *    @cCode.typedef(alias = "FILE*", include = "stdio.h")
   *    case class FileStream(<some Scala properties>)
   *
   * FIXME Due to type renaming for uniqueness, we cannot use the original name
   *       in C code through cCode.function annotation.
   */
  @ignore
  class typedef(alias: String, include: String) extends StaticAnnotation


  /*
   * Functions or types definitions annotated with @cCode.drop will not be translated by
   * GenC. This implies the @extern annotation for verification in Stainless.
   */
  @ignore
  class drop() extends StaticAnnotation

  /*
   * Field accesses of classes annotated with @cCode.global will be mapped to global accesses.
   * Function parameters whose types are such classes will be dropped.
   * In GenC, we make sure that at most one instance of such classes is initialized.
   * Moreover, all fields of such classes must have default values, which will be used as initial
   * values for global variables when compiling in GenC.
   */
  @ignore
  class global() extends StaticAnnotation

  /* Same as `global`, but variables will be declared without being initialized */
  @ignore
  class globalUninitialized() extends StaticAnnotation

  /* Same as `global`, but variables will not be declared */
  @ignore
  class globalExternal() extends StaticAnnotation

  /* The `static` annotation can be used to mark variables that appear in `@global` annotated classes */
  @ignore @field @getter @setter @param
  class static() extends StaticAnnotation

  /* The `volatile` annotation can be used to mark variables that appear in `@global` annotated classes */
  @ignore @field @getter @setter @param
  class volatile() extends StaticAnnotation
}
