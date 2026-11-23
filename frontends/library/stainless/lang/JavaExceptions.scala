/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

// The Stainless versions of standard Java exceptions.
//
// The frontend extracts `java.lang.Throwable` and `java.lang.Exception` as `stainless.lang.Exception`, and the
// other Java exceptions below as the classes of the same name, which follow the hierarchy of Java. The arguments
// of their constructors are extracted as their message, as far as the message can be extracted.

@library
class RuntimeException(msg: String = "") extends Exception(msg)

@library
class IllegalArgumentException(msg: String = "") extends RuntimeException(msg)

@library
class IllegalStateException(msg: String = "") extends RuntimeException(msg)

@library
class UnsupportedOperationException(msg: String = "") extends RuntimeException(msg)

@library
class ArithmeticException(msg: String = "") extends RuntimeException(msg)

@library
class IndexOutOfBoundsException(msg: String = "") extends RuntimeException(msg)

@library
class NoSuchElementException(msg: String = "") extends RuntimeException(msg)
