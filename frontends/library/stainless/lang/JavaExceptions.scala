/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

// The Stainless versions of standard Java exceptions.
//
// The frontend extracts `java.lang.Throwable` and `java.lang.Exception` as `stainless.lang.Exception`, and the
// other Java exceptions below as the classes of the same name, which follow the hierarchy of Java. The arguments
// of their constructors, such as the message, are not extracted. As `Exception`, these classes take no message.

@library
class RuntimeException extends Exception

@library
class IllegalArgumentException extends RuntimeException

@library
class IllegalStateException extends RuntimeException

@library
class UnsupportedOperationException extends RuntimeException

@library
class ArithmeticException extends RuntimeException

@library
class IndexOutOfBoundsException extends RuntimeException

@library
class NoSuchElementException extends RuntimeException
