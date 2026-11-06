/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc

import CPrinter.manualSignature
import org.scalatest.funsuite.AnyFunSuite

class CPrinterSuite extends AnyFunSuite:

  test("The signature of a manually defined function ends at its last token before the body"):
    assert(manualSignature("int32_t f(int32_t x) { return x; }") == "int32_t f(int32_t x)")
    assert(manualSignature("\nint32_t f(void)\n{\n  return 0;\n}\n") == "\nint32_t f(void)")

  test("The parameter list of a manually defined function can have nested parentheses"):
    val signature: String = "int32_t f(int32_t (*g)(int32_t), int32_t x)"
    assert(manualSignature(signature + " { return g(x); }") == signature)

  test("The parameter list of a manually defined function is not always its first parenthesis"):
    val returnsFunction: String = "int32_t (*f(int32_t (*g)(int32_t)))(int32_t)"
    assert(manualSignature(returnsFunction + " { return g; }") == returnsFunction)
    val attribute: String = "__attribute__((noinline)) int32_t f(int32_t x)"
    assert(manualSignature(attribute + " { return x; }") == attribute)

  test("The braces of a parameter list and of an array size do not open the body"):
    val signature: String = "int32_t f(struct { int32_t x; } s, int32_t a[sizeof((char[]){ 1, 2 })])"
    assert(manualSignature(signature + " { return 0; }") == signature)

  test("The braces and the parentheses of comments are skipped"):
    val signature: String = "/* { ) */ int32_t f(void)"
    assert(manualSignature(signature + " /* { ( */ // { (\n{ return 0; }") == signature)
    val lineComment: String = "// Don't stop here: {\nint32_t f(void)"
    assert(manualSignature(lineComment + " // {\n{ return 0; }") == lineComment)
    val quotes: String = "/* ' \" */ int32_t f(void)"
    assert(manualSignature(quotes + " { return 0; }") == quotes)

  test("The braces and the parentheses of string literals and of character constants are skipped"):
    val signature: String =
      """__attribute__((section("a{\"b("))) int32_t f(char a['{'], char b['\''], char c[')'])"""
    assert(manualSignature(signature + " { return 0; }") == signature)

  test("The signature of a code without a body is the whole code"):
    assert(manualSignature("int32_t f(int32_t x);\n") == "int32_t f(int32_t x);")
    assert(manualSignature("#define f(x) ((x) + 1)") == "#define f(x) ((x) + 1)")
    assert(manualSignature("int32_t f(char a[sizeof \"{ ])") == "int32_t f(char a[sizeof \"{ ])")
    assert(manualSignature("/* { ") == "")
