package stainless
package utils

import collection.immutable.BitSet

abstract class TokensCommon {
  val maxToken: Int

  type Token = Int
  type TokenSet = BitSet

  def tokenRange(lo: Int, hi: Int): TokenSet = BitSet(lo to hi: _*)

  def showTokenDetailed(token: Int) = debugString(token)

  def showToken(token: Int) = {
    val str = tokenString(token)
    if (isKeyword(token)) s"'$str'" else str
  }

  val tokenString, debugString = new Array[String](maxToken + 1)

  def enter(token: Int, str: String, debugStr: String = ""): Unit = {
    assert(tokenString(token) == null)
    tokenString(token) = str
    debugString(token) = if (debugStr.isEmpty) str else debugStr
  }

  /** special tokens */
  final val EMPTY = 0;             enter(EMPTY, "<empty>") // a missing token, used in lookahead
  final val ERROR = 1;             enter(ERROR, "erroneous token") // an erroneous token
  final val EOF = 2;               enter(EOF, "eof")

  /** literals */
  final val CHARLIT = 3;           enter(CHARLIT, "character literal")
  final val INTLIT = 4;            enter(INTLIT, "integer literal")
  final val LONGLIT = 5;           enter(LONGLIT, "long literal")
  final val FLOATLIT = 6;          enter(FLOATLIT, "float literal")
  final val DOUBLELIT = 7;         enter(DOUBLELIT, "double literal")
  final val STRINGLIT = 8;         enter(STRINGLIT, "string literal")
  final val STRINGPART = 9;        enter(STRINGPART, "string literal", "string literal part")
  //final val INTERPOLATIONID = 10;  enter(INTERPOLATIONID, "string interpolator")
  //final val SYMBOLLIT = 11;        enter(SYMBOLLIT, "symbol literal") // TODO: deprecate

  /** identifiers */
  final val IDENTIFIER = 12;       enter(IDENTIFIER, "identifier")
  //final val BACKQUOTED_IDENT = 13; enter(BACKQUOTED_IDENT, "identifier", "backquoted ident")

  /** alphabetic keywords */
  final val IF = 20;               enter(IF, "if")
  final val FOR = 21;              enter(FOR, "for")
  final val ELSE = 22;             enter(ELSE, "else")
  final val THIS = 23;             enter(THIS, "this")
  final val NULL = 24;             enter(NULL, "null")
  final val NEW = 25;              enter(NEW, "new")
  //final val WITH = 26;             enter(WITH, "with")
  final val SUPER = 27;            enter(SUPER, "super")
  //final val CASE = 28;             enter(CASE, "case")
  //final val CASECLASS = 29;        enter(CASECLASS, "case class")
  //final val CASEOBJECT = 30;       enter(CASEOBJECT, "case object")
  //final val VAL = 31;              enter(VAL, "val")
  final val ABSTRACT = 32;         enter(ABSTRACT, "abstract")
  final val FINAL = 33;            enter(FINAL, "final")
  final val PRIVATE = 34;          enter(PRIVATE, "private")
  final val PROTECTED = 35;        enter(PROTECTED, "protected")
  final val OVERRIDE = 36;         enter(OVERRIDE, "override")
  //final val IMPLICIT = 37;         enter(IMPLICIT, "implicit")
  //final val VAR = 38;              enter(VAR, "var")
  //final val DEF = 39;              enter(DEF, "def")
  //final val TYPE = 40;             enter(TYPE, "type")
  final val EXTENDS = 41;          enter(EXTENDS, "extends")
  final val TRUE = 42;             enter(TRUE, "true")
  final val FALSE = 43;            enter(FALSE, "false")
  //final val OBJECT = 44;           enter(OBJECT, "object")
  final val CLASS = 45;            enter(CLASS, "class")
  final val IMPORT = 46;           enter(IMPORT, "import")
  final val PACKAGE = 47;          enter(PACKAGE, "package")
  //final val YIELD = 48;            enter(YIELD, "yield")
  final val DO = 49;               enter(DO, "do")
  //final val TRAIT = 50;            enter(TRAIT, "trait")
  //final val SEALED = 51;           enter(SEALED, "sealed")
  final val THROW = 52;            enter(THROW, "throw")
  final val TRY = 53;              enter(TRY, "try")
  final val CATCH = 54;            enter(CATCH, "catch")
  final val FINALLY = 55;          enter(FINALLY, "finally")
  final val WHILE = 56;            enter(WHILE, "while")
  final val RETURN = 57;           enter(RETURN, "return")
  //final val MATCH = 58;            enter(MATCH, "match")
  //final val LAZY = 59;             enter(LAZY, "lazy")
  //final val THEN = 60;             enter(THEN, "then")
  //final val FORSOME = 61;          enter(FORSOME, "forSome") // TODO: deprecate
  //final val INLINE = 62;           enter(INLINE, "inline")
  final val THISS = 63;             enter(THISS, "thiss")

  /** special symbols */
  final val COMMA = 70;            enter(COMMA, "','")
  final val SEMI = 71;             enter(SEMI, "';'")
  final val DOT = 72;              enter(DOT, "'.'")
  //final val NEWLINE = 78;          enter(NEWLINE, "end of statement", "new line")
  //final val NEWLINES = 79;         enter(NEWLINES, "end of statement", "new lines")

  /** special keywords */
  //final val USCORE = 73;           enter(USCORE, "_")
  final val COLON = 74;            enter(COLON, ":")
  final val EQUALS = 75;           enter(EQUALS, "=")
  //final val LARROW = 76;           enter(LARROW, "<-")
  //final val ARROW = 77;            enter(ARROW, "=>")
  //final val SUBTYPE = 80;          enter(SUBTYPE, "<:")
  //final val SUPERTYPE = 81;        enter(SUPERTYPE, ">:")
  //final val HASH = 82;             enter(HASH, "#")
  final val AT = 83;               enter(AT, "@")
  //final val VIEWBOUND = 84;        enter(VIEWBOUND, "<%") // TODO: deprecate

  val keywords: TokenSet

  def isKeyword(token: Token): Boolean = keywords contains token

  /** parentheses */
  final val LPAREN = 90;           enter(LPAREN, "'('")
  final val RPAREN = 91;           enter(RPAREN, "')'")
  final val LBRACKET = 92;         enter(LBRACKET, "'['")
  final val RBRACKET = 93;         enter(RBRACKET, "']'")
  final val LBRACE = 94;           enter(LBRACE, "'{'")
  final val RBRACE = 95;           enter(RBRACE, "'}'")

  final val firstParen = LPAREN
  final val lastParen = RBRACE
}

object Tokens extends TokensCommon {
  final val minToken = EMPTY
  final val maxToken = XMLSTART

  final val INTERPOLATIONID = 10;  enter(INTERPOLATIONID, "string interpolator")
  final val SYMBOLLIT = 11;        enter(SYMBOLLIT, "symbol literal") // TODO: deprecate

  final val BACKQUOTED_IDENT = 13; enter(BACKQUOTED_IDENT, "identifier", "backquoted ident")

  final val identifierTokens = BitSet(IDENTIFIER, BACKQUOTED_IDENT)

  def isIdentifier(token : Int) =
    token >= IDENTIFIER && token <= BACKQUOTED_IDENT

  /** alphabetic keywords */
  final val WITH = 26;             enter(WITH, "with")
  final val CASE = 28;             enter(CASE, "case")
  final val CASECLASS = 29;        enter(CASECLASS, "case class")
  final val CASEOBJECT = 30;       enter(CASEOBJECT, "case object")
  final val VAL = 31;              enter(VAL, "val")
  final val IMPLICIT = 37;         enter(IMPLICIT, "implicit")
  final val VAR = 38;              enter(VAR, "var")
  final val DEF = 39;              enter(DEF, "def")
  final val TYPE = 40;             enter(TYPE, "type")
  final val OBJECT = 44;           enter(OBJECT, "object")
  final val YIELD = 48;            enter(YIELD, "yield")
  final val TRAIT = 50;            enter(TRAIT, "trait")
  final val SEALED = 51;           enter(SEALED, "sealed")
  final val MATCH = 58;            enter(MATCH, "match")
  final val LAZY = 59;             enter(LAZY, "lazy")
  final val THEN = 60;             enter(THEN, "then")
  final val FORSOME = 61;          enter(FORSOME, "forSome") // TODO: deprecate
  final val IS = 62;               enter(IS, "is")
  final val INLINE = 64;           enter(INLINE, "inline")

  /** special symbols */
  final val NEWLINE = 78;          enter(NEWLINE, "end of statement", "new line")
  final val NEWLINES = 79;         enter(NEWLINES, "end of statement", "new lines")

  /** special keywords */
  final val USCORE = 73;           enter(USCORE, "_")
  final val LARROW = 76;           enter(LARROW, "<-")
  final val ARROW = 77;            enter(ARROW, "=>")
  final val SUBTYPE = 80;          enter(SUBTYPE, "<:")
  final val SUPERTYPE = 81;        enter(SUPERTYPE, ">:")
  final val HASH = 82;             enter(HASH, "#")
  final val VIEWBOUND = 84;        enter(VIEWBOUND, "<%") // TODO: deprecate

  /** XML mode */
  final val XMLSTART = 96;         enter(XMLSTART, "$XMLSTART$<") // TODO: deprecate

  final val alphaKeywords = tokenRange(IF, INLINE)
  final val symbolicKeywords = tokenRange(USCORE, VIEWBOUND)
  final val symbolicTokens = tokenRange(COMMA, VIEWBOUND)
  final val keywords = alphaKeywords | symbolicKeywords

  final val allTokens = tokenRange(minToken, maxToken)

  final val simpleLiteralTokens = tokenRange(CHARLIT, STRINGLIT) | BitSet(TRUE, FALSE, THISS)
  final val literalTokens = simpleLiteralTokens | BitSet(INTERPOLATIONID, SYMBOLLIT, NULL)

  final val atomicExprTokens = literalTokens | identifierTokens | BitSet(
    USCORE, NULL, THIS, THISS, SUPER, TRUE, FALSE, RETURN, XMLSTART)

  final val canStartExpressionTokens = atomicExprTokens | BitSet(
    LBRACE, LPAREN, IF, DO, WHILE, FOR, NEW, TRY, THROW)

  final val canStartTypeTokens = literalTokens | identifierTokens | BitSet(
    THIS, SUPER, USCORE, LPAREN, AT)

  final val canStartBindingTokens = identifierTokens | BitSet(USCORE, LPAREN)

  final val templateIntroTokens = BitSet(CLASS, TRAIT, OBJECT, CASECLASS, CASEOBJECT)

  final val dclIntroTokens = BitSet(DEF, VAL, VAR, TYPE)

  final val defIntroTokens = templateIntroTokens | dclIntroTokens

  final val localModifierTokens = BitSet(
    ABSTRACT, FINAL, SEALED, IMPLICIT, INLINE, LAZY)

  final val accessModifierTokens = BitSet(
    PRIVATE, PROTECTED)

  final val modifierTokens = localModifierTokens | accessModifierTokens | BitSet(
    OVERRIDE)

  /** Is token only legal as start of statement (eof also included)? */
  final val mustStartStatTokens = defIntroTokens | modifierTokens | BitSet(
    IMPORT, PACKAGE)

  final val canStartStatTokens = canStartExpressionTokens | mustStartStatTokens | BitSet(
    AT, CASE)

  final val canEndStatTokens = atomicExprTokens | BitSet(
    TYPE, RPAREN, RBRACE, RBRACKET)

  final val numericLitTokens = BitSet(INTLIT, LONGLIT, FLOATLIT, DOUBLELIT)
}

