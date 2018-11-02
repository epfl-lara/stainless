/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen

import inox.ast.Identifier

/** Defines a language, 'reclang', that functions as an intermediate language between stainless trees and wasm code.
  *
  * The main feature of this language are extensible record types,
  * which are meant to be easily translatable both to the current memory model of wasm (linear memory)
  * and the planned future extension of reference types.
  * The class [[stainless.wasmgen.intermediate.Lowering]]
  * is responsible for the lowering to this intermediate language.
  *
  * reclang is defined by the following grammars (nonterminals in ' '):
  *
  *   'type' ::= Boolean | Int | Long | Double | Array('type') | ('type'*) => 'type' | 'id'
  *
  * where id refers to the name of a record sort defined in the program.
  * There is no type polymorphism.
  * A record sort is defined as follows:
  *
  *   'sort' ::= struct 'id' ('field'*) [extends 'id']?
  *   'field' ::= 'id' : 'type'
  *
  * There is a single sort, called "anyref", that does not have a parent.
  * It has a single field which rerpesents the type tag of a given runtime value:
  *
  *   struct anyref (typeTag: Int)
  *
  * anyref is the root of the record hierarchy. All other records have a parent.
  * Note that there is no subtyping in reclang; casts have to be given explicitly.
  * A record contains entries for the fields of all its ascestors as well as its own.
  *
  * The expressions of reclang are given below:
  *
  *   'e' ::= error | 'id' // variable
  *         | val 'id' = 'e'; 'e' | println('e')
  *         | 'id'('e'*) // function invocation
  *         | 'e'; 'e' | if ('e') 'e' else 'e' | 'e' == 'e'
  *         | 'intconst' | 'doubleconst' | true | false
  *         | 'id'('e'*) // record constructor
  *         | 'e'.'id' // record field selector
  *         | 'e'('e'*) // higher-order application
  *         | 'e'.asInstanceOf['id']
  *
  *         | new Array['type']('e', 'e'?) // length, optional initializer
  *         | 'e'('e') // array select
  *         | 'e'('e') = 'e' // array set
  *         | 'e'.length
  *         | Array.copy('e', 'e', 'e', 'e') // from, to, start, finish
  *
  *         | 'e' 'binop' 'e'
  *         | ! 'e'
  *
  *   'binop' ::= + | - | * | / | mod | remainder
  *             | < | > | <= | >= | & | "|"
  *             | ^ | << | >> | >>>
  *             | (bitvector casts)
  *             | "||" | &&
  *
  *
  * The notable typing rules are for records:
  * a record constructor takes as arguments expressions of the types of
  * the fields of all the ancestors (incl.) of the current type.
  * Also, a selector is allowed with the name of a field of an ancestor.
  * Casts have to be between compatible record types, i.e.,
  * that are related by the ancestor relation.
  * An upcast is always successful.
  * A downcast to an incompatible type fails the program.
  *
  * Functions are closed in reclang and are represented closures,
  * i.e., records containing a function pointer
  * and the environment captured by the function.
  * Since there is no polymorphism,
  * there are boxed versions of the elementary types
  * (which are regular record types).
  *
  * The typetag field (which is defined in anyref,
  * therefore present in every record) defines the type of a record value
  * at runtime as follows:
  * 0 for boxed Int,
  * 1 for boxed Long,
  * 2 is not used but is reserved for boxed Float,
  * 3 for boxed Double,
  * 4 for boxed Array,
  * 5 for closure,
  * and then as many tags as are needed for record sorts
  * that are instantiated in the program.
  * In principle that could be any type,
  * but we can skip types we know are not instantiated.
  *
  * Two reference values are equal if their type tags are equal
  * and all fields defined by the type of their tag are equal.
  */
package object intermediate {
  object trees extends Trees { self =>
    object printer extends Printer {
      val trees: self.type = self
    }
    case class Symbols(
      records: Map[Identifier, RecordSort],
      functions: Map[Identifier, FunDef]
    ) extends AbstractSymbols {
      def withFunctions(functions: Seq[FunDef]): Symbols =
        Symbols(this.records, this.functions ++ functions.map(fd => fd.id -> fd))

      def withSorts(sorts: Seq[ADTSort]): Symbols = this

      def withRecords(records: Seq[RecordSort]): Symbols =
        Symbols(this.records ++ records.map(rec => rec.id -> rec), this.functions)
    }
    val NoSymbols: Symbols = Symbols(Map(), Map())
  }

}
