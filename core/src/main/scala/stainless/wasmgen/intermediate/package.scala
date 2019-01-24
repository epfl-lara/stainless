/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.wasmgen

import inox.ast.Identifier

/** Defines a language, 'reclang', that functions as an intermediate language between stainless trees and wasm code.
  *
  * The main feature of reclang is that its structured types are extensible record,
  * which are meant to be easily translatable both to the current memory model of wasm (linear memory)
  * and the planned future extension of reference types.
  * The class [[stainless.wasmgen.intermediate.Lowering]]
  * is responsible for the lowering to this intermediate language.
  *
  * We now give an informal overview of reclang.
  * In the following grammars, nonterminal symbols are given in single quotes('),
  * and terminal symbols without quotes.
  *
  * The types of reclang are defined as follows:
  *
  *   'type' ::= Boolean | Char | Int | Long | Unit | Double | String | Array | ('type'*) => 'type' | 'id'
  *
  * where id refers to the name of a record sort defined in the program.
  * There is no type polymorphism, including arrays, which always contain boxed values.
  *
  * A record sort is defined as follows:
  *
  *   'sort' ::= struct 'id' ('field'*) [extends 'id']?
  *   'field' ::= 'id' : 'type'
  *
  * There is a single sort, called "anyref", that does not have a parent:
  *   struct anyref (typeTag: Int)
  * anyref has a single field which represents the type tag of a given runtime value.
  * anyref is the root of the record hierarchy. All other records have a parent.
  * There is no subtyping in reclang,
  * but there are operators which can cast one record to another,
  * provided they are connected with the ancestor (transitive reflexive closure of parent) relation.
  *
  * At runtime, a record's representation contains a list of values
  * corresponding to the fields it defines as well as all fields that its ancestors define.
  * The order of fields is from the further ancestor until the current field type.
  *
  * The expressions of reclang are given below:
  *
  *   'e' ::= error | 'id' // variable, or pointer to a named function
  *         | val 'id' = 'e'; 'e' | println('e')
  *         | 'id'('e'*) // function invocation
  *         | 'e'; 'e' | if ('e') 'e' else 'e' | 'e' == 'e'
  *         | 'intconst' | 'doubleconst' | 'charconst' | 'stingliteral'
  *         | true | false | ()
  *         | 'id'({'e' {, 'e'}*}?) // record constructor
  *         | 'e'.'id' // record field selector
  *         | 'e'({'e' {, 'e'}*}?) // higher-order application
  *         | 'e'.asInstanceOf['id']
  *
  *         | new Array['type']('e'{, 'e'}?) // length, optional initializer
  *         | 'e'('e') // array select
  *         | 'e'('e') = 'e' // array set
  *         | 'e'.length // array or string length
  *         | 'e'.substing('e', 'e') // string operations
  *
  *         | 'e' 'binop' 'e'
  *         | ! 'e'
  *
  *   'binop' ::= + | - | * | / | mod | remainder
  *             | < | > | <= | >= | & | "|"
  *             | ^ | << | >> | >>>
  *             | (bitvector casts)
  *             | "||" | && | concat
  *
  *
  * The notable typing rules are for records:
  * a record constructor takes as arguments expressions of the types of
  * the fields of all the ancestors of the current type.
  * Also, a selector is allowed with the name of a field of an ancestor.
  * Casts have to be between compatible record types, i.e.,
  * that are related by the ancestor relation.
  * An upcast is always successful.
  * A downcast to an incompatible type fails the program.
  *
  * The only values that can have a function type in reclang are function pointers.
  * Fucntions are represented by closures,
  * i.e., records containing a function pointer
  * and the environment captured by the function.
  *
  * Polymorphism is implemented with type erasure and boxing.
  * There are boxed versions of the elementary types
  * (which are regular record types).
  *
  * The typetag field
  * (which is defined in anyref, therefore is present in every record)
  * defines the type of a record value at runtime as follows:
  * 0 for boxed Boolean,
  * 1 for boxed Char,
  * 2 for boxed Int,
  * 3 for boxed Long,
  * 4 for boxed Float,
  * 5 for boxed Double,
  * 6 for boxed Array,
  * 7 for boxed String,
  * 8 for closure,
  * and then as many tags as are needed for record sorts
  * that are instantiated in the program.
  * We differentiate between records which correspond to abstract types
  * (cannot be instantiated, do not possess a tag)
  * and records which correspond to constructors
  * (can be instantiated, possess a tag).
  *
  * Two reference values are equal if their type tags are equal
  * and all fields defined by their tagged type are equal.
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
