/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package oo

trait ExtractionCaches extends extraction.ExtractionCaches { self: oo.ExtractionContext =>

  private class ClassKey(private val cd: s.ClassDef) extends CacheKey {
    override def dependencies = Set(cd.id)

    // As in the `FunctionKey` and `SortKey` cases, we have to use a
    // special representation of the class definition for equality checking
    // as we can't rely on identifier equality here.
    private val key = (
      cd.id,
      cd.typeArgs,
      cd.parents,
      cd.fields.map(_.toVariable),
      cd.flags
    )

    override def hashCode: Int = key.hashCode
    override def equals(that: Any): Boolean = that match {
      case ck: ClassKey => (cd eq ck.cd) || (key == ck.key)
      case _ => false
    }

    override def toString: String = s"ClassKey(${cd.id.asString})"
  }

  protected given ClassKey: Keyable[s.ClassDef] with
    def apply(id: Identifier)(using symbols: s.Symbols): CacheKey = ClassKey(symbols.getClass(id))
    def apply(sort: s.ClassDef): CacheKey = new ClassKey(sort)

  override protected def getSimpleKey(id: Identifier)(using symbols: s.Symbols): CacheKey =
    symbols.lookupClass(id).map(ClassKey(_))
      .orElse(symbols.lookupTypeDef(id).map(TypeDefKey(_)))
      .getOrElse(super.getSimpleKey(id))

  private class TypeDefKey(private val td: s.TypeDef) extends CacheKey {
    override def dependencies = Set(td.id)

    // As in the `FunctionKey` and `SortKey` cases, we have to use a
    // special representation of the class definition for equality checking
    // as we can't rely on identifier equality here.
    private val key = (
      td.id,
      td.typeArgs,
      td.flags
    )

    override def hashCode: Int = key.hashCode
    override def equals(that: Any): Boolean = that match {
      case tk: TypeDefKey => (td eq tk.td) || (key == tk.key)
      case _ => false
    }

    override def toString: String = s"TypeDefKey(${td.id.asString})"
  }

  protected given TypeDefKey: Keyable[s.TypeDef] with
    def apply(id: Identifier)(using symbols: s.Symbols): CacheKey = TypeDefKey(symbols.getTypeDef(id))
    def apply(td: s.TypeDef): CacheKey = new TypeDefKey(td)
}
