/* Copyright 2009-2018 EPFL, Lausanne */

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

  protected implicit object ClassKey extends Keyable[s.ClassDef] {
    def apply(id: Identifier)(implicit symbols: s.Symbols): CacheKey = ClassKey(symbols.classes(id))
    def apply(sort: s.ClassDef): CacheKey = new ClassKey(sort)
  }

  override protected def getSimpleKey(id: Identifier)(implicit symbols: s.Symbols): CacheKey =
    symbols.lookupClass(id).map(ClassKey(_)).getOrElse(super.getSimpleKey(id))
}
