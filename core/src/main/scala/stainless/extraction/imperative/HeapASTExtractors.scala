/* Copyright 2009-2020 EPFL, Lausanne */

package stainless
package extraction
package imperative

trait HeapASTExtractors {
  val s: Trees
  import s._

  /** An extractor for the asRefs conversion of heap ref sets */
  object AsHeapRefSet {
    object WrapperId {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.HeapRefSetDecorations") => true
        case _ => false
      }
    }

    object Id {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.HeapRefSetDecorations.asRefs") => true
        case _ => false
      }
    }

    def unapply(expr: Expr)(using Symbols): Option[Expr] = expr match {
      case FunctionInvocation(Id(), _, Seq(
          FunctionInvocation(WrapperId(), Seq(_), Seq(objs)))) =>
        Some(objs)
      case _ => None
    }
  }

  /** An extractor for the Heap type in the stainless.lang package */
  object HeapType {
    // TODO(gsps): Cache this ClassDef
    def classDefOpt(using s: Symbols): Option[ClassDef] =
      s.lookup.get[ClassDef]("stainless.lang.Heap")

    def unapply(tpe: Type)(using Symbols): Boolean = tpe match {
      case ct: ClassType => classDefOpt.map(_.id == ct.id).getOrElse(false)
      case _ => false
    }
  }

  /** An extractor for the refEq method on AnyHeapRef */
  object RefEq {
    object Id {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.AnyHeapRef.refEq") => true
        case _ => false
      }
    }

    def unapply(expr: Expr)(using Symbols): Option[(Expr, Expr)] = expr match {
      case FunctionInvocation(Id(), _, Seq(e1, e2)) => Some((e1, e2))
      case _ => None
    }
  }

  /** An extractor for the refEq function in stainless.lang */
  object ObjectIdentity {
    object Id {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.objectId") => true
        case _ => false
      }
    }

    def unapply(e: Expr): Option[Expr] = e match {
      case FunctionInvocation(Id(), Seq(_), Seq(obj)) => Some(obj)
      case _ => None
    }
  }

  /** An extractor for the get function in stainless.lang.Heap */
  object HeapGet {
    object Id {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.Heap.get") => true
        case _ => false
      }
    }

    def unapply(e: Expr): Boolean = e match {
      case FunctionInvocation(Id(), Seq(), Seq()) => true
      case _ => false
    }
  }

  /** An extractor for the unchanged function in stainless.lang.Heap */
  object HeapUnchanged {
    object Id {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.Heap.unchanged") => true
        case _ => false
      }
    }

    def unapply(e: Expr): Option[(Expr, Expr, Expr)] = e match {
      case FunctionInvocation(Id(), Seq(), Seq(objs, heap1, heap2)) => Some((objs, heap1, heap2))
      case _ => None
    }
  }

  /** An extractor for the eval method on stainless.lang.Heap */
  object HeapEval {
    object Id {
      def unapply(id: Identifier): Boolean = id match {
        case ast.SymbolIdentifier("stainless.lang.Heap.eval") => true
        case _ => false
      }
    }

    def unapply(e: Expr): Option[(Expr, Expr)] = e match {
      case FunctionInvocation(Id(), Seq(_), Seq(heap, value)) => Some((heap, value))
      case _ => None
    }
  }
}