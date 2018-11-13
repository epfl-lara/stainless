package stainless.frontends.fast.extraction
import scala.reflect.runtime.{universe => ru}
import dotty.tools.dotc.ast.untpd

trait ExtractMods {

  def extractMods(tree: untpd.MemberDef): untpd.Modifiers = {
    val mirror = ru.runtimeMirror(tree.getClass.getClassLoader).reflect(tree)
    val rawMethodSymbol = mirror.symbol.typeSignature.member(ru.TermName("rawMods"))
    val mods: untpd.Modifiers = mirror.reflectMethod(rawMethodSymbol.asMethod)().asInstanceOf[untpd.Modifiers]
    mods
  }
}