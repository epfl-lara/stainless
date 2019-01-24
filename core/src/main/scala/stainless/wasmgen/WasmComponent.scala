/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package wasmgen

import inox.Context
import inox.transformers.SymbolTransformer
import extraction.StainlessPipeline
import utils.{CheckFilter, DependenciesFinder}

import scala.concurrent.Future

object DebugSectionWasm extends inox.DebugSection("wasm")

class WasmAnalysis extends AbstractAnalysis {
  val name = "no analysis"
  type Report = NoReport

  def toReport = new NoReport
}

class WasmFilter(val context: Context) extends CheckFilter {
  val trees: stainless.trees.type = stainless.trees

  override def shouldBeChecked(fd: trees.FunDef): Boolean = {
    fd.params.isEmpty && super.shouldBeChecked(fd)
  }
}

object WasmComponent extends Component {
  val name = "wasm-codegen"
  val description = "Generate WebAssembly code that runs parameterless functions in the program"
  type Report = NoReport
  type Analysis = WasmAnalysis

  override val lowering: SymbolTransformer {
    val s: extraction.trees.type
    val t: extraction.trees.type
  } = inox.transformers.SymbolTransformer(new transformers.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  def run(pipeline: StainlessPipeline)(implicit context: Context) =
    new WasmComponentRun(pipeline)(context)
}

class WasmComponentRun(override val pipeline: StainlessPipeline)
                      (override implicit val context: Context) extends {
  override val component = WasmComponent
  override val trees: stainless.trees.type = stainless.trees
} with ComponentRun {

  def parse(json: io.circe.Json): NoReport = new NoReport

  override def createFilter: WasmFilter = new WasmFilter(this.context)

  override lazy val dependenciesFinder: DependenciesFinder { val t: stainless.trees.type } = new WasmDependenciesFinder

  private[stainless] def execute(functions: Seq[Identifier], symbols: trees.Symbols): Future[WasmAnalysis] = {
    Future {
      val module = codegen.LinearMemoryCodeGen.transform(new intermediate.Lowering(context).transform(symbols), functions)
      new wasm.FileWriter(module, context).writeFiles()
      new WasmAnalysis
    }
  }
}
