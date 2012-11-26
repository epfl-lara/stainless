package leon
package verification

import purescala.Definitions.Program

// TODO FIXME this class is slowly but surely becoming useless,
// as we now have a notion of phases.
abstract class Analyser(context : LeonContext) {
  // Does whatever the analysis should. Uses the reporter to
  // signal results and/or errors.
  def analyse(program: Program) : Unit
}
