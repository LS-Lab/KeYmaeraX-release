import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._

import scala.language.postfixOps

/**
  * A searchy tactic tries to find a proof itself. For more control over how the proof unfolds, see script tactics.
  * @see [[CheatSheetScriptTactic]]
  */
class CheatSheetSearchyTactic extends (() => BelleExpr) {

  def apply() = {
    /* loop invariant as a String, long invariants can use Scala '|'-delimited multi-line strings for readability */
    val invariant: Formula = "v>=0".asFormula

    /* Most tactics need positions: negative values -1,... point to the antecedent, positive values 1,... to the succedent */

    /* Creates the actual tactic */
    (   prop
      & loop(invariant)('R) <(         /* tactic a<(b,c): expects 'a' to produce 2 subgoals, does 'b' on subgoal 1 and 'c' on subgoal 2 */
        print("Base case") & QE        /* print to the console and close real arithmetic goal */
        ,
        print("Use case") & QE
        ,
        print("Induction step") & normalize & OnAll(prop & diffSolve()('R) & QE)
      )
    )
  }
}
