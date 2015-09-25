import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._

class Example1Tactic extends (() => Tactic) {

  def apply() = {
    ls(implyR) & la(andL) & ls(diffSolve) & ls(implyR) & QE
  }
}

new Example1Tactic