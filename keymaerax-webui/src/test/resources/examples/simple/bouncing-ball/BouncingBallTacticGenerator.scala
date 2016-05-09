import edu.cmu.cs.ls.keymaerax.bellerophon.{TheType, BelleExpr}

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.language.postfixOps

class BouncingBallTacticGenerator extends (() => BelleExpr) {

  def apply() = {
    implyR(1) & andL('L)*@TheType() & loop("v^2<=2*g()*(H-h) & h>=0".asFormula)(1) <(
      QE,
      QE,
      composeb(1) & choiceb(1, 1::Nil) & testb(1, 1::0::Nil) & composeb(1, 1::1::Nil) &
        testb(1, 1::1::Nil) & assignb(1, 1::1::1::Nil) & debug("Foo") & diffSolve()(1) & QE
      )
  }

}

new BouncingBallTacticGenerator()