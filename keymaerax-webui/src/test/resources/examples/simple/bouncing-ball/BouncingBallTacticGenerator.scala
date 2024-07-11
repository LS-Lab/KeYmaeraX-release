import org.keymaerax.bellerophon.BelleExpr

import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.parser.StringConverter._

import scala.language.postfixOps

class BouncingBallTacticGenerator extends (() => BelleExpr) {

  def apply() = {
    implyR(1) & (andL('L)*) & loop("v^2<=2*g()*(H-h) & h>=0".asFormula)(1) <(
      QE,
      QE,
      composeb(1) & choiceb(1, 1::Nil) & testb(1, 1::0::Nil) & composeb(1, 1::1::Nil) &
        testb(1, 1::1::Nil) & assignb(1, 1::1::1::Nil) & solve(1) & allR(1) & (implyR(1)*2) &
        allL("t_".asTerm)('Llast) & QE
      )
  }

}
