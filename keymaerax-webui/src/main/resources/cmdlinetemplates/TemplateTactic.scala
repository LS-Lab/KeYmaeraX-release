package cmdlinetemplates

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.language.postfixOps

class TemplateTactic extends (() => BelleExpr) {

  def apply(): BelleExpr = {
    /* implement your Scala tactic here; replace 'close' with your tactic */
    close
  }

}
