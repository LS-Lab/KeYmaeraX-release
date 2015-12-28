package edu.cmu.cs.ls.keymaerax.btactics

/**
  * Since axioms are always referred to by their names (which are strings), we have the following problems:
  * 1) It's hard to keep everything up to date when a new axiom is added
  * 2) We don't get any static exhaustiveness checking when we case on an axiom
  *
  * AxiomInfo exists to help fix that. An AxiomInfo is just a collection of per-axiom information. The tests for
  * this object dynamically ensure it is exhaustive with respect to AxiomBase and DerivedAxioms. By adding a new
  * field to AxiomInfo you can ensure that all new axioms will have to have that field.
  * Created by bbohrer on 12/28/15.
  */
object AxiomInfo {
  case class AxiomNotFoundException(axiomName: String) extends Exception

  def apply(axiomName: String): AxiomInfo = {
    axiomName match {
      case "all instantiate" => new AxiomInfo("allI")
      case "all eliminate" => new AxiomInfo("allE")
      case "exists eliminate" => new AxiomInfo("existsE")
      case  "vacuous all quantifier" => new AxiomInfo("allV")
      case "vacuous exists quantifier" => new AxiomInfo("existV")
      case  "all dual" => new AxiomInfo("allD")
      case "exists dual" => new AxiomInfo("existD")
      case "const congruence" => new AxiomInfo("CE")
      case "const formula congruence" => new AxiomInfo("CE")
      // [a] modalities and <a> modalities
      case "<> dual" => new AxiomInfo("<>D")
      case "[] dual" => new AxiomInfo("[]D")
      case "[:=] assign" => new AxiomInfo("[:=]")
      case "<:=> assign" => new AxiomInfo("<:=>")
      case "[':=] differential assign" => new AxiomInfo("[':=]")
      case "<':=> differential assign" => new AxiomInfo("<':=>")
      case "[:=] assign equational" => new AxiomInfo("[:=]")
      case "<:=> assign equational" => new AxiomInfo("<:=>")
      case "[:=] assign update" => new AxiomInfo("[:=]")
      case "<:=> assign update" => new AxiomInfo("<:=>")
      case "[:*] assign nondet" => new AxiomInfo("[:*]")
      case  "<:*> assign nondet" => new AxiomInfo("<:*>")
      case "[?] test"    => new AxiomInfo("[?]")
      case "<?> test"    => new AxiomInfo("<?>")
      case "[++] choice" => new AxiomInfo("[++]")
      case "<++> choice" => new AxiomInfo("<++>")
      case "[;] compose" => new AxiomInfo("[;]")
      case "<;> compose" => new AxiomInfo("<;>")
      case "[*] iterate" => new AxiomInfo("[*]")
      case "<*> iterate" => new AxiomInfo("<*>")

      case "DW"              => new AxiomInfo("DW")
      case "DC differential cut" => new AxiomInfo("DC")
      case "DE differential effect" => new AxiomInfo("DE")
      case "DE differential effect (system)" => new AxiomInfo("DE")
      case "DI differential invariant" => new AxiomInfo("DI")
      case "DG differential ghost" => new AxiomInfo("DG")
      case "DG differential Lipschitz ghost system" => new AxiomInfo("DG")
      case "DG++ System" => new AxiomInfo("DG++")
      case "DG++" => new AxiomInfo("DG++")
      case ", commute" => new AxiomInfo(",")
      case "DS& differential equation solution" => new AxiomInfo("DS&")
      case "DX differential skip" => new AxiomInfo("DX")
      case "DX diamond differential skip" => new AxiomInfo("DX")

      case "&' derive and" => new AxiomInfo("&'")
      case "|' derive or" => new AxiomInfo("|'")
      case "->' derive imply" => new AxiomInfo("->'")
      case "forall' derive forall" => new AxiomInfo("forall'")
      case "exists' derive exists" => new AxiomInfo("exists'")
      case "c()' derive constant fn" => new AxiomInfo("c()'")
      case "=' derive ="   => new AxiomInfo("='")
      case ">=' derive >=" => new AxiomInfo(">='")
      case ">' derive >"   => new AxiomInfo(">'")
      case "<=' derive <=" => new AxiomInfo("<='")
      case "<' derive <"   => new AxiomInfo("<'")
      case "!=' derive !=" => new AxiomInfo("!=")
      case "-' derive neg"   => new AxiomInfo("-'")
      case "+' derive sum"   => new AxiomInfo("+'")
      case "-' derive minus" => new AxiomInfo("-'")
      case "*' derive product" => new AxiomInfo("*'")
      case "/' derive quotient" => new AxiomInfo("/'")
      case "^' derive power" => new AxiomInfo("^'")

      case "chain rule" => new AxiomInfo("chain")
      case "x' derive var"   => new AxiomInfo("x'")
      case "V vacuous" => new AxiomInfo("V")
      case "K modal modus ponens" => new AxiomInfo("K")
      case "I induction" => new AxiomInfo("I")
      // derived
      case "' linear" => new AxiomInfo("'")
      case "' linear right" => new AxiomInfo("'")
      case "DW differential weakening" => new AxiomInfo("DW")
      case "DE differential effect system" => new AxiomInfo("DE")
      // derived axioms
      case "!& deMorgan" => new AxiomInfo("!&")
      case "!| deMorgan" => new AxiomInfo("!|")
      case "!-> deMorgan" => new AxiomInfo("!->")
      case "!<-> deMorgan" => new AxiomInfo("!<->")
      case "!all" => new AxiomInfo("!all")
      case "!exists" => new AxiomInfo("!exists")
      case "![]" => new AxiomInfo("![]")
      case "!<>" => new AxiomInfo("!<>")
      case "[] split" => new AxiomInfo("[]split")
      case "<> split" => new AxiomInfo("<>split")
      case "[] split left" => new AxiomInfo("[]split")
      case "[] split right" => new AxiomInfo("[]split")
      case "<*> approx" => new AxiomInfo("<*>")
      case "<*> stuck" => new AxiomInfo("<*>")
      case "<'> stuck" => new AxiomInfo("<'>")
      case "[] post weaken" => new AxiomInfo("[]post")
      case "+<= up" => new AxiomInfo("+<=")
      case "-<= up" => new AxiomInfo("-<=")
      case "<=+ down" => new AxiomInfo("<=+")
      case "<=- down" => new AxiomInfo("<=-")
      case _ => throw new AxiomNotFoundException(axiomName)
    }
  }
}
/** The short name for an axiom is a string intended for use in the UI where space is a concern (e.g. when
  * displaying tree-style proofs). Since the goal is to be as short as possible, they are not required to be
  * unique, but should still be as suggestive as possible of what the axiom does.*/
class AxiomInfo (shortName: String)
