package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{DependentTactic, DependentPositionTactic, BelleExpr}
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Position

import scala.collection.immutable.HashMap

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

sealed trait DisplayInfo {
  val name: String
}
case class SimpleDisplayInfo(override val name: String) extends DisplayInfo
case class RuleDisplayInfo(override val name: String, conclusion: SequentDisplay, premises:List[SequentDisplay]) extends DisplayInfo
case class SequentDisplay(ante: List[String], succ: List[String])

object DerivationInfo {
  implicit def displayInfo(name: String): SimpleDisplayInfo = {SimpleDisplayInfo(name)}
  implicit def sequentDisplay(succAcc:(List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }

  implicit def qeTool:QETool = DerivedAxioms.qeTool
  case class AxiomNotFoundException(axiomName: String) extends Exception

  private val needsCodeName = "THISAXIOMSTILLNEEDSACODENAME"

  val allInfo: List[DerivationInfo] = List(
    new CoreAxiomInfo("chain rule", "o'", "Dcompose", {case () => TactixLibrary.Dcompose}),
    new CoreAxiomInfo("V vacuous", "V", "V", {case () => TactixLibrary.V}),
    new CoreAxiomInfo("K modal modus ponens", "K", "K", {case () => TactixLibrary.K}),
    // Note: the tactic I has a codeName and belleExpr, but there's no tactic that simply applies the I axiom
    new CoreAxiomInfo("I induction", "I", needsCodeName, {case () => ???}),
    new CoreAxiomInfo("all instantiate", "alli", needsCodeName, {case () => ???}),
    new CoreAxiomInfo("vacuous all quantifier", "Vall", "vacuousAll", {case () => HilbertCalculus.vacuousAll}),
    new CoreAxiomInfo("vacuous exists quantifier", "Vexists", "vacuousExists", {case () => HilbertCalculus.vacuousExists}),
    new CoreAxiomInfo("const congruence", "CCE", needsCodeName, {case () => ???}),
    new CoreAxiomInfo("const formula congruence", "CCQ", needsCodeName, {case () => ???}),
    // Note: only used to implement Dskipd
    new CoreAxiomInfo("DX differential skip", "DX", needsCodeName, {case () => ???}),
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> dual", "<.>", needsCodeName, {case () => HilbertCalculus.duald}),
    new CoreAxiomInfo("[] dual", "[.]", needsCodeName, {case () => HilbertCalculus.dualb}),
    new CoreAxiomInfo("[:=] assign", "[:=]", "assignb", {case () => HilbertCalculus.assignb}),
    new CoreAxiomInfo("<:=> assign", "<:=>", "assignd", {case () => HilbertCalculus.assignd}),
    new CoreAxiomInfo("[':=] differential assign", "[':=]", "Dassignb", {case () => HilbertCalculus.Dassignb}),
    new CoreAxiomInfo("[:=] assign equational", "[:=]=", "assignb", {case () => HilbertCalculus.assignb}),
    new CoreAxiomInfo("<:=> assign equational", "<:=>=", "assignd", {case () => HilbertCalculus.assignd}),
    new CoreAxiomInfo("[:=] assign update", "[:=]", "assignb", {case () => HilbertCalculus.assignb}),
    new CoreAxiomInfo("<:=> assign update", "<:=>", "assignd", {case () => HilbertCalculus.assignd}),
    new CoreAxiomInfo("[:*] assign nondet", "[:*]", "randomb", {case () => HilbertCalculus.randomb}),
    new CoreAxiomInfo("<:*> assign nondet", "<:*>", "randomd", {case () => HilbertCalculus.randomd}),
    new CoreAxiomInfo("[?] test", "[?]", "testb", {case () => HilbertCalculus.testb}),
    new CoreAxiomInfo("<?> test", "<?>", "testd", {case () => HilbertCalculus.testd}),
    new CoreAxiomInfo("[++] choice", "[++]", "choiceb", {case () => HilbertCalculus.choiceb}), //@todo "[\u222A]"
    new CoreAxiomInfo("<++> choice", "<++>", "choiced", {case () => HilbertCalculus.choiced}), //@todo "<\u222A>" (or possibly even "\u2329\u222A\u232A" but why asking for trouble
    new CoreAxiomInfo("[;] compose", "[;]", "composeb", {case () => HilbertCalculus.composeb}),
    new CoreAxiomInfo("<;> compose", "<;>", "composed", {case () => HilbertCalculus.composed}),
    new CoreAxiomInfo("[*] iterate", "[*]", "iterateb", {case () => HilbertCalculus.iterateb}),
    new CoreAxiomInfo("<*> iterate", "<*>", "iterated", {case () => HilbertCalculus.iterated}),
    new CoreAxiomInfo("all dual", "alld", needsCodeName, {case () => ???}),
  
    new CoreAxiomInfo("DW", "DW", "DW", {case () => HilbertCalculus.DW}),
    new CoreAxiomInfo("DC differential cut", "DC", "DC", {case () => (fml:Formula) =>  HilbertCalculus.DC(fml)}),
    new CoreAxiomInfo("DE differential effect system", "DE", "DE", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect", "DE", "DE", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect (system)", "DE", "DE", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DI differential invariant", "DI", "DI", {case () => HilbertCalculus.DI}),
    new CoreAxiomInfo("DG differential ghost", "DG", "DG", {case () => (x:Variable) => (t1:Term) => (t2:Term) => HilbertCalculus.DG(x,t1,t2)},
      List(VariableArg("x"), TermArg("t1"), TermArg("t2"))),
    new CoreAxiomInfo("DG differential Lipschitz ghost system", "DG", "DG", {case () => ???}),
    new CoreAxiomInfo("DG++ System", "DG++", needsCodeName, {case () => ???}),
    new CoreAxiomInfo("DG++", "DG++", needsCodeName, {case () => ???}),
    new CoreAxiomInfo(", commute", ",", needsCodeName, {case () => ???}),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", "DS", {case () => HilbertCalculus.DS}),
    // Derivatives
    new CoreAxiomInfo("&' derive and", "&'", "Dand", {case () => HilbertCalculus.Dand}),
    new CoreAxiomInfo("|' derive or", "|'", "Dor", {case () => HilbertCalculus.Dor}),
    new CoreAxiomInfo("->' derive imply", "->'", "Dimply", {case () => HilbertCalculus.Dimply}),
    new CoreAxiomInfo("forall' derive forall", "forall'", "Dforall", {case () => HilbertCalculus.Dforall}), //@todo "\u2200'"
    new CoreAxiomInfo("exists' derive exists", "exists'", "Dexists", {case () => HilbertCalculus.Dexists}), //@todo "\u2203'"
    new CoreAxiomInfo("c()' derive constant fn", "c()'", "Dconst", {case () => HilbertCalculus.Dconst}),
    new CoreAxiomInfo("=' derive =", "='", "Dequal", {case () => HilbertCalculus.Dequal}),
    new CoreAxiomInfo(">=' derive >=", ">='", "Dgreaterequal", {case () => HilbertCalculus.Dgreaterequal}),
    new CoreAxiomInfo(">' derive >", ">'", "Dgreater", {case () => HilbertCalculus.Dgreater}),
    new CoreAxiomInfo("<=' derive <=", "<='", "Dlessequal", {case () => HilbertCalculus.Dlessequal}),
    new CoreAxiomInfo("<' derive <", "<'", "Dless", {case () => HilbertCalculus.Dless}),
    new CoreAxiomInfo("!=' derive !=", "!='", "Dnotequal", {case () => HilbertCalculus.Dnotequal}),
    new CoreAxiomInfo("-' derive neg", "-'", "Dneg", {case () => HilbertCalculus.Dneg}),
    new CoreAxiomInfo("+' derive sum", "+'", "Dplus", {case () => HilbertCalculus.Dplus}),
    new CoreAxiomInfo("-' derive minus", "-'", "Dminus", {case () => HilbertCalculus.Dminus}),
    new CoreAxiomInfo("*' derive product", "*'", "Dtimes", {case () => HilbertCalculus.Dtimes}),
    new CoreAxiomInfo("/' derive quotient", "/'", "Dquotient", {case () => HilbertCalculus.Dquotient}),
    new CoreAxiomInfo("^' derive power", "^'", "Dpower", {case () => HilbertCalculus.Dpower}),
    new CoreAxiomInfo("x' derive variable", "x'", "Dvariable", {case () => HilbertCalculus.Dvariable}),
    new CoreAxiomInfo("x' derive var", "x'", "Dvariable", {case () => HilbertCalculus.Dvariable}),

    // Derived axioms
    new DerivedAxiomInfo("<':=> differential assign", "<':=>", "assignD", {case () => DerivedAxioms.assignDAxiom}),
    new DerivedAxiomInfo("DS differential equation solution", "DS", "DSnodomain", {case () => DerivedAxioms.DSnodomainT}),
    new DerivedAxiomInfo("Dsol& differential equation solution", "DS&", "DSddomain", {case () => DerivedAxioms.DSddomainT}),
    new DerivedAxiomInfo("Dsol differential equation solution", "DS", "DSdnodomain", {case () => DerivedAxioms.DSdnodomainT}),
    new DerivedAxiomInfo("DG differential pre-ghost", "DG", "DGpreghost", {case () => DerivedAxioms.DGpreghostT}),
    new DerivedAxiomInfo("DX diamond differential skip", "DX", "Dskipd", {case () => DerivedAxioms.DskipdT}),
    new DerivedAxiomInfo("all eliminate", "alle", "allEliminate", {case () => DerivedAxioms.allEliminateT}),
    new DerivedAxiomInfo("exists eliminate", "existse", "existsEliminate", {case () => DerivedAxioms.existsEliminateT}),
    new DerivedAxiomInfo("exists dual", "existsd", "existsDual", {case () => DerivedAxioms.existsDualT}),
    new DerivedAxiomInfo("' linear", "l'", "Dlinear", {case () => DerivedAxioms.DlinearT}),
    new DerivedAxiomInfo("' linear right", "l'", "DlinearRight", {case () => DerivedAxioms.DlinearRightT}),
    new DerivedAxiomInfo("!& deMorgan", "!&", "notAnd", {case () => DerivedAxioms.notAndT}),
    new DerivedAxiomInfo("!| deMorgan", "!|", "notOr", {case () => DerivedAxioms.notOrT}),
    new DerivedAxiomInfo("!-> deMorgan", "!->", "notImply", {case () => DerivedAxioms.notImplyT}),
    new DerivedAxiomInfo("!<-> deMorgan", "!<->", "notEquiv", {case () => DerivedAxioms.notEquivT}),
    new DerivedAxiomInfo("!all", "!all", "notAll", {case () => DerivedAxioms.notAllT}),
    new DerivedAxiomInfo("!exists", "!exists", "notExists", {case () => DerivedAxioms.notExistsT}),
    new DerivedAxiomInfo("![]", "![]", "notBox", {case () => DerivedAxioms.notBoxT}),
    new DerivedAxiomInfo("!<>", "!<>", "notDiamond", {case () => DerivedAxioms.notDiamondT}),
    new DerivedAxiomInfo("[] split", "[]&", "boxSplit", {case () => DerivedAxioms.boxSplitT}),
    new DerivedAxiomInfo("<> split", "<>|", "diamondSplit", {case () => DerivedAxioms.diamondSplitT}),
    new DerivedAxiomInfo("[] split left", "[]&<-", "boxSplitLeft", {case () => DerivedAxioms.boxSplitLeftT}),
    new DerivedAxiomInfo("[] split right", "[]&->", "boxSplitRight", {case () => DerivedAxioms.boxSplitRightT}),
    new DerivedAxiomInfo("<*> approx", "<*> approx", "loopApproxd", {case () => DerivedAxioms.loopApproxdT}),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", "loopStuck", {case () => DerivedAxioms.loopStuckT}),
    new DerivedAxiomInfo("<'> stuck", "<'> stuck", "odeStuck", {case () => DerivedAxioms.odeStuckT}),
    new DerivedAxiomInfo("[] post weaken", "[]PW", "postconditionWeaken", {case () => DerivedAxioms.postconditionWeakenT}),
    new DerivedAxiomInfo("+<= up", "+<=", "intervalUpPlus", {case () => DerivedAxioms.intervalUpPlusT}),
    new DerivedAxiomInfo("-<= up", "-<=", "intervalUpMinus", {case () => DerivedAxioms.intervalUpMinusT}),
    new DerivedAxiomInfo("<=+ down", "<=+", "intervalDownPlus", {case () => DerivedAxioms.intervalDownPlusT}),
    new DerivedAxiomInfo("<=- down", "<=-", "intervalDownMinus", {case () => DerivedAxioms.intervalDownMinusT}),
    new DerivedAxiomInfo("<-> reflexive", "<->R", "equivReflexive", {case () => DerivedAxioms.equivReflexiveT}),
    new DerivedAxiomInfo("-> distributes over &", "->&", "implyDistAnd", {case () => DerivedAxioms.implyDistAndT}),
    new DerivedAxiomInfo("-> distributes over <->", "-><->", "implyDistEquiv", {case () => DerivedAxioms.implyDistEquivT}),
    new DerivedAxiomInfo("-> weaken", "->W", "implWeaken", {case () => DerivedAxioms.implWeakenT}),
    new DerivedAxiomInfo("!! double negation", "!!", "doubleNegation", {case () => DerivedAxioms.doubleNegationT}),
    new DerivedAxiomInfo(":= assign dual", ":=D", "assignDual", {case () => DerivedAxioms.assignDualT}),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", "vacuousAssignb", {case () => DerivedAxioms.vacuousAssignbT}),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", "vacuousAssignd", {case () => DerivedAxioms.vacuousAssigndT}),
    new DerivedAxiomInfo("[*] approx", "[*] approx", "loopApproxb", {case () => DerivedAxioms.loopApproxbT}),
    new DerivedAxiomInfo("exists generalize", "existsG", "existsGeneralize", {case () => DerivedAxioms.existsGeneralizeT}),
    new DerivedAxiomInfo("all substitute", "allS", "allSubstitute", {case () => DerivedAxioms.allSubstituteT}),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", "vacuousBoxAssignNondet", {case () => DerivedAxioms.vacuousBoxAssignNondetT}),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", "vacuousDiamondAssignNondet", {case () => DerivedAxioms.vacuousDiamondAssignNondetT}),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", "DCCR", "domainCommute", {case () => DerivedAxioms.domainCommuteT}), //@todo shortname
    new DerivedAxiomInfo("& commute", "&C", "andCommute", {case () => DerivedAxioms.andCommuteT}),
    new DerivedAxiomInfo("& associative", "&A", "andAssoc", {case () => DerivedAxioms.andAssocT}),
    new DerivedAxiomInfo("-> expand", "->E", "implyExpand", {case () => DerivedAxioms.implyExpandT}),
    new DerivedAxiomInfo("-> tautology", "->taut", "implyTautology", {case () => DerivedAxioms.implyTautologyT}),
    new DerivedAxiomInfo("\\forall->\\exists", "all->exists", "forallThenExists", {case () => DerivedAxioms.forallThenExistsT}),
    new DerivedAxiomInfo("->true", "->T", "impliesTrue", {case () => DerivedAxioms.impliesTrueT}),
    new DerivedAxiomInfo("true->", "T->", "trueImplies", {case () => DerivedAxioms.trueImpliesT}),
    new DerivedAxiomInfo("&true", "&T", "andTrue", {case () => DerivedAxioms.andTrueT}),
    new DerivedAxiomInfo("true&", "T&", "trueAnd", {case () => DerivedAxioms.trueAndT}),
    new DerivedAxiomInfo("0*", "0*", "zeroTimes", {case () => DerivedAxioms.zeroTimesT}),
    new DerivedAxiomInfo("0+", "0+", "zeroPlus", {case () => DerivedAxioms.zeroPlusT}),
    new DerivedAxiomInfo("= reflexive", "=R", "equalReflexive", {case () => DerivedAxioms.equalReflexiveT}),
    new DerivedAxiomInfo("* commute", "*C", "timesCommute", {case () => DerivedAxioms.timesCommuteT}),
    new DerivedAxiomInfo("= commute", "=C", "equalCommute", {case () => DerivedAxioms.equalCommuteT}),
    new DerivedAxiomInfo("<=", "<=", "lessEqual", {case () => DerivedAxioms.lessEqualT}),
    new DerivedAxiomInfo("= negate", "!!=", "notNotEqual", {case () => DerivedAxioms.notNotEqualT}),
    new DerivedAxiomInfo("!= negate", "! =", "notEqual", {case () => DerivedAxioms.notEqualT}),
    new DerivedAxiomInfo("! <", "!<", "notLess", {case () => DerivedAxioms.notLessT}),
    new DerivedAxiomInfo("! >", "!>", "notGreater", {case () => DerivedAxioms.notGreaterT}),
    new DerivedAxiomInfo("< negate", "!<=", "notGreaterEqual", {case () => DerivedAxioms.notGreaterEqualT}),
    new DerivedAxiomInfo(">= flip", ">=F", "flipGreaterEqual", {case () => DerivedAxioms.flipGreaterEqualT}),
    new DerivedAxiomInfo("> flip", ">F", "flipGreater", {case () => DerivedAxioms.flipGreaterT}),
    new DerivedAxiomInfo("<", "<", "less", {case () => DerivedAxioms.lessT}),
    new DerivedAxiomInfo(">", ">", "greater", {case () => DerivedAxioms.greaterT}),
    new DerivedAxiomInfo("abs", "abs", "abs", {case () => DerivedAxioms.absT}),
    new DerivedAxiomInfo("min", "min", "min", {case () => DerivedAxioms.minT}),
    new DerivedAxiomInfo("max", "max", "max", {case () => DerivedAxioms.maxT}),
    new DerivedAxiomInfo("*<= up", "*<=", "intervalUpTimes", {case () => DerivedAxioms.intervalUpTimesT}),
    new DerivedAxiomInfo("1Div<= up", "1/<=", "intervalUp1Divide", {case () => DerivedAxioms.intervalUp1DivideT}),
    new DerivedAxiomInfo("Div<= up", "/<=", "intervalUpDivide", {case () => DerivedAxioms.intervalUpDivideT}),
    new DerivedAxiomInfo("<=* down", "<=*", "intervalDownTimes", {case () => DerivedAxioms.intervalDownTimesT}),
    new DerivedAxiomInfo("<=1Div down", "<=1/", "intervalDown1Divide", {case () => DerivedAxioms.intervalDown1DivideT}),
    new DerivedAxiomInfo("<=Div down", "<=/", "intervalDownDivide", {case () => DerivedAxioms.intervalDownDivide}),
    new DerivedAxiomInfo("! !=", "!!=", "notNotEqual", {case () => ???}),
    new DerivedAxiomInfo("! =", "! =", "notEqual", {case () => DerivedAxioms.notEqualT}),
    new DerivedAxiomInfo("! <=", "!<=", "notLessEqual", {case () => DerivedAxioms.notLessEqualT}),
    new DerivedAxiomInfo("* associative", "*A", "timesAssociative", {case () => DerivedAxioms.timesAssociativeT}),
    new DerivedAxiomInfo("* commutative", "*C", "timesCommutative", {case () => DerivedAxioms.timesCommutativeT}),
    new DerivedAxiomInfo("* inverse", "*i", "timesInverse", {case () => DerivedAxioms.timesInverseT}),
    new DerivedAxiomInfo("* closed", "*c", "timesClosed", {case () => DerivedAxioms.timesClosedT}),
    new DerivedAxiomInfo("* identity", "*I", "timesIdentity", {case () => DerivedAxioms.timesIdentityT}),
    new DerivedAxiomInfo("+ associative", "+A", "plusAssociative", {case () => DerivedAxioms.plusAssociativeT}),
    new DerivedAxiomInfo("+ commutative", "+C", "plusCommutative", {case () => DerivedAxioms.plusCommutativeT}),
    new DerivedAxiomInfo("+ inverse", "+i", "plusInverse", {case () => DerivedAxioms.plusInverseT}),
    new DerivedAxiomInfo("+ closed", "+c", "plusClosed", {case () => DerivedAxioms.plusClosedT}),
    new DerivedAxiomInfo("positivity", "Pos", "positivity", {case () => DerivedAxioms.positivityT}),
    new DerivedAxiomInfo("distributive", "*+", "distributive", {case () => DerivedAxioms.distributiveT}),
    new DerivedAxiomInfo("all distribute", "Dall", "allDistribute", {case () => DerivedAxioms.allDistributeT}),
    new DerivedAxiomInfo("[]~><> propagation", "[]~><>", "boxDiamondPropagation", {case () => DerivedAxioms.boxDiamondPropagationT}),
    //@todo internal only
    new DerivedAxiomInfo("K1", "K1", "K1", {case () => ???}),
    new DerivedAxiomInfo("K2", "K2", "K2", {case () => ???}),
    new DerivedAxiomInfo("P1", "P1", "P1", {case () => ???}),
    new DerivedAxiomInfo("P2", "P2", "P2", {case () => ???}),
    new DerivedAxiomInfo("P3", "P3", "P3", {case () => ???}),
    new DerivedAxiomInfo("P9", "P9", "P9", {case () => ???}),
    new DerivedAxiomInfo("P10", "P10", "P10", {case () => ???}),
    // axioms for unit tests
    new DerivedAxiomInfo("exists dual dummy", "DUMMY", "dummyexistsDualAxiomT", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy", "DUMMY", "dummyallDualAxiom", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy 2", "DUMMY", "dummyallDualAxiom2", {case () => ???}),
    new DerivedAxiomInfo("+id' dummy", "DUMMY", "dummyDplus0", {case () => ???}),
    new DerivedAxiomInfo("+*' reduce dummy", "DUMMY", "dummyDplustimesreduceAxiom", {case () => ???}),
    new DerivedAxiomInfo("+*' expand dummy", "DUMMY", "dummyDplustimesexpandAxiom", {case () => ???}),
    new DerivedAxiomInfo("^' dummy", "DUMMY", "dummyDpowerconsequence", {case () => ???}),

    // Note: Tactic info does not cover all tactics yet.
    // Proof rule position PositionTactics
    new PositionTacticInfo("notL", "!L", {case () => ProofRuleTactics.notL}),  //@todo
    new PositionTacticInfo("notR", "!R", {case () => ProofRuleTactics.notR}),
    new PositionTacticInfo("andR", "^R", {case () => ProofRuleTactics.andR}),  //@todo "\u2227R"
    new PositionTacticInfo("andL", "^L", {case () => ProofRuleTactics.andL}), //@todo "\u2227L"
    new PositionTacticInfo("orL", "|L", {case () => ProofRuleTactics.orL}), //@todo "\u2228L"
    new PositionTacticInfo("orR", "|R", {case () => ProofRuleTactics.orR}), //@todo "\u2228R"
    new PositionTacticInfo("implyL", "->L", {case () => ProofRuleTactics.implyL}), //@todo "\u2192L"
    new PositionTacticInfo("implyR", "->R", {case () => ProofRuleTactics.implyR}), //@todo "\u2192R"
    new PositionTacticInfo("equivL", "<->L", {case () => ProofRuleTactics.equivL}), //@todo "\u2194L"
    new PositionTacticInfo("equivR", "<->R", {case () => ProofRuleTactics.equivR}), //@todo "\u2194R"
    new PositionTacticInfo("commuteEquivL", "<->CL", {case () => ProofRuleTactics.commuteEquivL}),
    new PositionTacticInfo("commuteEquivR", "<->CR", {case () => ProofRuleTactics.commuteEquivR}),
    new PositionTacticInfo("equivifyR", "<->R", {case () => ProofRuleTactics.equivifyR}),
    new PositionTacticInfo("hideL", "hide", {case () => ProofRuleTactics.hideL}),  //@todo W for weakening? If people know that
    new PositionTacticInfo("hideR", "hide", {case () => ProofRuleTactics.hideR}),
    new PositionTacticInfo("coHideL", "hide", {case () => ProofRuleTactics.coHideL}),
    new PositionTacticInfo("coHideR", "hide", {case () => ProofRuleTactics.coHideR}),
    new PositionTacticInfo("closeFalse", "close", {case () => ProofRuleTactics.closeFalse}),
    new PositionTacticInfo("closeTrue", "close", {case () => ProofRuleTactics.closeTrue}),
    new PositionTacticInfo("skolemizeL", "skolem", {case () => ProofRuleTactics.skolemizeL}),
    new PositionTacticInfo("skolemizeR", "skolem", {case () => ProofRuleTactics.skolemizeR}),
    new PositionTacticInfo("skolemize", "skolem", {case () => ProofRuleTactics.skolemize}),
    new PositionTacticInfo("coHide", "hide", {case () => ProofRuleTactics.coHide}),
    new PositionTacticInfo("hide", "hide", {case () => ProofRuleTactics.hide}),

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "hide", {case () => ProofRuleTactics.coHide2}),
    new TwoPositionTacticInfo("exchangeL", "X", {case () => ProofRuleTactics.exchangeL}),
    new TwoPositionTacticInfo("exchangeR", "X", {case () => ProofRuleTactics.exchangeR}),
    new TwoPositionTacticInfo("close", "close", {case () => ProofRuleTactics.close}),

    // Proof rule input tactics
    new InputTacticInfo("cut", "cut", List(FormulaArg("cutFormula")), {case () => (fml:Formula) => ProofRuleTactics.cut(fml)}),
    // Proof rule input position tactics
    //@todo Move these DependentPositionTactic wrappers to ProofRuleTactics?
    new InputPositionTacticInfo("cutL", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutL") {
        /** Create the actual tactic to be applied at position pos */
        override def factory(pos: Position): DependentTactic = new DependentTactic("cutL") {
          ProofRuleTactics.cutL(fml)(pos)
        }
      }}),
    new InputPositionTacticInfo("cutR", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutR") {
        /** Create the actual tactic to be applied at position pos */
        override def factory(pos: Position): DependentTactic = new DependentTactic("cutR") {
          ProofRuleTactics.cutR(fml)(pos)
        }
      }}),
    new InputPositionTacticInfo("cutLR", "cut", List(FormulaArg("cutFormula")),
      {case () => (fml:Formula) => new DependentPositionTactic("cutLR") {
          /** Create the actual tactic to be applied at position pos */
          override def factory(pos: Position): DependentTactic = new DependentTactic("cutLR") {
            ProofRuleTactics.cutLR(fml)(pos)
          }
        }}),
    new InputPositionTacticInfo("loop",
      RuleDisplayInfo("loop",(List("&Gamma;"), List("j(&oline;x)", "&Delta;")),
        List(
          (List("&Gamma;"),List("j(&oline;x)", "&Delta;")),
          (List("j(&oline;x)"),List("[a]j(&oline;x)")),
          (List("j(&oline;x)"),List("P"))))
      , List(FormulaArg("invariant")), {case () => (fml:Formula) => TactixLibrary.loop(fml)}),

    // TactixLibrary tactics
    new PositionTacticInfo("step", "step", {case () => TactixLibrary.step}),
    new PositionTacticInfo("stepAt", "stepAt", {case () => HilbertCalculus.stepAt}),
    new PositionTacticInfo("normalize", "normalize", {case () => TactixLibrary.normalize}),
    new PositionTacticInfo("prop", "prop", {case () => TactixLibrary.prop}),
    // Technically in InputPositionTactic(Generator[Formula, {case () => ???}), but the generator is optional
    new PositionTacticInfo("master", "master", {case () => TactixLibrary.master()}),
    new TacticInfo("QE", "QE",  {case () => TactixLibrary.QE}, needsTool = true),

    // Differential tactics
    new PositionTacticInfo("diffInd", "diffInd",  {case () => DifferentialTactics.diffInd}, needsTool = true),
    new InputPositionTacticInfo("diffCut", "diffCut", List(FormulaArg("cutFormula")), {case () => (fml:Formula) => DifferentialTactics.diffCut(fml)}, needsTool = true),
    new InputPositionTacticInfo("diffInvariant", "diffInv", List(FormulaArg("invariant")), {case () => (fml:Formula) => DifferentialTactics.diffInvariant(qeTool, fml)}, needsTool = true),
    new PositionTacticInfo("Dconstify", "Dconst", {case () => DifferentialTactics.Dconstify}),
    new PositionTacticInfo("Dvariable", "Dvar", {case () => DifferentialTactics.Dvariable}),

    // DLBySubst
    new InputPositionTacticInfo("I", "I", List(FormulaArg("invariant")), {case () => (fml:Formula) => DLBySubst.I(fml)})
  )

  private val byCodeName: Map[String, DerivationInfo] =
  /* @todo Decide on a naming convention. Until then, making everything case insensitive */
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc.+((info.codeName.toLowerCase(), info))
    }

  private val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc.+((info.canonicalName, info))
    }

  def apply(axiomName: String): DerivationInfo = {
    byCanonicalName.get(axiomName) match {
      case Some(info) => info
      case None => throw new AxiomNotFoundException(axiomName)
    }
  }

  def ofCodeName(name:String) = byCodeName.get(name.toLowerCase).get
}

object AxiomInfo {
  def apply(axiomName: String): AxiomInfo =
    DerivationInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }
}

object TacticInfo {
  def apply(tacticName: String): TacticInfo =
    DerivationInfo(tacticName) match {
      case info:TacticInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a tactic")
    }
}

sealed trait ArgInfo {
  val sort: String
  val name: String
}
case class FormulaArg (override val name: String) extends ArgInfo {
  val sort = "formula"
}
case class VariableArg (override val name: String) extends ArgInfo {
  val sort = "variable"
}
case class TermArg (override val name: String) extends ArgInfo {
  val sort = "term"
}
sealed trait DerivationInfo {
  val canonicalName: String
  val display: DisplayInfo
  val codeName: String
  val inputs: List[ArgInfo] = Nil
  // This is an Any because for input tactics it's a function <inputType> => BelleExpr. For non-imput tactics sthis is a
  // BelleExpr. The input information for tactics allows us to disambiguate.
  def belleExpr: Any
  //@todo add formattedName/unicodeName: String
  val numPositionArgs: Int = 0
}

trait AxiomInfo extends DerivationInfo {
  def formula: Formula
}

case class CoreAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any, override val inputs:List[ArgInfo] = Nil) extends AxiomInfo {
  def belleExpr = expr()
  override def formula:Formula = {
    Axiom.axioms.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override val numPositionArgs = 1
}

case class DerivedAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any) extends AxiomInfo {
  def belleExpr = expr()
  override def formula: Formula = {
    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
      case Some(fml) => fml._1
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override val numPositionArgs = 1
}

class TacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false) extends DerivationInfo {
  def belleExpr = expr()
  val canonicalName = codeName
}

case class PositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool)

case class InputPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => Any, needsTool: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool) {
  override val numPositionArgs = 2
}