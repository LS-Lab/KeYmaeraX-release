/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
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

/** UI display information on how to show an axiom, rule, or tactic application */
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
  case class AxiomNotFoundException(axiomName: String) extends ProverException("Axiom with said name not found: " + axiomName)

  private val needsCodeName = "THISAXIOMSTILLNEEDSACODENAME"

  private def useAt(l:Lemma):BelleExpr = HilbertCalculus.useAt(l)
  /**
    * Central registry for axiom, derived axiom, proof rule, and tactic meta-information.
    * Transferred into subsequent maps etc for efficiency reasons.
    */
  private val allInfo: List[DerivationInfo] = List(
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> diamond", "<.>", "diamond", {case () => ???}),
    new DerivedAxiomInfo("[] box", "[.]", "box", {case () => ???}),
    new CoreAxiomInfo("[:=] assign", "[:=]", "assignb", {case () => HilbertCalculus.assignb}),
    new DerivedAxiomInfo("<:=> assign", "<:=>", "assignd", {case () => HilbertCalculus.assignd}),
    new CoreAxiomInfo("[:=] assign equality", "[:=]=", "assignbeq", {case () => ???}),
    //@todo new DerivedAxiomInfo("<:=> assign equality", "<:=>=", "assigndeq", {case () => ???}),
    new CoreAxiomInfo("[':=] differential assign", "[':=]", "Dassignb", {case () => HilbertCalculus.Dassignb}),
    new CoreAxiomInfo("[:*] assign nondet", "[:*]", "randomb", {case () => HilbertCalculus.randomb}),
    new CoreAxiomInfo("[?] test", "[?]", "testb", {case () => HilbertCalculus.testb}),
    new DerivedAxiomInfo("<?> test", "<?>", "testd", {case () => HilbertCalculus.testd}),
    new CoreAxiomInfo("[++] choice", "[++]", "choiceb", {case () => HilbertCalculus.choiceb}), //@todo "[\u222A]"
    new DerivedAxiomInfo("<++> choice", "<++>", "choiced", {case () => HilbertCalculus.choiced}), //@todo "<\u222A>" (or possibly even "\u2329\u222A\u232A" but why asking for trouble
    new CoreAxiomInfo("[;] compose", "[;]", "composeb", {case () => HilbertCalculus.composeb}),
    new DerivedAxiomInfo("<;> compose", "<;>", "composed", {case () => HilbertCalculus.composed}),
    new CoreAxiomInfo("[*] iterate", "[*]", "iterateb", {case () => HilbertCalculus.iterateb}),
    new DerivedAxiomInfo("<*> iterate", "<*>", "iterated", {case () => HilbertCalculus.iterated}),
  //@todo if hybrid games enabled
    //new CoreAxiomInfo("<d> dual", "<d>", "duald", {case () => HilbertCalculus.duald}),
    //new DerivedAxiomInfo("[d] dual", "[d]", "dualb", {case () => HilbertCalculus.dualb}),
    new CoreAxiomInfo("K modal modus ponens", "K", "K", {case () => TactixLibrary.K}),
    //@note the tactic I has a codeName and belleExpr, but there's no tactic that simply applies the I axiom
  //@todo why isn't the code name just "I"? And the belleExpr could be useAt("I")?
    new CoreAxiomInfo("I induction", "I", "induction", {case () => ???}),
    new CoreAxiomInfo("V vacuous", "V", "V", {case () => TactixLibrary.V}),

    // differential equation axioms
    new CoreAxiomInfo("DW", "DW", "DWaxiom", {case () => HilbertCalculus.DW}),
    new CoreAxiomInfo("DC differential cut", "DC", "DC", {case () => (fml:Formula) =>  HilbertCalculus.DC(fml)}),
    new CoreAxiomInfo("DE differential effect", "DE", "DE", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect (system)", "DE", "DEs", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DI differential invariant", "DI", "DI", {case () => HilbertCalculus.DI}),
    new CoreAxiomInfo("DG differential ghost", "DG", "DG", {case () => (x:Variable) => (t1:Term) => (t2:Term) => HilbertCalculus.DG(x,t1,t2)},
      List(VariableArg("x"), TermArg("t1"), TermArg("t2"))),
    new CoreAxiomInfo("DG differential Lipschitz ghost system", "DG", "DGs", {case () => ???}),
    new CoreAxiomInfo("DG++ System", "DG++", "DGpps", {case () => ???}),
    new CoreAxiomInfo("DG++", "DG++", "DGpp", {case () => ???}),
    new CoreAxiomInfo(", commute", ",", "commaCommute", {case () => ???}),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", "DS", {case () => HilbertCalculus.DS}),

    // Differential Axioms
    new CoreAxiomInfo("c()' derive constant fn", "c()'", "Dconst", {case () => HilbertCalculus.Dconst}),
    new CoreAxiomInfo("x' derive var", "x'", "Dvar", {case () => HilbertCalculus.Dvariable}),
    new DerivedAxiomInfo("x' derive variable", "x'", "DvariableAxiom", {case () => HilbertCalculus.Dvariable}),
    new CoreAxiomInfo("+' derive sum", "+'", "Dplus", {case () => HilbertCalculus.Dplus}),
    new CoreAxiomInfo("-' derive neg", "-'", "Dneg", {case () => HilbertCalculus.Dneg}),
    new CoreAxiomInfo("-' derive minus", "-'", "Dminus", {case () => HilbertCalculus.Dminus}),
    new CoreAxiomInfo("*' derive product", "*'", "Dtimes", {case () => HilbertCalculus.Dtimes}),
    new CoreAxiomInfo("/' derive quotient", "/'", "Dquotient", {case () => HilbertCalculus.Dquotient}),
    new CoreAxiomInfo("^' derive power", "^'", "Dpower", {case () => HilbertCalculus.Dpower}),
    new CoreAxiomInfo("chain rule", "o'", "Dcompose", {case () => TactixLibrary.Dcompose}),

    new CoreAxiomInfo("=' derive =", "='", "Dequal", {case () => HilbertCalculus.Dequal}),
    new CoreAxiomInfo(">=' derive >=", ">='", "Dgreaterequal", {case () => HilbertCalculus.Dgreaterequal}),
    new CoreAxiomInfo(">' derive >", ">'", "Dgreater", {case () => HilbertCalculus.Dgreater}),
    new CoreAxiomInfo("<=' derive <=", "<='", "Dlessequal", {case () => HilbertCalculus.Dlessequal}),
    new CoreAxiomInfo("<' derive <", "<'", "Dless", {case () => HilbertCalculus.Dless}),
    new CoreAxiomInfo("!=' derive !=", "!='", "Dnotequal", {case () => HilbertCalculus.Dnotequal}),
    new CoreAxiomInfo("&' derive and", "&'", "Dand", {case () => HilbertCalculus.Dand}),
    new CoreAxiomInfo("|' derive or", "|'", "Dor", {case () => HilbertCalculus.Dor}),
    new DerivedAxiomInfo("->' derive imply", "->'", "Dimply", {case () => HilbertCalculus.Dimply}),
    new CoreAxiomInfo("forall' derive forall", "forall'", "Dforall", {case () => HilbertCalculus.Dforall}), //@todo "\u2200'"
    new CoreAxiomInfo("exists' derive exists", "exists'", "Dexists", {case () => HilbertCalculus.Dexists}), //@todo "\u2203'"

    // first-order logic quantifiers
    new CoreAxiomInfo("all instantiate", "alli", "alli"/*@todo allinst?*/, {case () => ???}),
    new DerivedAxiomInfo("all distribute", "all->", "allDistribute"/*@todo alldist*/, {case () => useAt(DerivedAxioms.allDistributeAxiom)}),
    new CoreAxiomInfo("vacuous all quantifier", "Vall", "vacuousAll", {case () => HilbertCalculus.vacuousAll}),
    new DerivedAxiomInfo("vacuous exists quantifier", "Vexists", "vacuousExists", {case () => HilbertCalculus.vacuousExists}),

    // more
    new CoreAxiomInfo("const congruence", "CCE", "constCongruence", {case () => ???}),
    new CoreAxiomInfo("const formula congruence", "CCQ", "constFormulaCongruence", {case () => ???}),
    // Note: only used to implement Dskipd
    new CoreAxiomInfo("DX differential skip", "DX", "DX", {case () => ???}),

    new CoreAxiomInfo("all dual", "alld", "alld", {case () => }),
    new CoreAxiomInfo("all eliminate", "alle", "alle", {case () => }),


    // Derived axioms
    new DerivedAxiomInfo("[:=] assign update", "[:=]", "assignbup", {case () => HilbertCalculus.assignb}),
    new DerivedAxiomInfo("<:=> assign update", "<:=>", "assigndup", {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:*> assign nondet", "<:*>", "randomd", {case () => HilbertCalculus.randomd}),
    new DerivedAxiomInfo("[:=] assign equational", "[:=]==", "assignbequational", {case () => HilbertCalculus.assignb}),
    new DerivedAxiomInfo("<:=> assign equational", "<:=>==", "assigndequational", {case () => HilbertCalculus.assignd}),
    /* @todo replace all the axioms with useAt(axiom) */
    new DerivedAxiomInfo("<':=> differential assign", "<':=>", "Dassignd", {case () => useAt(DerivedAxioms.assignDAxiom)}),
    new DerivedAxiomInfo("DS differential equation solution", "DS", "DSnodomain", {case () => useAt(DerivedAxioms.DSnodomain)}),
    new DerivedAxiomInfo("Dsol& differential equation solution", "DS&", "DSddomain", {case () => useAt(DerivedAxioms.DSddomain)}),
    new DerivedAxiomInfo("Dsol differential equation solution", "DS", "DSdnodomain", {case () => useAt(DerivedAxioms.DSdnodomain)}),
    new DerivedAxiomInfo("DG differential pre-ghost", "DG", "DGpreghost", {case () => useAt(DerivedAxioms.DGpreghost)}),
    new DerivedAxiomInfo("DW differential weakening", "DW", "DWeaken", {case () => HilbertCalculus.DW}),
    new DerivedAxiomInfo("DX diamond differential skip", "DX", "Dskipd", {case () => useAt(DerivedAxioms.Dskipd)}),
//    new DerivedAxiomInfo("all eliminate", "alle", "allEliminate", {case () => useAt(DerivedAxioms.allEliminateAxiom)}),
    new DerivedAxiomInfo("exists eliminate", "existse", "existsEliminate", {case () => useAt(DerivedAxioms.existsEliminate)}),
    new DerivedAxiomInfo("exists dual", "existsd", "existsDual", {case () => useAt(DerivedAxioms.existsDualAxiom)}),
    new DerivedAxiomInfo("' linear", "l'", "Dlinear", {case () => useAt(DerivedAxioms.Dlinear)}),
    new DerivedAxiomInfo("' linear right", "l'", "DlinearRight", {case () => useAt(DerivedAxioms.DlinearRight)}),
    new DerivedAxiomInfo("!& deMorgan", "!&", "notAnd", {case () => useAt(DerivedAxioms.notAnd)}),
    new DerivedAxiomInfo("!| deMorgan", "!|", "notOr", {case () => useAt(DerivedAxioms.notOr)}),
    new DerivedAxiomInfo("!-> deMorgan", "!->", "notImply", {case () => useAt(DerivedAxioms.notImply)}),
    new DerivedAxiomInfo("!<-> deMorgan", "!<->", "notEquiv", {case () => useAt(DerivedAxioms.notEquiv)}),
    new DerivedAxiomInfo("!all", "!all", "notAll", {case () => useAt(DerivedAxioms.notAll)}),
    new DerivedAxiomInfo("!exists", "!exists", "notExists", {case () => useAt(DerivedAxioms.notExists)}),
    new DerivedAxiomInfo("![]", "![]", "notBox", {case () => useAt(DerivedAxioms.notBox)}),
    new DerivedAxiomInfo("!<>", "!<>", "notDiamond", {case () => useAt(DerivedAxioms.notDiamond)}),
    new DerivedAxiomInfo("[] split", "[]&", "boxAnd", {case () => HilbertCalculus.useAt(DerivedAxioms.boxAnd)}),
    new DerivedAxiomInfo("<> split", "<>|", "diamondOr", {case () => useAt(DerivedAxioms.diamondOr)}),
//    new DerivedAxiomInfo("<> split left", "<>|<-", "diamondSplitLeft", {case () => useAt(DerivedAxioms.diamondSplitLeft)}),
//    new DerivedAxiomInfo("[] split left", "[]&<-", "boxSplitLeft", {case () => useAt(DerivedAxioms.boxSplitLeft)}),
//    new DerivedAxiomInfo("[] split right", "[]&->", "boxSplitRight", {case () => useAt(DerivedAxioms.boxSplitRight)}),
    new DerivedAxiomInfo("<*> approx", "<*> approx", "loopApproxd", {case () => useAt(DerivedAxioms.loopApproxd)}),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", "loopStuck", {case () => useAt(DerivedAxioms.loopStuck)}),
    new DerivedAxiomInfo("<'> stuck", "<'> stuck", "odeStuck", {case () => useAt(DerivedAxioms.odeStuck)}),
    new DerivedAxiomInfo("[] post weaken", "[]PW", "postWeaken", {case () => useAt(DerivedAxioms.postconditionWeaken)}),
    new DerivedAxiomInfo("+<= up", "+<=", "intervalUpPlus", {case () => useAt(DerivedAxioms.intervalUpPlus)}),
    new DerivedAxiomInfo("-<= up", "-<=", "intervalUpMinus", {case () => useAt(DerivedAxioms.intervalUpMinus)}),
    new DerivedAxiomInfo("<=+ down", "<=+", "intervalDownPlus", {case () => useAt(DerivedAxioms.intervalDownPlus)}),
    new DerivedAxiomInfo("<=- down", "<=-", "intervalDownMinus", {case () => useAt(DerivedAxioms.intervalDownMinus)}),
    new DerivedAxiomInfo("<-> reflexive", "<->R", "equivReflexive", {case () => useAt(DerivedAxioms.equivReflexiveAxiom)}),
    new DerivedAxiomInfo("-> distributes over &", "->&", "implyDistAnd", {case () => useAt(DerivedAxioms.implyDistAndAxiom)}),
    new DerivedAxiomInfo("-> distributes over <->", "-><->", "implyDistEquiv", {case () => useAt(DerivedAxioms.implyDistEquivAxiom)}),
    new DerivedAxiomInfo("-> weaken", "->W", "implyWeaken", {case () => useAt(DerivedAxioms.implWeaken)}),
    new DerivedAxiomInfo("!! double negation", "!!", "doubleNegation", {case () => useAt(DerivedAxioms.doubleNegationAxiom)}),
    new DerivedAxiomInfo(":= assign dual", ":=D", "assignDual", {case () => useAt(DerivedAxioms.assignDualAxiom)}),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", "vacuousAssignb", {case () => useAt(DerivedAxioms.vacuousAssignbAxiom)}),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", "vacuousAssignd", {case () => useAt(DerivedAxioms.vacuousAssigndAxiom)}),
    new DerivedAxiomInfo("[*] approx", "[*] approx", "loopApproxb", {case () => useAt(DerivedAxioms.loopApproxb)}),
  //@todo might have a better name
    new DerivedAxiomInfo("exists generalize", "existsG", "existsGeneralize", {case () => useAt(DerivedAxioms.existsGeneralize)}),
    new DerivedAxiomInfo("all substitute", "allS", "allSubstitute", {case () => useAt(DerivedAxioms.allSubstitute)}),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", "vacuousBoxAssignNondet", {case () => useAt(DerivedAxioms.vacuousBoxAssignNondetAxiom)}),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", "vacuousDiamondAssignNondet", {case () => useAt(DerivedAxioms.vacuousDiamondAssignNondetAxiom)}),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", "{&}C", "domainCommute", {case () => useAt(DerivedAxioms.domainCommute)}), //@todo shortname
    new DerivedAxiomInfo("& commute", "&C", "andCommute", {case () => useAt(DerivedAxioms.andCommute)}),
    new DerivedAxiomInfo("& associative", "&A", "andAssoc", {case () => useAt(DerivedAxioms.andAssoc)}),
    new DerivedAxiomInfo("-> expand", "->E", "implyExpand", {case () => useAt(DerivedAxioms.implyExpand)}),
    new DerivedAxiomInfo("-> tautology", "->taut", "implyTautology", {case () => useAt(DerivedAxioms.implyTautology)}),
    new DerivedAxiomInfo("\\forall->\\exists", "all->exists", "forallThenExists", {case () => useAt(DerivedAxioms.forallThenExistsAxiom)}),
    new DerivedAxiomInfo("->true", "->T", "implyTrue", {case () => useAt(DerivedAxioms.impliesTrue)}),
    new DerivedAxiomInfo("true->", "T->", "trueImply", {case () => useAt(DerivedAxioms.trueImplies)}),
    new DerivedAxiomInfo("&true", "&T", "andTrue", {case () => useAt(DerivedAxioms.andTrue)}),
    new DerivedAxiomInfo("true&", "T&", "trueAnd", {case () => useAt(DerivedAxioms.trueAnd)}),
    new DerivedAxiomInfo("0*", "0*", "zeroTimes", {case () => useAt(DerivedAxioms.zeroTimes)}),
    new DerivedAxiomInfo("0+", "0+", "zeroPlus", {case () => useAt(DerivedAxioms.zeroPlus)}),
    new DerivedAxiomInfo("*0", "*0", "timesZero", {case () => useAt(DerivedAxioms.timesZero)}),
    new DerivedAxiomInfo("+0", "+0", "plusZero", {case () => useAt(DerivedAxioms.plusZero)}),
    new DerivedAxiomInfo("= reflexive", "=R", "equalReflexive", {case () => useAt(DerivedAxioms.equalReflex)}),
    new DerivedAxiomInfo("= commute", "=C", "equalCommute", {case () => useAt(DerivedAxioms.equalCommute)}),
    new DerivedAxiomInfo("<=", "<=", "lessEqual", {case () => useAt(DerivedAxioms.lessEqual)}),
    new DerivedAxiomInfo("= negate", "!!=", "equalNegate", {case () => useAt(DerivedAxioms.notNotEqual)}),
    new DerivedAxiomInfo("!= negate", "! =", "notEqualNegate", {case () => useAt(DerivedAxioms.notEqual)}),
    new DerivedAxiomInfo("! <", "!<", "notLess", {case () => useAt(DerivedAxioms.notLess)}),
    new DerivedAxiomInfo("! >", "!>", "notGreater", {case () => useAt(DerivedAxioms.notGreater)}),
    new DerivedAxiomInfo("< negate", "!<=", "notGreaterEqual", {case () => useAt(DerivedAxioms.notGreaterEqual)}),
    new DerivedAxiomInfo(">= flip", ">=F", "flipGreaterEqual", {case () => useAt(DerivedAxioms.flipGreaterEqual)}),
    new DerivedAxiomInfo("> flip", ">F", "flipGreater", {case () => useAt(DerivedAxioms.flipGreater)}),
    new DerivedAxiomInfo("<", "<", "less", {case () => useAt(DerivedAxioms.less)}),
    new DerivedAxiomInfo(">", ">", "greater", {case () => useAt(DerivedAxioms.greater)}),
    new DerivedAxiomInfo("abs", "abs", "abs", {case () => useAt(DerivedAxioms.absDef)}),
    new DerivedAxiomInfo("min", "min", "min", {case () => useAt(DerivedAxioms.minDef)}),
    new DerivedAxiomInfo("max", "max", "max", {case () => useAt(DerivedAxioms.maxDef)}),
    new DerivedAxiomInfo("*<= up", "*<=", "intervalUpTimes", {case () => useAt(DerivedAxioms.intervalUpTimes)}),
    new DerivedAxiomInfo("1Div<= up", "1/<=", "intervalUp1Divide", {case () => useAt(DerivedAxioms.intervalUp1Divide)}),
    new DerivedAxiomInfo("Div<= up", "/<=", "intervalUpDivide", {case () => useAt(DerivedAxioms.intervalUpDivide)}),
    new DerivedAxiomInfo("<=* down", "<=*", "intervalDownTimes", {case () => useAt(DerivedAxioms.intervalDownTimes)}),
    new DerivedAxiomInfo("<=1Div down", "<=1/", "intervalDown1Divide", {case () => useAt(DerivedAxioms.intervalDown1Divide)}),
    new DerivedAxiomInfo("<=Div down", "<=/", "intervalDownDivide", {case () => useAt(DerivedAxioms.intervalDownDivide)}),
    new DerivedAxiomInfo("! !=", "!!=", "notNotEqual", {case () => useAt(DerivedAxioms.notNotEqual)}),
    new DerivedAxiomInfo("! =", "! =", "notEqual", {case () => useAt(DerivedAxioms.notEqual)}),
    new DerivedAxiomInfo("! <=", "!<=", "notLessEqual", {case () => useAt(DerivedAxioms.notLessEqual)}),
    new DerivedAxiomInfo("* associative", "*A", "timesAssociative", {case () => useAt(DerivedAxioms.timesAssociative)}),
    new DerivedAxiomInfo("* commute", "*C", "timesCommute", {case () => useAt(DerivedAxioms.timesCommutative)}),
    new DerivedAxiomInfo("* inverse", "*i", "timesInverse", {case () => useAt(DerivedAxioms.timesInverse)}),
    new DerivedAxiomInfo("* closed", "*c", "timesClosed", {case () => useAt(DerivedAxioms.timesClosed)}),
    new DerivedAxiomInfo("* identity", "*I", "timesIdentity", {case () => useAt(DerivedAxioms.timesIdentity)}),
    new DerivedAxiomInfo("+ associative", "+A", "plusAssociative", {case () => useAt(DerivedAxioms.plusAssociative)}),
    new DerivedAxiomInfo("+ commute", "+C", "plusCommute", {case () => useAt(DerivedAxioms.plusCommutative)}),
    new DerivedAxiomInfo("+ inverse", "+i", "plusInverse", {case () => useAt(DerivedAxioms.plusInverse)}),
    new DerivedAxiomInfo("+ closed", "+c", "plusClosed", {case () => useAt(DerivedAxioms.plusClosed)}),
    new DerivedAxiomInfo("positivity", "Pos", "positivity", {case () => useAt(DerivedAxioms.positivity)}),
    new DerivedAxiomInfo("distributive", "*+", "distributive", {case () => useAt(DerivedAxioms.distributive)}),
    new DerivedAxiomInfo("[]~><> propagation", "[]~><>", "boxDiamondPropagation", {case () => useAt(DerivedAxioms.boxDiamondPropagation)}),
    new DerivedAxiomInfo("-> self", "-> self", "implySelf", {case () => useAt(DerivedAxioms.implySelf)}),
    //@todo internal only
//    new DerivedAxiomInfo("K1", "K1", "K1", {case () => useAt(DerivedAxioms.K1)}),
//    new DerivedAxiomInfo("K2", "K2", "K2", {case () => useAt(DerivedAxioms.K2)}),
    new DerivedAxiomInfo("PC1", "PC1", "PC1", {case () => useAt(DerivedAxioms.PC1)}),
    new DerivedAxiomInfo("PC2", "PC2", "PC2", {case () => useAt(DerivedAxioms.PC2)}),
    new DerivedAxiomInfo("PC3", "PC3", "PC3", {case () => useAt(DerivedAxioms.PC3)}),
    new DerivedAxiomInfo("PC9", "PC9", "PC9", {case () => useAt(DerivedAxioms.PC9)}),
    new DerivedAxiomInfo("PC10", "PC10", "PC10", {case () => useAt(DerivedAxioms.PC10)}),
    // @internal axioms for unit tests
    new DerivedAxiomInfo("exists dual dummy", "DUMMY", "dummyexistsDualAxiomT", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy", "DUMMY", "dummyallDualAxiom", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy 2", "DUMMY", "dummyallDualAxiom2", {case () => ???}),
    new DerivedAxiomInfo("+id' dummy", "DUMMY", "dummyDplus0", {case () => ???}),
    new DerivedAxiomInfo("+*' reduce dummy", "DUMMY", "dummyDplustimesreduceAxiom", {case () => ???}),
    new DerivedAxiomInfo("+*' expand dummy", "DUMMY", "dummyDplustimesexpandAxiom", {case () => ???}),
    new DerivedAxiomInfo("^' dummy", "DUMMY", "dummyDpowerconsequence", {case () => ???}),

    // Note: Tactic info does not cover all tactics yet.
    // Proof rule position PositionTactics
    new PositionTacticInfo("notL"
      , RuleDisplayInfo("!L", (List("&Gamma;", "!p"),List("&Delta;")), List((List("&Gamma;"),List("p","&Delta;"))))
      , {case () => ProofRuleTactics.notL}),  //@todo
    new PositionTacticInfo("notR"
      , RuleDisplayInfo("!R", (List("&Gamma;"),List("!p","&Delta;")), List((List("&Gamma;","p"),List("&Delta;"))))
      , {case () => ProofRuleTactics.notR}),
    new PositionTacticInfo("andR"
      , RuleDisplayInfo("^R", (List("&Gamma;"),List("p&q","&Delta;")),
        List((List("&Gamma;"),List("p", "&Delta;")),
          (List("&Gamma;"), List("q", "&Delta;"))))
      , {case () => ProofRuleTactics.andR}),  //@todo "\u2227R"
    new PositionTacticInfo("andL"
      , RuleDisplayInfo("^L", (List("&Gamma;", "p&q"),List("&Delta;")), List((List("&Gamma;","p","q"),List("&Delta;"))))
      , {case () => ProofRuleTactics.andL}), //@todo "\u2227L"
    new PositionTacticInfo("orL"
      , RuleDisplayInfo("|L", (List("&Gamma;", "p|q"),List("&Delta;")),
        List((List("&Gamma;", "p"),List("&Delta;")),
          (List("&Gamma;", "q"),List("&Delta;"))))
      , {case () => ProofRuleTactics.orL}), //@todo "\u2228L"
    new PositionTacticInfo("orR"
      , RuleDisplayInfo("|R", (List("&Gamma;"),List("p|q","&Delta;")), List((List("&Gamma;"),List("p","q","&Delta;"))))
      , {case () => ProofRuleTactics.orR}), //@todo "\u2228R"
    new PositionTacticInfo("implyR"
      , RuleDisplayInfo("->R", (List("&Gamma;"),List("p->q", "&Delta;")), List((List("&Gamma;","p"),List("q","&Delta;"))))
      , {case () => ProofRuleTactics.implyR}), //@todo "\u2192L"
    new PositionTacticInfo("implyL"
      , RuleDisplayInfo("->L", (List("&Gamma;","p->q"),List("&Delta;")),
        List((List("&Gamma;","p"),List("&Delta;")),
          (List("&Gamma;"),List("q","&Delta;"))))
      , {case () => ProofRuleTactics.implyL}), //@todo "\u2192R"
    new PositionTacticInfo("equivL"
      , RuleDisplayInfo("<->L", (List("&Gamma;","p<->q"),List("&Delta;")),
        List((List("&Gamma;","p&q"),List("&Delta;")),
          (List("&Gamma;","!p&!q"),List("&Delta;"))
         ))
      , {case () => ProofRuleTactics.equivL}), //@todo "\u2194L"
    new PositionTacticInfo("equivR"
      , RuleDisplayInfo("<->R", (List("&Gamma;"),List("p<->q","&Delta;")),
        List((List("&Gamma;","p","q"),List("&Delta;")),
          (List("&Gamma;","!p","!q"),List("&Delta;"))))
      , {case () => ProofRuleTactics.equivR}), //@todo "\u2194R"
    new TacticInfo("G"
      , "G"
      /* This realy ought to be show as an inference rule, but due to a UI bug we can't support non-input rules just yet
        RuleDisplayInfo("G", (List(""),List("[a]p")),
        List((List(),List("p"))))*/
      , {case () => DLBySubst.G}),

    new PositionTacticInfo("commuteEquivL", "<->CL", {case () => ProofRuleTactics.commuteEquivL}),
    new PositionTacticInfo("commuteEquivR", "<->CR", {case () => ProofRuleTactics.commuteEquivR}),
    new PositionTacticInfo("equivifyR", "-><->", {case () => ProofRuleTactics.equivifyR}),
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
      RuleDisplayInfo("loop",(List("&Gamma;"), List("[a*]j(x)", "&Delta;")),
        List(
          (List("&Gamma;"),List("j(x)", "&Delta;")),
          (List("j(x)"),List("[a]j(x)")),
          (List("j(x)"),List("P"))))
      , List(FormulaArg("j(x)")), {case () => (fml:Formula) => TactixLibrary.loop(fml)}),

  //
    new TacticInfo("TrivialCloser", "TrivialCloser", {case () => ProofRuleTactics.trivialCloser}),
    new TacticInfo("nil", "nil", {case () => Idioms.nil}),

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
    new PositionTacticInfo("diffSolve", "diffSolve",  {case () => ??? /*DifferentialTactics.diffSolve */}, needsTool = true),
    new InputPositionTacticInfo("diffCut", "diffCut", List(FormulaArg("cutFormula")), {case () => (fml:Formula) => DifferentialTactics.diffCut(fml)}, needsTool = true),
    new InputPositionTacticInfo("diffInvariant",
      RuleDisplayInfo("diffInvariant",
        (List("&Gamma;"), List("[x' = f(x)]p", "&Delta;")),
        List((List("&Gamma;"),List("[x' = f(x) & j(x)]"))))
      , List(FormulaArg("f(x)")), {case () => (fml:Formula) => DifferentialTactics.diffInvariant(qeTool, fml)}, needsTool = true),
    new PositionTacticInfo("Dconstify", "Dconst", {case () => DifferentialTactics.Dconstify}),
    new PositionTacticInfo("Dvariable", "Dvar", {case () => DifferentialTactics.Dvariable}),

    // DLBySubst
    new InputPositionTacticInfo("I", "I", List(FormulaArg("invariant")), {case () => (fml:Formula) => DLBySubst.I(fml)})
  ) ensuring(consistentInfo _, "meta-information on AxiomInfo is consistent with actual (derived) axioms etc.")

  private def consistentInfo(list: List[DerivationInfo]): Boolean = {
    //@note to avoid file storage issues on some OSes, lowercase versions of names are expected to be unique.
    val canonicals = list.map(i => i.canonicalName.toLowerCase())
    val codeNames = list.map(i => i.codeName.toLowerCase()).filter(n => n!=needsCodeName)
    list.forall(i => i match {
        case ax: CoreAxiomInfo => Axiom.axioms.contains(ax.canonicalName) ensuring(r=>r, "core axiom correctly marked as CoreAxiomInfo: " + ax.canonicalName)
        case ax: DerivedAxiomInfo => true //@todo can't ask DerivedAxioms.derivedAxiom yet since still initializing, besides that'd be circular
        case _ => true
      }
    ) &
      (canonicals.length==canonicals.distinct.length ensuring(r=>r, "unique canonical names: " + (canonicals diff canonicals.distinct))) &
      (codeNames.length==codeNames.distinct.length ensuring(r=>r, "unique code names / identifiers: " + (codeNames diff codeNames.distinct)))
  }


  /** code name mapped to derivation information */
  private val byCodeName: Map[String, DerivationInfo] =
  /* @todo Decide on a naming convention. Until then, making everything case insensitive */
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc.+((info.codeName.toLowerCase(), info))
    }

  /** canonical name mapped to derivation information */
  private val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc.+((info.canonicalName.toLowerCase, info))
    }

  /** Retrieve meta-information on an inference by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivationInfo = {
    byCanonicalName.getOrElse(axiomName.toLowerCase,
        throw new AxiomNotFoundException(axiomName))
  }

  /** Throw an AssertionError if id does not conform to the rules for code names. */
  def assertValidIdentifier(id:String) = { assert(id.forall{case c => c.isLetterOrDigit})}

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName:String): DerivationInfo = byCodeName.get(codeName.toLowerCase).get
}

object AxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): AxiomInfo =
    DerivationInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom")
  }

  /** Retrieve meta-information on an axiom by the given code name `codeName` */
  def ofCodeName(codeName: String): AxiomInfo =
    DerivationInfo.ofCodeName(codeName) match {
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

/** Meta-information on a derivation step, which is an axiom, derived axiom, proof rule, or tactic. */
sealed trait DerivationInfo {
  /** Canonical name unique across all derivations (axioms or tactics). For axioms this is as declared in the
    * axioms file, for and tactics it is identical to codeName. Can and will contain spaces and special chars. */
  val canonicalName: String
  /** How to display this inference step in a UI */
  val display: DisplayInfo
  /** The unique alphanumeric identifier for this inference step. */
  val codeName: String
  /** Specification of inputs (other than positions) to the derivation, along with names to use when displaying in the UI. */
  val inputs: List[ArgInfo] = Nil
  /** Bellerophon tactic implementing the derivation. For non-input tactics this is simply a BelleExpr. For input tactics
    * it is (curried) function which accepts the inputs and produces a BelleExpr. */
  def belleExpr: Any
  //@todo add formattedName/unicodeName: String
  /** Number of positional arguments to the derivation. Can be 0, 1 or 2. */
  val numPositionArgs: Int = 0
}

/** Meta-Information for an axiom or derived axiom */
trait AxiomInfo extends DerivationInfo {
  /** The valid formula that this axiom represents */
  def formula: Formula
  /** A Provable concluding this axiom */
  def provable: Provable
}

/** Meta-Information for an axiom from the prover core */
case class CoreAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any, override val inputs:List[ArgInfo] = Nil) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  override val formula:Formula = {
    Axiom.axioms.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override lazy val provable:Provable = Axiom.axiom(canonicalName)
  override val numPositionArgs = 1
}

/** Information for a derived axiom proved from the core */
case class DerivedAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  override lazy val formula: Formula =
    DerivedAxioms.derivedAxiom(canonicalName).conclusion.succ.head
//  {
//    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
//      case Some(fml) => fml._1
//      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
//    }
//  }
  override lazy val provable:Provable = DerivedAxioms.derivedAxiom(canonicalName)
  override val numPositionArgs = 1
}

object DerivedAxiomInfo {
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def locate(axiomName: String): Option[DerivedAxiomInfo] =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on an axiom by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivedAxiomInfo =
    DerivationInfo(axiomName) match {
      case info: DerivedAxiomInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived axiom")
    }

  //@todo val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo])
}

// tactics

/** Meta-information on a tactic performing a proof step (or more) */
class TacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false) extends DerivationInfo {
  DerivationInfo.assertValidIdentifier(codeName)
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