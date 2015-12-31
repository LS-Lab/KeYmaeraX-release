package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.core.{Axiom, Formula}

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
object DerivationInfo {
  case class AxiomNotFoundException(axiomName: String) extends Exception

  private val needsCodeName = "THISAXIOMSTILLNEEDSACODENAME"

  val allInfo: List[DerivationInfo] = List(
    new CoreAxiomInfo("chain rule", "o'", "Dcompose"),
    new CoreAxiomInfo("V vacuous", "V", "V"),
    new CoreAxiomInfo("K modal modus ponens", "K", "K"),
    new CoreAxiomInfo("I induction", "I", "I"),
    new CoreAxiomInfo("all instantiate", "alli", needsCodeName),
    new CoreAxiomInfo("vacuous all quantifier", "Vall", "vacuousAll"),
    new CoreAxiomInfo("vacuous exists quantifier", "Vexists", "vacuousExists"),
    new CoreAxiomInfo("const congruence", "CCE", needsCodeName),
    new CoreAxiomInfo("const formula congruence", "CCQ", needsCodeName),
    new CoreAxiomInfo("DX differential skip", "DX", "Dskipd"),
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> dual", "<.>", needsCodeName),
    new CoreAxiomInfo("[] dual", "[.]", needsCodeName),
    new CoreAxiomInfo("[:=] assign", "[:=]", "assignb"),
    new CoreAxiomInfo("<:=> assign", "<:=>", "assignd"),
    new CoreAxiomInfo("[':=] differential assign", "[':=]", "Dassignb"),
    new CoreAxiomInfo("<':=> differential assign", "<':=>", "Dassgnd"),
    new CoreAxiomInfo("[:=] assign equational", "[:=]=", "assignb"),
    new CoreAxiomInfo("<:=> assign equational", "<:=>=", "assignd"),
    new CoreAxiomInfo("[:=] assign update", "[:=]", "assignb"),
    new CoreAxiomInfo("<:=> assign update", "<:=>", "assignd"),
    new CoreAxiomInfo("[:*] assign nondet", "[:*]", "randomb"),
    new CoreAxiomInfo("<:*> assign nondet", "<:*>", "randomd"),
    new CoreAxiomInfo("[?] test", "[?]", "testb"),
    new CoreAxiomInfo("<?> test", "<?>", "testd"),
    new CoreAxiomInfo("[++] choice", "[++]", "choiceb"),
    new CoreAxiomInfo("<++> choice", "<++>", "choiced"),
    new CoreAxiomInfo("[;] compose", "[;]", "composeb"),
    new CoreAxiomInfo("<;> compose", "<;>", "composed"),
    new CoreAxiomInfo("[*] iterate", "[*]", "iterateb"),
    new CoreAxiomInfo("<*> iterate", "<*>", "iterated"),
    new CoreAxiomInfo("all dual", "alld", needsCodeName),
  
    new CoreAxiomInfo("DW", "DW", "DW"),
    new CoreAxiomInfo("DC differential cut", "DC", "DC"),
    new CoreAxiomInfo("DE differential effect system", "DE", "DE"),
    new CoreAxiomInfo("DE differential effect", "DE", "DE"),
    new CoreAxiomInfo("DE differential effect (system)", "DE", "DE"),
    new CoreAxiomInfo("DI differential invariant", "DI", "DI"),
    new CoreAxiomInfo("DG differential ghost", "DG", "DG"),
    new CoreAxiomInfo("DG differential Lipschitz ghost system", "DG", "DG"),
    new CoreAxiomInfo("DG++ System", "DG++", needsCodeName),
    new CoreAxiomInfo("DG++", "DG++", needsCodeName),
    new CoreAxiomInfo(", commute", ",", needsCodeName),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", "DS"),
    // Derivatives
    new CoreAxiomInfo("&' derive and", "&'", "Dand"),
    new CoreAxiomInfo("|' derive or", "|'", "Dor"),
    new CoreAxiomInfo("->' derive imply", "->'", "Dimply"),
    new CoreAxiomInfo("forall' derive forall", "forall'", "Dforall"),
    new CoreAxiomInfo("exists' derive exists", "exists'", "Dexists"),
    new CoreAxiomInfo("c()' derive constant fn", "c()'", "Dconst"),
    new CoreAxiomInfo("=' derive =", "='", "Dequal"),
    new CoreAxiomInfo(">=' derive >=", ">='", "Dgreaterequal"),
    new CoreAxiomInfo(">' derive >", ">'", "Dgreater"),
    new CoreAxiomInfo("<=' derive <=", "<='", "Dlessequal"),
    new CoreAxiomInfo("<' derive <", "<'", "Dless"),
    new CoreAxiomInfo("!=' derive !=", "!='", "Dnotequal"),
    new CoreAxiomInfo("-' derive neg", "-'", "Dneg"),
    new CoreAxiomInfo("+' derive sum", "+'", "Dplus"),
    new CoreAxiomInfo("-' derive minus", "-'", "Dminus"),
    new CoreAxiomInfo("*' derive product", "*'", "Dtimes"),
    new CoreAxiomInfo("/' derive quotient", "/'", "Dquotient"),
    new CoreAxiomInfo("^' derive power", "^'", "Dpower"),
    new CoreAxiomInfo("x' derive variable", "x'", "Dvariable"),
    new CoreAxiomInfo("x' derive var", "x'", "Dvariable"),

    // derived axioms
    new DerivedAxiomInfo("DW differential weakening", "DW", "DWeakening"),
    new DerivedAxiomInfo("DS differential equation solution", "DS", "DSnodomain"),
    new DerivedAxiomInfo("Dsol& differential equation solution", "DS&", "DSddomain"),
    new DerivedAxiomInfo("Dsol differential equation solution", "DS", "DSdnodomain"),
    new DerivedAxiomInfo("DG differential pre-ghost", "DG", "DGpreghost"),
    new DerivedAxiomInfo("DX diamond differential skip", "DX", "Dskipd"),
    new DerivedAxiomInfo("all eliminate", "alle", "allEliminate"),
    new DerivedAxiomInfo("exists eliminate", "existse", "existsEliminate"),
    new DerivedAxiomInfo("exists dual", "existsd", "existsDualAxiom"),
    new DerivedAxiomInfo("' linear", "l'", "Dlinear"),
    new DerivedAxiomInfo("' linear right", "l'", "DlinearRight"),
    new DerivedAxiomInfo("!& deMorgan", "!&", "notAnd"),
    new DerivedAxiomInfo("!| deMorgan", "!|", "notOr"),
    new DerivedAxiomInfo("!-> deMorgan", "!->", "notImply"),
    new DerivedAxiomInfo("!<-> deMorgan", "!<->", "notEquiv"),
    new DerivedAxiomInfo("!all", "!all", "notAll"),
    new DerivedAxiomInfo("!exists", "!exists", "notExists"),
    new DerivedAxiomInfo("![]", "![]", "notBox"),
    new DerivedAxiomInfo("!<>", "!<>", "notDiamond"),
    new DerivedAxiomInfo("[] split", "[]&", "boxSplit"),
    new DerivedAxiomInfo("<> split", "<>|", "diamondSplit"),
    new DerivedAxiomInfo("[] split left", "[]&<-", "boxSplitLeft"),
    new DerivedAxiomInfo("[] split right", "[]&->", "boxSplitRight"),
    new DerivedAxiomInfo("<*> approx", "<*> approx", "loopApproxd"),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", "loopStuck"),
    new DerivedAxiomInfo("<'> stuck", "<'> stuck", "odeStuck"),
    new DerivedAxiomInfo("[] post weaken", "[]PW", "postconditionWeaken"),
    new DerivedAxiomInfo("+<= up", "+<=", "intervalUpPlus"),
    new DerivedAxiomInfo("-<= up", "-<=", "intervalUpMinus"),
    new DerivedAxiomInfo("<=+ down", "<=+", "intervalDownPLus"),
    new DerivedAxiomInfo("<=- down", "<=-", "intervalDownMinus"),
    new DerivedAxiomInfo("<-> reflexive", "<->R", "equivReflexive"),
    new DerivedAxiomInfo("-> distributes over &", "->&", "implyDistAnd"),
    new DerivedAxiomInfo("-> distributes over <->", "-><->", "implyDistEquiv"),
    new DerivedAxiomInfo("-> weaken", "->W", "implWeaken"),
    new DerivedAxiomInfo("!! double negation", "!!", "doubleNegation"),
    new DerivedAxiomInfo(":= assign dual", ":=D", "assignDual"),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", "vacuousAssignb"),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", "vacuousAssignd"),
    new DerivedAxiomInfo("[*] approx", "[*] approx", "loopApproxb"),
    new DerivedAxiomInfo("exists generalize", "existsG", "existsGeneralize"),
    new DerivedAxiomInfo("all substitute", "allS", "allSubstitute"),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", "vacuousBoxAssignNondet"),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", "vacuousDiamondAssignNondet"),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", "DCCR", "domainCommute"), //@todo shortname
    new DerivedAxiomInfo("& commute", "&C", "andCommute"),
    new DerivedAxiomInfo("& associative", "&A", "andAssoc"),
    new DerivedAxiomInfo("-> expand", "->E", "implyExpand"),
    new DerivedAxiomInfo("-> tautology", "->taut", "implyTautology"),
    new DerivedAxiomInfo("\\forall->\\exists", "all->exists", "forallThenExists"),
    new DerivedAxiomInfo("->true", "->T", "impliesTrue"),
    new DerivedAxiomInfo("true->", "T->", "trueImplies"),
    new DerivedAxiomInfo("&true", "&T", "andTrue"),
    new DerivedAxiomInfo("true&", "T&", "trueAnd"),
    new DerivedAxiomInfo("0*", "0*", "zeroTimes"),
    new DerivedAxiomInfo("0+", "0+", "zeroPlus"),
    new DerivedAxiomInfo("= reflexive", "=R", "equalReflexive"),
    new DerivedAxiomInfo("* commute", "*C", "timesCommute"),
    new DerivedAxiomInfo("= commute", "=C", "equalCommute"),
    new DerivedAxiomInfo("<=", "<=", "lessEqual"),
    new DerivedAxiomInfo("= negate", "!!=", "notNotEqual"),
    new DerivedAxiomInfo("!= negate", "! =", "notEqual"),
    new DerivedAxiomInfo("! <", "!<", "notLess"),
    new DerivedAxiomInfo("! >", "!>", "notGreater"),
    new DerivedAxiomInfo("< negate", "!<=", "notGreaterEqual"),
    new DerivedAxiomInfo(">= flip", ">=F", "flipGreaterEqual"),
    new DerivedAxiomInfo("> flip", ">F", "flipGreater"),
    new DerivedAxiomInfo("<", "<", "less"),
    new DerivedAxiomInfo(">", ">", "greater"),
    new DerivedAxiomInfo("abs", "abs", "abs"),
    new DerivedAxiomInfo("min", "min", "min"),
    new DerivedAxiomInfo("max", "max", "max"),
    new DerivedAxiomInfo("*<= up", "*<=", "intervalUpTimes"),
    new DerivedAxiomInfo("1Div<= up", "1/<=", "intervalUp1Divide"),
    new DerivedAxiomInfo("Div<= up", "/<=", "intervalUpDivide"),
    new DerivedAxiomInfo("<=* down", "<=*", "intervalDownTimes"),
    new DerivedAxiomInfo("<=1Div down", "<=1/", "intervalDown1Divide"),
    new DerivedAxiomInfo("<=Div down", "<=/", "intervalDownDivide"),
    new DerivedAxiomInfo("! !=", "!!=", "notNotEqual"),
    new DerivedAxiomInfo("! =", "! =", "notEqual"),
    new DerivedAxiomInfo("! <=", "!<=", "notLessEqual"),
    new DerivedAxiomInfo("* associative", "*A", "timesAssociative"),
    new DerivedAxiomInfo("* commutative", "*C", "timesCommutative"),
    new DerivedAxiomInfo("* inverse", "*i", "timesInverse"),
    new DerivedAxiomInfo("* closed", "*c", "timesClosed"),
    new DerivedAxiomInfo("* identity", "*I", "timesIdentity"),
    new DerivedAxiomInfo("+ associative", "+A", "plusAssociative"),
    new DerivedAxiomInfo("+ commutative", "+C", "plusCommutative"),
    new DerivedAxiomInfo("+ inverse", "+i", "plusInverse"),
    new DerivedAxiomInfo("+ closed", "+c", "plusClosed"),
    new DerivedAxiomInfo("positivity", "Pos", "positivity"),
    new DerivedAxiomInfo("distributive", "*+", "distributive"),
    new DerivedAxiomInfo("all distribute", "Dall", "allDistribute"),
    new DerivedAxiomInfo("[]~><> propagation", "[]~><>", "boxDiamondPropagation"),
    new DerivedAxiomInfo("K1", "K1", "K1"),
    new DerivedAxiomInfo("K2", "K2", "K2"),
    new DerivedAxiomInfo("P1", "P1", "P1"),
    new DerivedAxiomInfo("P2", "P2", "P2"),
    new DerivedAxiomInfo("P3", "P3", "P3"),
    new DerivedAxiomInfo("P9", "P9", "P9"),
    new DerivedAxiomInfo("P10", "P10", "P10"),
    // axioms for unit tests
    new DerivedAxiomInfo("exists dual dummy", "DUMMY", "dummyexistsDualAxiom"),
    new DerivedAxiomInfo("all dual dummy", "DUMMY", "dummyallDualAxiom"),
    new DerivedAxiomInfo("all dual dummy 2", "DUMMY", "dummyallDualAxiom2"),
    new DerivedAxiomInfo("+id' dummy", "DUMMY", "dummyDplus0"),
    new DerivedAxiomInfo("+*' reduce dummy", "DUMMY", "dummyDplustimesreduceAxiom"),
    new DerivedAxiomInfo("+*' expand dummy", "DUMMY", "dummyDplustimesexpandAxiom"),
    new DerivedAxiomInfo("^' dummy", "DUMMY", "dummyDpowerconsequence"),

    // Note: Tactic info does not cover all tactics yet.
    // Proof rule position PositionTactics
    new PositionTacticInfo("notL", "!L"),
    new PositionTacticInfo("notR", "!R"),
    new PositionTacticInfo("andR", "^R"),
    new PositionTacticInfo("andL", "^L"),
    new PositionTacticInfo("orL", "|L"),
    new PositionTacticInfo("orR", "|R"),
    new PositionTacticInfo("implyL", "->L"),
    new PositionTacticInfo("implyR", "->R"),
    new PositionTacticInfo("equivL", "<->L"),
    new PositionTacticInfo("equivR", "<->R"),
    new PositionTacticInfo("commuteEquivL", "<->CL"),
    new PositionTacticInfo("commuteEquivR", "<->CR"),
    new PositionTacticInfo("equivifyR", "<->R"),
    new PositionTacticInfo("hideL", "hide"),
    new PositionTacticInfo("hideR", "hide"),
    new PositionTacticInfo("coHideL", "hide"),
    new PositionTacticInfo("coHideR", "hide"),
    new PositionTacticInfo("closeFalse", "close"),
    new PositionTacticInfo("closeTrue", "close"),
    new PositionTacticInfo("skolemizeL", "skolem"),
    new PositionTacticInfo("skolemizeR", "skolem"),
    new PositionTacticInfo("skolemize", "skolem"),
    new PositionTacticInfo("coHide", "hide"),
    new PositionTacticInfo("hide", "hide"),

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "hide"),
    new TwoPositionTacticInfo("exchangeL", "X"),
    new TwoPositionTacticInfo("exchangeR", "X"),
    new TwoPositionTacticInfo("close", "close"),

    // Proof rule input tactics
    new InputTacticInfo("cut", "cut", List(FormulaSort())),
    // Proof rule input position tactics
    new InputPositionTacticInfo("cutL", "cut", List(FormulaSort())),
    new InputPositionTacticInfo("cutR", "cut", List(FormulaSort())),
    new InputPositionTacticInfo("cutLR", "cut", List(FormulaSort())),

    // TactixLibrary tactics
    new PositionTacticInfo("step", "step"),
    new PositionTacticInfo("normalize", "normalize"),
    new PositionTacticInfo("prop", "prop"),
    // Technically in InputPositionTactic(Generator[Formula), but the generator is optional
    new PositionTacticInfo("master", "master"),
    new TacticInfo("QE", "QE", needsTool = true),

    // Differential tactics
    new PositionTacticInfo("diffInd", "diffInd", needsTool = true),
    new InputPositionTacticInfo("diffCut", "diffCut", List(FormulaSort()), needsTool = true),
    new InputPositionTacticInfo("diffInvariant", "diffInv", List(FormulaSort()), needsTool = true),
    new PositionTacticInfo("Dconstify", "Dconst"),
    new PositionTacticInfo("Dvariable", "Dvar"),

    // DLBySubst
    new InputPositionTacticInfo("I", "I", List(FormulaSort()))
  )

  val byCodeName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc.+((info.codeName, info))
    }

  val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc.+((info.canonicalName, info))
    }

  def apply(axiomName: String): DerivationInfo = {
    byCanonicalName.get(axiomName) match {
      case Some(info) => info
      case None => throw new AxiomNotFoundException(axiomName)
    }
  }
}

object AxiomInfo {
  def apply(axiomName: String): AxiomInfo =
    DerivationInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Runnable \"" + info.canonicalName + "\" is not an axiom")
  }
}

sealed trait InputSort {}
case class FormulaSort () extends InputSort

sealed trait DerivationInfo {
  val canonicalName: String
  val displayName: String
  val codeName: String
  val numPositionArgs: Int = 0
}

trait AxiomInfo extends DerivationInfo {
  def formula: Formula
}

case class CoreAxiomInfo(override val canonicalName:String, override val displayName: String, override val codeName: String) extends AxiomInfo {
  override def formula:Formula = {
    Axiom.axioms.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override val numPositionArgs = 1
}

case class DerivedAxiomInfo(override val canonicalName:String, override val displayName: String, override val codeName: String) extends AxiomInfo {
  override def formula: Formula = {
    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
      case Some(fml) => fml._1
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override val numPositionArgs = 1
}

class TacticInfo(override val codeName: String, override val displayName: String, needsTool: Boolean = false) extends DerivationInfo {
  val inputs: List[InputSort] = Nil
  val canonicalName = codeName
}

case class PositionTacticInfo(override val codeName: String, override val displayName: String, needsTool: Boolean = false)
  extends TacticInfo(codeName, displayName, needsTool) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(override val codeName: String, override val displayName: String, needsTool: Boolean = false)
  extends TacticInfo(codeName, displayName, needsTool) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(override val codeName: String, override val displayName: String, override val inputs:List[InputSort], needsTool: Boolean = false)
  extends TacticInfo(codeName, displayName, needsTool)

case class InputPositionTacticInfo(override val codeName: String, override val displayName: String, override val inputs:List[InputSort], needsTool: Boolean = false)
  extends TacticInfo(codeName, displayName, needsTool) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(override val codeName: String, override val displayName: String, override val inputs:List[InputSort], needsTool: Boolean = false)
  extends TacticInfo(codeName, displayName, needsTool) {
  override val numPositionArgs = 2
}