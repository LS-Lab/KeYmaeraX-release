package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.RunnableInfo.AxiomNotFoundException
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
object RunnableInfo {
  case class AxiomNotFoundException(axiomName: String) extends Exception

  val allInfo: List[RunnableInfo] = List(
    new CoreAxiomInfo("chain rule", "o'", ""),
    new CoreAxiomInfo("V vacuous", "V", ""),
    new CoreAxiomInfo("K modal modus ponens", "K", ""),
    new CoreAxiomInfo("I induction", "I", ""),
    new CoreAxiomInfo("all instantiate", "alli", ""),
    new CoreAxiomInfo("all eliminate", "alle", ""),
    new CoreAxiomInfo("exists eliminate", "existse", ""),
    new CoreAxiomInfo("vacuous all quantifier", "Vall", ""),
    new CoreAxiomInfo("vacuous exists quantifier", "Vexists", ""),
    new CoreAxiomInfo("all dual", "alld", ""),
    new CoreAxiomInfo("exists dual", "existsd", ""),
    new CoreAxiomInfo("const congruence", "CCE", ""),
    new CoreAxiomInfo("const formula congruence", "CCQ", ""),
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> dual", "<.>", ""),
    new CoreAxiomInfo("[] dual", "[.]", ""),
    new CoreAxiomInfo("[:=] assign", "[:=]", ""),
    new CoreAxiomInfo("<:=> assign", "<:=>", ""),
    new CoreAxiomInfo("[':=] differential assign", "[':=]", ""),
    new CoreAxiomInfo("<':=> differential assign", "<':=>", ""),
    new CoreAxiomInfo("[:=] assign equational", "[:=]=", ""),
    new CoreAxiomInfo("<:=> assign equational", "<:=>=", ""),
    new CoreAxiomInfo("[:=] assign update", "[:=]", ""),
    new CoreAxiomInfo("<:=> assign update", "<:=>", ""),
    new CoreAxiomInfo("[:*] assign nondet", "[:*]", ""),
    new CoreAxiomInfo("<:*> assign nondet", "<:*>", ""),
    new CoreAxiomInfo("[?] test", "[?]", ""),
    new CoreAxiomInfo("<?> test", "<?>", ""),
    new CoreAxiomInfo("[++] choice", "[++]", ""),
    new CoreAxiomInfo("<++> choice", "<++>", ""),
    new CoreAxiomInfo("[;] compose", "[;]", ""),
    new CoreAxiomInfo("<;> compose", "<;>", ""),
    new CoreAxiomInfo("[*] iterate", "[*]", ""),
    new CoreAxiomInfo("<*> iterate", "<*>", ""),

    new CoreAxiomInfo("DW", "DW", ""),
    new CoreAxiomInfo("DW differential weakening", "DW", ""),
    new CoreAxiomInfo("DC differential cut", "DC", ""),
    new CoreAxiomInfo("DE differential effect system", "DE", ""),
    new CoreAxiomInfo("DE differential effect", "DE", ""),
    new CoreAxiomInfo("DE differential effect (system)", "DE", ""),
    new CoreAxiomInfo("DI differential invariant", "DI", ""),
    new CoreAxiomInfo("DG differential ghost", "DG", ""),
    new CoreAxiomInfo("DG differential Lipschitz ghost system", "DG", ""),
    new CoreAxiomInfo("DG differential pre-ghost", "DG", ""),
    new CoreAxiomInfo("DG++ System", "DG++", ""),
    new CoreAxiomInfo("DG++", "DG++", ""),
    new CoreAxiomInfo(", commute", ",", ""),
    new CoreAxiomInfo("DS differential equation solution", "DS", ""),
    new CoreAxiomInfo("Dsol& differential equation solution", "DS&",
      ""),
    new CoreAxiomInfo("Dsol differential equation solution", "DS", ""),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", ""),
    new CoreAxiomInfo("DX differential skip", "DX", ""),
    new CoreAxiomInfo("DX diamond differential skip", "DX", ""),
    // Derivatives
    new CoreAxiomInfo("&' derive and", "&'", ""),
    new CoreAxiomInfo("|' derive or", "|'", ""),
    new CoreAxiomInfo("->' derive imply", "->'", ""),
    new CoreAxiomInfo("forall' derive forall", "forall'", ""),
    new CoreAxiomInfo("exists' derive exists", "exists'", ""),
    new CoreAxiomInfo("c()' derive constant fn", "c()'", ""),
    new CoreAxiomInfo("=' derive =", "='", ""),
    new CoreAxiomInfo(">=' derive >=", ">='", ""),
    new CoreAxiomInfo(">' derive >", ">'", ""),
    new CoreAxiomInfo("<=' derive <=", "<='", ""),
    new CoreAxiomInfo("<' derive <", "<'", ""),
    new CoreAxiomInfo("!=' derive !=", "!='", ""),
    new CoreAxiomInfo("-' derive neg", "-'", ""),
    new CoreAxiomInfo("+' derive sum", "+'", ""),
    new CoreAxiomInfo("-' derive minus", "-'", ""),
    new CoreAxiomInfo("*' derive product", "*'", ""),
    new CoreAxiomInfo("/' derive quotient", "/'", ""),
    new CoreAxiomInfo("^' derive power", "^'", ""),
    new CoreAxiomInfo("x' derive variable", "x'", ""),
    new CoreAxiomInfo("x' derive var", "x'", ""),

    // derived axioms
    new DerivedAxiomInfo("' linear", "l'", ""),
    new DerivedAxiomInfo("' linear right", "l'", ""),
    new DerivedAxiomInfo("!& deMorgan", "!&", ""),
    new DerivedAxiomInfo("!| deMorgan", "!|", ""),
    new DerivedAxiomInfo("!-> deMorgan", "!->", ""),
    new DerivedAxiomInfo("!<-> deMorgan", "!<->", ""),
    new DerivedAxiomInfo("!all", "!all", ""),
    new DerivedAxiomInfo("!exists", "!exists", ""),
    new DerivedAxiomInfo("![]", "![]", ""),
    new DerivedAxiomInfo("!<>", "!<>", ""),
    new DerivedAxiomInfo("[] split", "[]&", ""),
    new DerivedAxiomInfo("<> split", "<>|", ""),
    new DerivedAxiomInfo("[] split left", "[]&<-", ""),
    new DerivedAxiomInfo("[] split right", "[]&->", ""),
    new DerivedAxiomInfo("<*> approx", "<*> approx", ""),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", ""),
    new DerivedAxiomInfo("<'> stuck", "<'> stuck", ""),
    new DerivedAxiomInfo("[] post weaken", "[]PW", ""),
    new DerivedAxiomInfo("+<= up", "+<=", ""),
    new DerivedAxiomInfo("-<= up", "-<=", ""),
    new DerivedAxiomInfo("<=+ down", "<=+", ""),
    new DerivedAxiomInfo("<=- down", "<=-", ""),
    new DerivedAxiomInfo("<-> reflexive", "<->R", ""),
    new DerivedAxiomInfo("-> distributes over &", "->&", ""),
    new DerivedAxiomInfo("-> distributes over <->", "-><->", ""),
    new DerivedAxiomInfo("-> weaken", "->W", ""),
    new DerivedAxiomInfo("!! double negation", "!!", ""),
    new DerivedAxiomInfo(":= assign dual", ":=D", ""),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", ""),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", ""),
    new DerivedAxiomInfo("[*] approx", "[*] approx", ""),
    new DerivedAxiomInfo("exists generalize", "existsG", ""),
    new DerivedAxiomInfo("all substitute", "allS", ""),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", ""),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", ""),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", "DCCR", ""), //@todo shortname
    new DerivedAxiomInfo("& commute", "&C", ""),
    new DerivedAxiomInfo("& associative", "&A", ""),
    new DerivedAxiomInfo("-> expand", "->E", ""),
    new DerivedAxiomInfo("-> tautology", "->taut", ""),
    new DerivedAxiomInfo("\\forall->\\exists", "all->exists", ""),
    new DerivedAxiomInfo("->true", "->T", ""),
    new DerivedAxiomInfo("true->", "T->", ""),
    new DerivedAxiomInfo("&true", "&T", ""),
    new DerivedAxiomInfo("true&", "T&", ""),
    new DerivedAxiomInfo("0*", "0*", ""),
    new DerivedAxiomInfo("0+", "0+", ""),
    new DerivedAxiomInfo("= reflexive", "=R", ""),
    new DerivedAxiomInfo("* commute", "*C", ""),
    new DerivedAxiomInfo("= commute", "=C", ""),
    new DerivedAxiomInfo("<=", "<=", ""),
    new DerivedAxiomInfo("= negate", "!!=", ""),
    new DerivedAxiomInfo("!= negate", "! =", ""),
    new DerivedAxiomInfo("! <", "!<", ""),
    new DerivedAxiomInfo("! >", "!>", ""),
    new DerivedAxiomInfo("< negate", "!<=", ""),
    new DerivedAxiomInfo(">= flip", ">=F", ""),
    new DerivedAxiomInfo("> flip", ">F", ""),
    new DerivedAxiomInfo("<", "<", ""),
    new DerivedAxiomInfo(">", ">", ""),
    new DerivedAxiomInfo("abs", "abs", ""),
    new DerivedAxiomInfo("min", "min", ""),
    new DerivedAxiomInfo("max", "max", ""),
    new DerivedAxiomInfo("*<= up", "*<=", ""),
    new DerivedAxiomInfo("1Div<= up", "1/<=", ""),
    new DerivedAxiomInfo("Div<= up", "/<=", ""),
    new DerivedAxiomInfo("<=* down", "<=*", ""),
    new DerivedAxiomInfo("<=1Div down", "<=1/", ""),
    new DerivedAxiomInfo("<=Div down", "<=/", ""),
    new DerivedAxiomInfo("! !=", "!!=", ""),
    new DerivedAxiomInfo("! =", "! =", ""),
    new DerivedAxiomInfo("! <=", "!<=", ""),
    new DerivedAxiomInfo("* associative", "*A", ""),
    new DerivedAxiomInfo("* commutative", "*C", ""),
    new DerivedAxiomInfo("* inverse", "*i", ""),
    new DerivedAxiomInfo("* closed", "*c", ""),
    new DerivedAxiomInfo("* identity", "*I", ""),
    new DerivedAxiomInfo("+ associative", "+A", ""),
    new DerivedAxiomInfo("+ commutative", "+C", ""),
    new DerivedAxiomInfo("+ inverse", "+i", ""),
    new DerivedAxiomInfo("+ closed", "+c", ""),
    new DerivedAxiomInfo("positivity", "Pos", ""),
    new DerivedAxiomInfo("distributive", "*+", ""),
    new DerivedAxiomInfo("all distribute", "Dall", ""),
    new DerivedAxiomInfo("[]~><> propagation", "[]~><>", ""),
    new DerivedAxiomInfo("K1", "K1", ""),
    new DerivedAxiomInfo("K2", "K2", ""),
    new DerivedAxiomInfo("P1", "P1", ""),
    new DerivedAxiomInfo("P2", "P2", ""),
    new DerivedAxiomInfo("P3", "P3", ""),
    new DerivedAxiomInfo("P9", "P9", ""),
    new DerivedAxiomInfo("P10", "P10", ""),
    // tactics for unit tests
    new DerivedAxiomInfo("exists dual dummy", "DUMMY", ""),
    new DerivedAxiomInfo("all dual dummy", "DUMMY", ""),
    new DerivedAxiomInfo("all dual dummy 2", "DUMMY", ""),
    new DerivedAxiomInfo("+id' dummy", "DUMMY", ""),
    new DerivedAxiomInfo("+*' reduce dummy", "DUMMY", ""),
    new DerivedAxiomInfo("+*' expand dummy", "DUMMY", ""),
    new DerivedAxiomInfo("^' dummy", "DUMMY", ""))

  val byCodeName: Map[String, RunnableInfo] =
    allInfo.foldLeft(HashMap.empty[String,RunnableInfo]){case (acc, info) =>
        acc.+((info.codeName, info))
    }

  val byCanonicalName: Map[String, RunnableInfo] =
    allInfo.foldLeft(HashMap.empty[String,RunnableInfo]){case (acc, info) =>
      acc.+((info.canonicalName, info))
    }

  def apply(axiomName: String): RunnableInfo = {
    byCanonicalName.get(axiomName) match {
      case Some(info) => info
      case None => throw new AxiomNotFoundException(axiomName)
    }
  }
}

object AxiomInfo {
  def apply(axiomName: String): AxiomInfo =
    RunnableInfo(axiomName) match {
      case info:AxiomInfo => info
      case info => throw new Exception("Runnable \"" + info.canonicalName + "\" is not an axiom")
  }
}

/** The short name for an axiom is a string intended for use in the UI where space is a concern (e.g. when
  * displaying tree-style proofs). Since the goal is to be as short as possible, they are not required to be
  * unique, but should still be as suggestive as possible of what the axiom does.
  * @note This can't be a case class because the auto-generated [[apply]] method conflicts with the one from
  *       the companion object.
  * */

sealed trait InputSort {}
case class FormulaSort () extends InputSort

sealed trait RunnableInfo {
  val canonicalName: String
  val displayName: String
  val codeName: String
  val isPositional: Boolean = false
}

trait AxiomInfo extends RunnableInfo {
  def formula: Formula
}

case class CoreAxiomInfo(override val canonicalName:String, override val displayName: String, override val codeName: String) extends AxiomInfo {
  override def formula:Formula = {
    Axiom.axioms.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override val isPositional = true
}

case class DerivedAxiomInfo(override val canonicalName:String, override val displayName: String, override val codeName: String) extends AxiomInfo {
  override def formula: Formula = {
    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
      case Some(fml) => fml._1
      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
    }
  }
  override val isPositional = true
}

class TacticInfo(override val canonicalName:String, override val displayName: String, override val codeName:String) extends RunnableInfo {
  val inputs: List[InputSort] = Nil
}

case class InputTacticInfo(override val canonicalName:String, override val displayName: String, override val codeName: String, override val inputs:List[InputSort])
  extends TacticInfo(canonicalName, displayName, codeName)