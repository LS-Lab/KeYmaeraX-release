/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo.AxiomNotFoundException
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative.ArithmeticSpeculativeSimplification
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.HashMap
import scala.language.implicitConversions
import scala.reflect.runtime.universe.TypeTag

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
  def name: String
  def asciiName: String
}
case class SimpleDisplayInfo(override val name: String, override val asciiName: String) extends DisplayInfo
case class RuleDisplayInfo(names: SimpleDisplayInfo, conclusion: SequentDisplay, premises:List[SequentDisplay]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class SequentDisplay(ante: List[String], succ: List[String], isClosed: Boolean = false)
case class AxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}
case class InputAxiomDisplayInfo(names: SimpleDisplayInfo, displayFormula: String, input: List[ArgInfo]) extends DisplayInfo {
  override def name = names.name
  override def asciiName = names.asciiName
}

/** Typed functions to circumvent type erasure of arguments and return types. */
abstract class TypedFunc[-A: TypeTag, +R: TypeTag] extends (A => R) {
  val retType: TypeTag[_] = scala.reflect.runtime.universe.typeTag[R]
  val argType: TypeTag[_] = scala.reflect.runtime.universe.typeTag[A]
}
/** Creates TypedFunc implicitly, e.g., by ((x: String) => x.length): TypedFunc[String, Int]  */
object TypedFunc {
  implicit def apply[A: TypeTag, R: TypeTag](f: A => R): TypedFunc[A, R] = f match {
    case tf: TypedFunc[A, R]  => tf
    case _ => new TypedFunc[A, R] { final def apply(arg: A): R = f(arg) }
  }
}

/**
  * Central list of all derivation steps (axioms, derived axioms, proof rules, tactics)
  * with meta information of relevant names and display names and visualizations for the user interface.
  */
object DerivationInfo {
  implicit def displayInfo(name: String): SimpleDisplayInfo = {SimpleDisplayInfo(name, name)}
  implicit def displayInfo(pair: (String, String)): SimpleDisplayInfo = SimpleDisplayInfo(pair._1, pair._2)
  implicit def sequentDisplay(succAcc:(List[String], List[String])): SequentDisplay = {
    SequentDisplay(succAcc._1, succAcc._2)
  }
  implicit def sequentDisplay(succAccClosed:(List[String], List[String], Boolean)): SequentDisplay = {
    SequentDisplay(succAccClosed._1, succAccClosed._2, succAccClosed._3)
  }

  case class AxiomNotFoundException(axiomName: String) extends ProverException("Axiom with said name not found: " + axiomName)

  //@todo
  private val needsCodeName = "TODOTHISAXIOMSTILLNEEDSACODENAME"

  private def useAt(l:Lemma):DependentPositionTactic = HilbertCalculus.useAt(l)
  private val posnil = TacticFactory.anon((pos,seq) => TactixLibrary.nil)

  private def convert(rules: Map[String,ProvableSig]): List[DerivationInfo] =
  //@todo display info is rather impoverished
    rules.keys.map(name => AxiomaticRuleInfo(name, SimpleDisplayInfo(name, name), canonicalize(name))).toList
  private def canonicalize(name: String): String = name.filter(c => c.isLetterOrDigit)
  /**
    * Central registry for axiom, derived axiom, proof rule, and tactic meta-information.
    * Transferred into subsequent maps etc for efficiency reasons.
    */
  private [btactics] val allInfo: List[DerivationInfo] = convert(ProvableSig.rules) ++ List(
    // [a] modalities and <a> modalities
    new CoreAxiomInfo("<> diamond"
      , AxiomDisplayInfo(("〈·〉", "<.>"), "<span class=\"k4-axiom-key\">〈a〉P </span> ↔ ¬[a]¬P")
      , "diamond", {case () => HilbertCalculus.diamond}),
    new DerivedAxiomInfo("[] box", "[.]", "box", {case () => HilbertCalculus.useAt(DerivedAxioms.boxAxiom)}),
    new PositionTacticInfo("assignb"
      , AxiomDisplayInfo("[:=]", "<span class=\"k4-axiom-key\">[x:=c]p(x)</span>↔p(c)")
      , {case () => TactixLibrary.assignb}),
    new CoreAxiomInfo("[:=] assign", "[:=]", "assignbAxiom", {case () => HilbertCalculus.useAt("[:=] assign")}),
    new CoreAxiomInfo("[:=] self assign", "[:=]", "selfassignb", {case () => HilbertCalculus.useAt("[:=] self assign")}),
    new DerivedAxiomInfo("<:=> assign", "<:=>", "assignd", {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:=> assign equality", "<:=>", "assigndEquality", {case () => HilbertCalculus.useAt("<:=> assign equality")}),
    new DerivedAxiomInfo("<:=> assign equality all", "<:=>", "assigndEqualityAll", {case () => HilbertCalculus.useAt("<:=> assign equality all")}),
    new CoreAxiomInfo("[:=] assign equality", "[:=]=", "assignbeq", {case () => HilbertCalculus.useAt("[:=] assign equality")}),
    new PositionTacticInfo("assignEquality", "[:=]=", {case () => DLBySubst.assignEquality}),
    new DerivedAxiomInfo("[:=] assign exists", ("[:=]∃","[:=]exists"), "assignbexists", {case () => HilbertCalculus.useAt(DerivedAxioms.assignbImpliesExistsAxiom) }),
    new DerivedAxiomInfo("[:=] assign all", ("[:=]∀","[:=]all"), "assignball", {case () => HilbertCalculus.useAt(DerivedAxioms.forallImpliesAssignbAxiom) }),
    new CoreAxiomInfo("[:=] assign equality exists", ("[:=]","[:=] assign exists"), "assignbequalityexists", {case () => HilbertCalculus.useAt("[:=] assign equality exists") }),
    new InputPositionTacticInfo("assignbExistsRule",
      RuleDisplayInfo(
        "[:=] assign exists",
        /* conclusion */ (List("&Gamma;"), List("∃t [x:=t;]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("[t:=e;][x:=t;]P", "&Delta;")) )
      ),
      List(TermArg("e")),
      _ => ((e: Term) => DLBySubst.assignbExists(e)): TypedFunc[Term, BelleExpr]
    ),
    new CoreAxiomInfo("[':=] differential assign"
      , AxiomDisplayInfo(("[′:=]","[':=]"), "[x′:=c]p(x′)↔p(c)")
      , "Dassignb", {case () => HilbertCalculus.Dassignb}),
    new CoreAxiomInfo("[:*] assign nondet"
      , AxiomDisplayInfo("[:*]", "<span class=\"k4-axiom-key\">[x:=*]p(x)</span>↔∀x p(x)")
      , "randomb", {case () => HilbertCalculus.randomb}),
    new CoreAxiomInfo("[?] test"
      , AxiomDisplayInfo("[?]", "[?Q]P↔(Q→P)")
      , "testb", {case () => HilbertCalculus.testb}),
    new DerivedAxiomInfo("<?> test", "<?>", "testd", {case () => HilbertCalculus.testd}),
    new CoreAxiomInfo("[++] choice"
      , AxiomDisplayInfo(("[∪]", "[++]"), "<span class=\"k4-axiom-key\">[a∪b]P</span>↔[a]P∧[b]P"), "choiceb", {case () => HilbertCalculus.choiceb}),
    new DerivedAxiomInfo("<++> choice", ("<∪>", "<++>"), "choiced", {case () => HilbertCalculus.choiced}),
    new CoreAxiomInfo("[;] compose"
      , AxiomDisplayInfo("[;]", "<span class=\"k4-axiom-key\">[a;b]P</span>↔[a][b]P")
      , "composeb", {case () => HilbertCalculus.composeb}),
    new DerivedAxiomInfo("<;> compose", "<;>", "composed", {case () => HilbertCalculus.composed}),
    new CoreAxiomInfo("[*] iterate"
      , AxiomDisplayInfo("[*]", "<span class=\"k4-axiom-key\">[a*]P</span>↔P∧[a][a*]P")
      , "iterateb", {case () => HilbertCalculus.iterateb}),
    new DerivedAxiomInfo("<*> iterate", "<*>", "iterated", {case () => HilbertCalculus.iterated}),
    new CoreAxiomInfo("<d> dual"
      , AxiomDisplayInfo(("<d>", "<d>"), "〈a^d〉P↔¬〈a〉¬P"), "duald", {case () => HilbertCalculus.duald}),
    new DerivedAxiomInfo("[d] dual"
      , AxiomDisplayInfo(("[d]", "[d]"), "[a^d]P↔¬[a]¬P"), "dualb", {case () => HilbertCalculus.dualb}),
    new DerivedAxiomInfo("[d] dual direct"
      , AxiomDisplayInfo(("[d]", "[d]"), "[a^d]P↔<a>P"), "dualDirectb", {case () => HilbertCalculus.useAt(DerivedAxioms.dualbDirectAxiom)}),
    new DerivedAxiomInfo("<d> dual direct"
      , AxiomDisplayInfo(("<d>", "<d>"), "<a^d>P↔[a]P"), "dualDirectd", {case () => HilbertCalculus.useAt(DerivedAxioms.dualdDirectAxiom)}),
    new CoreAxiomInfo("K modal modus ponens", "K", "K", {case () => TactixLibrary.K}),
    //@note the tactic I has a codeName and belleExpr, but there's no tactic that simply applies the I axiom
  //@todo why isn't the code name just "I"? And the belleExpr could be useAt("I")?
    new CoreAxiomInfo("I induction", "I", "induction", {case () => ???}),
    new CoreAxiomInfo("VK vacuous"
      , AxiomDisplayInfo("VK", "(p→[a]p)←[a]T")
      , "VK", {case () => HilbertCalculus.VK}),
    new DerivedAxiomInfo("V vacuous"
      , AxiomDisplayInfo("V", "p→[a]p")
      , "V", {case () => HilbertCalculus.V}),
    new CoreAxiomInfo("[]T system"
      , AxiomDisplayInfo("[]T", "[a]true")
      , "boxTrue", {case () => HilbertCalculus.boxTrue}),

    // differential equation axioms
    new CoreAxiomInfo("DW base", "DWbase", "DWbase", {case () => HilbertCalculus.DW}),
    new PositionTacticInfo("dW"
      , RuleDisplayInfo("Differential Weaken"
        , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]p(x)","&Delta;"))
        , /* premises */ List((List("&Gamma;<sub>const</sub>", "Q"), List("p(x)", "&Delta;<sub>const</sub>"))))
      , {case () => DifferentialTactics.diffWeaken}),
    new CoreAxiomInfo("DC differential cut"
    , InputAxiomDisplayInfo("DC","(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔[{x′=f(x)&Q∧R}]P)←[{x′=f(x)&Q}]R", List(FormulaArg("R")))
    , "DC", {case () => HilbertCalculus.useAt("DC differential cut")}),
    new InputPositionTacticInfo("dC"
    , RuleDisplayInfo("Differential Cut"
      , /* conclusion */ (List("&Gamma;"),List("[{x′=f(x) & Q}]P","&Delta;"))
      , /* premises */ List((List("&Gamma;"), List("[{x′=f(x) & Q}]R", "&Delta;")),
        (List("&Gamma;"), List("[{x′=f(x) & (Q∧R)}]P","&Delta;"))))
    , List(FormulaArg("R")) //@todo should be ListArg -> before merge, we already had lists in concrete Bellerophon syntax
    , _ => ((fml: Formula) => TactixLibrary.dC(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("dG",
      RuleDisplayInfo(
        "Differential Ghost",
        /* conclusion */ (List("&Gamma;"), List("[{x′=f(x) & Q}]P", "&Delta;")),
        /* premises */ List( (List("&Gamma;"), List("∃y [{x′=f(x),y′=a(x)y+b(x) & Q}]P", "&Delta;")) )
      ),
      List(VariableArg("y"), TermArg("a(x)"), TermArg("b(x)"), FormulaArg("P")),
      _ =>
        ((y: Variable) =>
          ((t1: Term) =>
            ((t2: Term) =>
              ((p: Option[Formula]) => TactixLibrary.dG(AtomicODE(DifferentialSymbol(y), Plus(Times(t1, y), t2)), p)
                ): TypedFunc[Option[Formula], BelleExpr]
              ): TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]
            ): TypedFunc[Term, TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]]
          ): TypedFunc[Variable, TypedFunc[Term, TypedFunc[Term, TypedFunc[Option[Formula], BelleExpr]]]]
    ),

    new CoreAxiomInfo("DE differential effect"
      , AxiomDisplayInfo("DE", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔[x′=f(x)&Q][x′:=f(x)]P")
      , "DE", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DE differential effect (system)"
      , AxiomDisplayInfo("DE", "<span class=\"k4-axiom-key\">[{x′=F,c&Q}]P</span>↔[{c,x′=F&Q}][x′:=f(x)]P")
      , "DEs", {case () => HilbertCalculus.DE}),
    new CoreAxiomInfo("DI differential invariance"
      , AxiomDisplayInfo("DI", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔[?Q]P)←(Q→[{x′=f(x)&Q}](P)′)")
      , "DIequiv", {case () => ???}),
    new DerivedAxiomInfo("DI differential invariant"
      , AxiomDisplayInfo("DI", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>←(Q→P∧[{x′=f(x)&Q}](P)′)")
      , "DI", {case () => HilbertCalculus.DI}),
    new CoreAxiomInfo("DG differential ghost"
      , AxiomDisplayInfo("DG", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔∃y [{x′=f(x),y′=a*y+b&Q}]P")
      , "DGa", {case () => HilbertCalculus.useAt("DG differential ghost")}),
    new CoreAxiomInfo("DG differential ghost constant"
      , AxiomDisplayInfo("DG", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔∃y [{x′=f(x),y′=g()&Q}]P")
      , "DGC", {case () => HilbertCalculus.useAt("DG differential ghost constant")}),
    new CoreAxiomInfo("DG differential ghost constant all"
      , AxiomDisplayInfo("DGa", "<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]P</span>↔∀y [{x′=f(x),y′=g()&Q}]P")
      , "DGCa", {case () => HilbertCalculus.useAt("DG differential ghost constant all")}),
    new CoreAxiomInfo("DG inverse differential ghost", "DG inverse differential ghost", "DGpp", {case () => ???}),
    new CoreAxiomInfo("DG inverse differential ghost implicational", "DG inverse differential ghost implicational", "DGi", {case () => ???}),
    new CoreAxiomInfo(", commute", ",", "commaCommute", {case () => ???}),
    new CoreAxiomInfo(", sort", ",", "commaSort", {case () => ???}),
    new CoreAxiomInfo("DS& differential equation solution", "DS&", "DS", {case () => HilbertCalculus.DS}),
    new CoreAxiomInfo("DIo open differential invariance >"
      , AxiomDisplayInfo("DIo >", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]f(x)>g(x)</span>↔[?Q]f(x)>g(x))←(Q→[{x′=f(x)&Q}](f(x)>g(x)→(f(x)>g(x))′))")
      , "DIogreater", {case () => ???}),
    new DerivedAxiomInfo("DIo open differential invariance <"
      , AxiomDisplayInfo("DIo <", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]f(x)<g(x)</span>↔[?Q]f(x)<g(x))←(Q→[{x′=f(x)&Q}](f(x)<g(x)→(f(x)<g(x))′))")
      , "DIoless", {case () => ???}),
    new CoreAxiomInfo("DIo open differential invariance >="
      , AxiomDisplayInfo("DIo >=", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]f(x)>=g(x)</span>↔[?Q]f(x)>=g(x))←(Q→[{x′=f(x)&Q}](f(x)>=g(x)→(f(x))'>(g(x))′))")
      , "DIogeq", {case () => ???}),
    new DerivedAxiomInfo("DIo open differential invariance <="
      , AxiomDisplayInfo("DIo >=", "(<span class=\"k4-axiom-key\">[{x′=f(x)&Q}]f(x)<=g(x)</span>↔[?Q]f(x)<=g(x))←(Q→[{x′=f(x)&Q}](f(x)<=g(x)→(f(x))'<(g(x))′))")
      , "DIoleq", {case () => ???}),
    new CoreAxiomInfo("DV differential variant >="
      , AxiomDisplayInfo("DVgeq", "todo DVgeq")
      , "DVgeq", {case () => ???}),
    new DerivedAxiomInfo("DV differential variant <="
      , AxiomDisplayInfo("DVleq", "todo DVleq")
      , "DVleq", {case () => ???}),

    // Differential Axioms
    new CoreAxiomInfo("c()' derive constant fn"
      , AxiomDisplayInfo(("c()'", "c()′"), "<span class=\"k4-axiom-key\">(c)′</span>=0")
      , "Dconst", {case () => HilbertCalculus.Derive.Dconst}),
    new CoreAxiomInfo("x' derive var"
      ,  AxiomDisplayInfo("x'", "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , "Dvar", {case () => HilbertCalculus.Derive.Dvar}),
    new DerivedAxiomInfo("x' derive variable"
      ,  AxiomDisplayInfo(("x′","x'"), "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , "DvariableAxiom", {case () => HilbertCalculus.useAt(DerivedAxioms.Dvariable)}),
    new DerivedAxiomInfo("x' derive var commuted"
      ,  AxiomDisplayInfo(("x′,C","x',C"), "x′=<span class=\"k4-axiom-key\">(x)′</span>")
      , "DvariableCommutedAxiom", {case () => HilbertCalculus.useAt(DerivedAxioms.DvariableCommuted)}),
    new PositionTacticInfo("Dvariable"
      ,  AxiomDisplayInfo(("x′","x'"), "<span class=\"k4-axiom-key\">(x)′</span>=x′")
      , {case () => DifferentialTactics.Dvariable}),
    new CoreAxiomInfo("+' derive sum"
      ,  AxiomDisplayInfo(("+′","+'"), "<span class=\"k4-axiom-key\">(f(x)+g(x))′</span>=f(x)′+g(x)′")
      , "Dplus", {case () => HilbertCalculus.Derive.Dplus}),
    new CoreAxiomInfo("-' derive neg"
      ,  AxiomDisplayInfo(("-′","-'"),"<span class=\"k4-axiom-key\">(-f(x))′</span>=-(f(x))′")
      , "Dneg", {case () => HilbertCalculus.Derive.Dneg}),
    new CoreAxiomInfo("-' derive minus"
      ,  AxiomDisplayInfo(("-′","-'"), "<span class=\"k4-axiom-key\">(f(x)-g(x))′</span>=f(x)′-g(x)′")
      , "Dminus", {case () => HilbertCalculus.Derive.Dminus}),
    new CoreAxiomInfo("*' derive product"
      ,  AxiomDisplayInfo(("·′","*'"), "<span class=\"k4-axiom-key\">(f(x)·g(x))′</span>=(f(x))′·g(x)+f(x)·(g(x))′")
      , "Dtimes", {case () => HilbertCalculus.Derive.Dtimes}),
    new CoreAxiomInfo("/' derive quotient"
      ,  AxiomDisplayInfo(("/′","/'"), "<span class=\"k4-axiom-key\">(f(g)/g(x))′</span>=(g(x)·(f(x))w-f(x)·(g(x))′)/g(x)^2")
      , "Dquotient", {case () => HilbertCalculus.Derive.Dquotient}),
    new CoreAxiomInfo("^' derive power"
      ,  AxiomDisplayInfo(("^′","^'"), "<span class=\"k4-axiom-key\">(f(g)^n)′</span>=n·f(g)^(n-1)·(f(g))′←n≠0")
      , "Dpower", {case () => HilbertCalculus.Derive.Dpower}),
    new CoreAxiomInfo("chain rule"
      ,  AxiomDisplayInfo(("∘′","o'"), "[y:=g(x)][y′:=1]((f(g(x)))′=(f(y))′·(g(x))′")
      , "Dcompose", {case () => TactixLibrary.Derive.Dcompose}),

    new CoreAxiomInfo("=' derive ="
      ,  AxiomDisplayInfo(("=′","='"),"<span class=\"k4-axiom-key\">(f(x)=g(x))′</span>↔f(x)′=g(x)′")
      , "Dequal", {case () => HilbertCalculus.Derive.Dequal}),
    new CoreAxiomInfo(">=' derive >="
      ,  AxiomDisplayInfo(("≥′",">='"), "<span class=\"k4-axiom-key\">(f(x)≥g(x))′</span>↔f(x)′≥g(x)′")
      , "Dgreaterequal", {case () => HilbertCalculus.Derive.Dgreaterequal}),
    new CoreAxiomInfo(">' derive >"
      ,  AxiomDisplayInfo((">′",">'"),"<span class=\"k4-axiom-key\">(f(x)>g(x))′</span>↔f(x)′≥g(x)′")
      , "Dgreater", {case () => HilbertCalculus.Derive.Dgreater}),
    new CoreAxiomInfo("<=' derive <="
      ,  AxiomDisplayInfo(("≤′","<='"), "<span class=\"k4-axiom-key\">(f(x)≤g(x))′</span>↔f(x)′≤g(x)′")
      , "Dlessequal", {case () => HilbertCalculus.Derive.Dlessequal}),
    new CoreAxiomInfo("<' derive <"
      ,  AxiomDisplayInfo(("<′","<'"),"<span class=\"k4-axiom-key\">(f(x)<g(m))′</span>↔f(x)′≤g(x)′")
      , "Dless", {case () => HilbertCalculus.Derive.Dless}),
    new CoreAxiomInfo("!=' derive !="
      ,  AxiomDisplayInfo(("≠′","!='"), "<span class=\"k4-axiom-key\">(f(x)≠g(x))′</span>↔f(x)′=g(x)′")
      , "Dnotequal", {case () => HilbertCalculus.Derive.Dnotequal}),
    new CoreAxiomInfo("&' derive and"
      ,  AxiomDisplayInfo(("∧′", "&'"),"<span class=\"k4-axiom-key\">(P&Q)′</span>↔P′∧Q′")
      , "Dand", {case () => HilbertCalculus.Derive.Dand}),
    new CoreAxiomInfo("|' derive or"
      ,  AxiomDisplayInfo(("∨′", "|'"), "<span class=\"k4-axiom-key\">(P|Q)′</span>↔P′∧Q′")
      , "Dor", {case () => HilbertCalculus.Derive.Dor}),
    new DerivedAxiomInfo("->' derive imply"
      ,  AxiomDisplayInfo(("→′","->'"), "<span class=\"k4-axiom-key\">(P→Q)′</span>↔(¬P∨Q)′")
      , "Dimply", {case () => HilbertCalculus.Derive.Dimply}),
    new CoreAxiomInfo("forall' derive forall"
      ,  AxiomDisplayInfo(("∀′","forall'"), "<span class=\"k4-axiom-key\">(∀x p(x))′</span>↔∀x (p(x))′")
      , "Dforall", {case () => HilbertCalculus.Derive.Dforall}),
    new CoreAxiomInfo("exists' derive exists"
      ,  AxiomDisplayInfo(("∃′","exists'"), "<span class=\"k4-axiom-key\">(∃x p(x))′</span>↔∀x (p(x))′")
      , "Dexists", {case () => HilbertCalculus.Derive.Dexists}),

    new PositionTacticInfo("derive", "'", {case () => HilbertCalculus.derive}),

    // first-order logic quantifiers
    new CoreAxiomInfo("all instantiate", ("∀inst","allInst"), "allInst", {case () => ???}),
    new DerivedAxiomInfo("all distribute", ("∀→","all->"), "allDist", {case () => HilbertCalculus.allDist}),
    new CoreAxiomInfo("vacuous all quantifier", ("V∀","allV"), "allV", {case () => HilbertCalculus.allV}),
    new DerivedAxiomInfo("vacuous exists quantifier", ("V∃","existsV"), "existsV", {case () => HilbertCalculus.existsV}),

    // more
    new CoreAxiomInfo("const congruence", "CCE", "constCongruence", {case () => ???}),
    new CoreAxiomInfo("const formula congruence", "CCQ", "constFormulaCongruence", {case () => ???}),
    // Note: only used to implement Dskipd
    new CoreAxiomInfo("DX differential skip", "DX", "DX", {case () => ???}),

    new CoreAxiomInfo("all dual", ("∀d","alld"), "alld", {case () => posnil}),
    new CoreAxiomInfo("all dual time", ("∀d","alldt"), "alldt", {case () => posnil}),
    new CoreAxiomInfo("all dual y", ("∀d","alldy"), "alldy", {case () => posnil}),
    new CoreAxiomInfo("all eliminate", ("∀e","alle"), "alle", {case () => posnil}),

    // compatibility axioms (derivable with Mathematica, but not with Z3)
    CoreAxiomInfo("dgZeroEquilibrium", "dgZeroEquilibrium", "dgZeroEquilibrium", _ => TactixLibrary.useAt("dgZeroEquilibrium")),

    // Derived axioms
    new DerivedAxiomInfo("exists eliminate", ("∃e","existse"), "existse", {case () => HilbertCalculus.existsE}),
    new DerivedAxiomInfo("[:=] assign update", "[:=]", "assignbup", {case () => HilbertCalculus.assignb}),
    new DerivedAxiomInfo("<:=> assign update", "<:=>", "assigndup", {case () => HilbertCalculus.assignd}),
    new DerivedAxiomInfo("<:*> assign nondet", "<:*>", "randomd", {case () => HilbertCalculus.randomd}),
    new DerivedAxiomInfo("[:=] assign equational", "[:=]==", "assignbequational", {case () => HilbertCalculus.assignb}),
    /* @todo replace all the axioms with useAt(axiom) */
    new DerivedAxiomInfo("<':=> differential assign", ("<′:=>","<':=>"), "Dassignd", {case () => useAt(DerivedAxioms.assignDAxiom)}),
    new DerivedAxiomInfo("DS differential equation solution", "DS", "DSnodomain", {case () => useAt(DerivedAxioms.DSnodomain)}),
    new DerivedAxiomInfo("Dsol& differential equation solution", "DS&", "DSddomain", {case () => useAt(DerivedAxioms.DSddomain)}),
    new DerivedAxiomInfo("Dsol differential equation solution", "DS", "DSdnodomain", {case () => useAt(DerivedAxioms.DSdnodomain)}),
    new DerivedAxiomInfo("DG differential pre-ghost", "DG", "DGpreghost", {case () => useAt(DerivedAxioms.DGpreghost)}),
    new DerivedAxiomInfo("DW differential weakening"
      , AxiomDisplayInfo("DW","[x′=f(x)&Q]P↔[x′=f(x)&Q](Q→P)")
      , "DW", {case () => HilbertCalculus.DW}),
    new DerivedAxiomInfo("DW differential weakening and"
      , AxiomDisplayInfo("DW∧","[x′=f(x)&Q]P→[x′=f(x)&Q](Q∧P)")
      , "DWeakenAnd", {case () => HilbertCalculus.DW}),
    new DerivedAxiomInfo("DX diamond differential skip", "DX", "Dskipd", {case () => useAt(DerivedAxioms.Dskipd)}),
    new DerivedAxiomInfo("DGd diamond differential ghost", "DGd", "DGd", {case () => useAt(DerivedAxioms.DGddifferentialghost)}),
    new DerivedAxiomInfo("DGd diamond differential ghost constant", "DGCd", "DGCd", {case () => useAt(DerivedAxioms.DGCddifferentialghostconst)}),
    new DerivedAxiomInfo("DGd diamond differential ghost constant exists", "DGCde", "DGCde", {case () => useAt(DerivedAxioms.DGCddifferentialghostconstexists)}),
    new DerivedAxiomInfo("DCd diamond differential cut", "DCd", "DCd", {case () => useAt(DerivedAxioms.DCddifferentialcut)}),
    new DerivedAxiomInfo("DWd diamond differential weakening", "DWd", "DWd", {case () => useAt(DerivedAxioms.DWddifferentialweakening)}),
    new DerivedAxiomInfo("DWd2 diamond differential weakening", "DWd2", "DWd2", {case () => useAt(DerivedAxioms.DWd2differentialweakening)}),
    new DerivedAxiomInfo(",d commute", "commaCommuted", "commaCommuted", {case () => useAt(DerivedAxioms.commaCommuted)}),
    new DerivedAxiomInfo("DGd diamond inverse differential ghost implicational", "DGdi", "DGdi", {case () => useAt(DerivedAxioms.DGdinversedifferentialghostimplicational)}),
//    new DerivedAxiomInfo("all eliminate", "alle", "allEliminate", {case () => useAt(DerivedAxioms.allEliminateAxiom)}),
    //@note derived axiom exists eliminate not yet proven -> use core axiom instead
//    new DerivedAxiomInfo("exists eliminate", "existse", "existsEliminate", {case () => useAt(DerivedAxioms.existsEliminate)}),
    new DerivedAxiomInfo("\\exists& exists and", "∃∧", "existsAnd", {case () => useAt(DerivedAxioms.existsAndAxiom)}),
    new DerivedAxiomInfo("\\forall-> forall implies", "∀→", "forallImplies", {case () => useAt(DerivedAxioms.forallImpliesAxiom)}),
    new DerivedAxiomInfo("exists dual", ("∃d","existsd"), "existsDual", {case () => useAt(DerivedAxioms.existsDualAxiom)}),
    new DerivedAxiomInfo("' linear", ("l′","l'"), "Dlinear", {case () => useAt(DerivedAxioms.Dlinear)}),
    new DerivedAxiomInfo("' linear right", ("l′","l'"), "DlinearRight", {case () => useAt(DerivedAxioms.DlinearRight)}),
    new DerivedAxiomInfo("!& deMorgan"
      , AxiomDisplayInfo(("¬∧", "!&"), "<span class=\"k4-axiom-key\">¬(p∧q)</span>↔(¬p|¬q)")
      , "notAnd", {case () => useAt(DerivedAxioms.notAnd)}),
    new DerivedAxiomInfo("!| deMorgan"
      , AxiomDisplayInfo(("¬∨","!|"), "<span class=\"k4-axiom-key\">(¬(p|q))</span>↔(¬p∧¬q)")
      , "notOr", {case () => useAt(DerivedAxioms.notOr)}),
    new DerivedAxiomInfo("!-> deMorgan"
      , AxiomDisplayInfo(("¬→","!->"), "<span class=\"k4-axiom-key\">¬(p->q)</span>↔(p∧¬q)")
      , "notImply", {case () => useAt(DerivedAxioms.notImply)}),
    new DerivedAxiomInfo("!<-> deMorgan"
      , AxiomDisplayInfo(("¬↔", "!<->"), "<span class=\"k4-axiom-key\">¬(p↔q)</span>↔(p∧¬q)| (¬p∧q)")
      , "notEquiv", {case () => useAt(DerivedAxioms.notEquiv)}),
    new DerivedAxiomInfo("!all"
      , AxiomDisplayInfo(("¬∀", "!all"), "<span class=\"k4-axiom-key\">¬∀x (p(x)))</span>↔∃x (¬p(x))")
      , "notAll", {case () => useAt(DerivedAxioms.notAll)}),
    new DerivedAxiomInfo("!exists"
      , AxiomDisplayInfo(("¬∃","!exists"), "<span class=\"k4-axiom-key\">(¬∃x (p(x)))</span>↔∀x (¬p(x))")
      , "notExists", {case () => useAt(DerivedAxioms.notExists)}),
    new DerivedAxiomInfo("![]", ("¬[]","![]"), "notBox", {case () => useAt(DerivedAxioms.notBox)}),
    new DerivedAxiomInfo("!<>", ("¬<>","!<>"), "notDiamond", {case () => useAt(DerivedAxioms.notDiamond)}),
    new DerivedAxiomInfo("[] split"
      , AxiomDisplayInfo(("[]∧", "[]^"), "<span class=\"k4-axiom-key\">[a](P∧Q)</span>↔[a]P ∧ [a]Q")
      , "boxAnd", {case () => HilbertCalculus.boxAnd}),
    new DerivedAxiomInfo("[] conditional split"
      , AxiomDisplayInfo(("[]→∧", "[]->^"), "<span class=\"k4-axiom-key\">[a](P→Q∧R)</span> ↔ [a](P→Q) ∧ [a](P→R)")
      , "boxImpliesAnd", {case () => HilbertCalculus.boxImpliesAnd}),
    new DerivedAxiomInfo("<> split"
      , AxiomDisplayInfo(("<>∨","<>|"), "<span class=\"k4-axiom-key\">〈a〉(P∨Q)</span>↔〈a〉P ∨ 〈a〉Q")
        , "diamondOr", {case () => useAt(DerivedAxioms.diamondOr)}),
//    new DerivedAxiomInfo("<> split left", "<>|<-", "diamondSplitLeft", {case () => useAt(DerivedAxioms.diamondSplitLeft)}),
//    new DerivedAxiomInfo("[] split left", "[]&<-", "boxSplitLeft", {case () => useAt(DerivedAxioms.boxSplitLeft)}),
//    new DerivedAxiomInfo("[] split right", "[]&->", "boxSplitRight", {case () => useAt(DerivedAxioms.boxSplitRight)}),
    new DerivedAxiomInfo("<*> approx", "<*> approx", "loopApproxd", {case () => useAt(DerivedAxioms.loopApproxd)}),
    new DerivedAxiomInfo("<*> stuck", "<*> stuck", "loopStuck", {case () => useAt(DerivedAxioms.loopStuck)}),
    new DerivedAxiomInfo("<'> stuck", ("<′> stuck","<'> stuck"), "odeStuck", {case () => useAt(DerivedAxioms.odeStuck)}),
    new DerivedAxiomInfo("[] post weaken", "[]PW", "postWeaken", {case () => useAt(DerivedAxioms.postconditionWeaken)}),
    new DerivedAxiomInfo("<-> reflexive", ("↔R","<->R"), "equivReflexive", {case () => useAt(DerivedAxioms.equivReflexiveAxiom)}),
    new DerivedAxiomInfo("-> distributes over &", ("→∧", "->&"), "implyDistAnd", {case () => useAt(DerivedAxioms.implyDistAndAxiom)}),
    new DerivedAxiomInfo("-> distributes over <->", ("→↔","-><->"), "implyDistEquiv", {case () => useAt(DerivedAxioms.implyDistEquivAxiom)}),
    new DerivedAxiomInfo("-> weaken", ("→W","->W"), "implyWeaken", {case () => useAt(DerivedAxioms.implWeaken)}),
    new DerivedAxiomInfo("!! double negation"
      , AxiomDisplayInfo(("¬¬","!!"), "(¬¬p↔p")
      , "doubleNegation", {case () => useAt(DerivedAxioms.doubleNegationAxiom)}),
    new DerivedAxiomInfo(":= assign dual", ":=D", "assignDual", {case () => useAt(DerivedAxioms.assignDualAxiom)}),
    new DerivedAxiomInfo(":= assign dual 2", ":=D", "assignDual2", {case () => useAt(DerivedAxioms.assignDual2Axiom)}),
    new DerivedAxiomInfo("[:=] vacuous assign", "V[:=]", "vacuousAssignb", {case () => useAt(DerivedAxioms.vacuousAssignbAxiom)}),
    new DerivedAxiomInfo("<:=> vacuous assign", "V<:=>", "vacuousAssignd", {case () => useAt(DerivedAxioms.vacuousAssigndAxiom)}),
    new DerivedAxiomInfo("[*] approx", "[*] approx", "loopApproxb", {case () => useAt(DerivedAxioms.loopApproxb)}),
  //@todo might have a better name
    new DerivedAxiomInfo("exists generalize", ("∃G","existsG"), "existsGeneralize", {case () => useAt(DerivedAxioms.existsGeneralize)}),
    new DerivedAxiomInfo("all substitute", ("∀S","allS"), "allSubstitute", {case () => useAt(DerivedAxioms.allSubstitute)}),
    new DerivedAxiomInfo("V[:*] vacuous assign nondet", "V[:*]", "vacuousBoxAssignNondet", {case () => useAt(DerivedAxioms.vacuousBoxAssignNondetAxiom)}),
    new DerivedAxiomInfo("V<:*> vacuous assign nondet", "V<:*>", "vacuousDiamondAssignNondet", {case () => useAt(DerivedAxioms.vacuousDiamondAssignNondetAxiom)}),
    new DerivedAxiomInfo("Domain Constraint Conjunction Reordering", ("{∧}C","{&}C"), "domainCommute", {case () => useAt(DerivedAxioms.domainCommute)}), //@todo shortname
    new DerivedAxiomInfo("& commute", ("∧C","&C"), "andCommute", {case () => useAt(DerivedAxioms.andCommute)}),
    new DerivedAxiomInfo("& reflexive", ("∧R","&R"), "andReflexive", {case () => useAt(DerivedAxioms.andReflexive)}),
    new DerivedAxiomInfo("& associative", ("∧A","&A"), "andAssoc", {case () => useAt(DerivedAxioms.andAssoc)}),
    new DerivedAxiomInfo("-> expand", ("→E","->E"), "implyExpand", {case () => useAt(DerivedAxioms.implyExpand)}),
    new DerivedAxiomInfo("-> tautology", ("→taut","->taut"), "implyTautology", {case () => useAt(DerivedAxioms.implyTautology)}),
    new DerivedAxiomInfo("\\forall->\\exists", ("∀→∃","all->exists"), "forallThenExists", {case () => useAt(DerivedAxioms.forallThenExistsAxiom)}),
    new DerivedAxiomInfo("->true"
      , AxiomDisplayInfo(("→⊤","->T"), "<span class=\"k4-axiom-key\">(p→⊤)</span>↔⊤")
      , "implyTrue", {case () => useAt(DerivedAxioms.impliesTrue)}),
    new DerivedAxiomInfo("true->"
      , AxiomDisplayInfo(("⊤→", "T->"), "<span class=\"k4-axiom-key\">(⊤→p)</span>↔p")
      , "trueImply", {case () => useAt(DerivedAxioms.trueImplies)}),
    new DerivedAxiomInfo("&true"
      , AxiomDisplayInfo(("∧⊤","&T"), "<span class=\"k4-axiom-key\">(p∧⊤)</span>↔p")
      , "andTrue", {case () => useAt(DerivedAxioms.andTrue)}),
    new DerivedAxiomInfo("true&"
      , AxiomDisplayInfo(("⊤∧","T&"), "<span class=\"k4-axiom-key\">(⊤∧p)</span>↔p")
      , "trueAnd", {case () => useAt(DerivedAxioms.trueAnd)}),
    new DerivedAxiomInfo("0*", "0*", "zeroTimes", {case () => useAt(DerivedAxioms.zeroTimes)}),
    new DerivedAxiomInfo("0+", "0+", "zeroPlus", {case () => useAt(DerivedAxioms.zeroPlus)}),
    new DerivedAxiomInfo("*0", "*0", "timesZero", {case () => useAt(DerivedAxioms.timesZero)}),
    new DerivedAxiomInfo("+0", "+0", "plusZero", {case () => useAt(DerivedAxioms.plusZero)}),
    new DerivedAxiomInfo("= reflexive", "=R", "equalReflexive", {case () => useAt(DerivedAxioms.equalReflex)}),
    new DerivedAxiomInfo(">= reflexive", ">=R", "greaterEqualReflexive", {case () => useAt(DerivedAxioms.greaterEqualReflex)}),
    new DerivedAxiomInfo("= commute", "=C", "equalCommute", {case () => useAt(DerivedAxioms.equalCommute)}),
    new DerivedAxiomInfo("<=", "<=", "lessEqual", {case () => useAt(DerivedAxioms.lessEqual)}),
    new DerivedAxiomInfo("! <"
      , AxiomDisplayInfo(("¬<","!<"), "<span class=\"k4-axiom-key\">¬(f<g)</span>↔(f≥g)")
      , "notLess", {case () => useAt(DerivedAxioms.notLess)}),
    new DerivedAxiomInfo("! >"
      , AxiomDisplayInfo(("¬>","!>"), "<span class=\"k4-axiom-key\">¬(f>g)</span>↔(f≤g)")
      , "notGreater", {case () => useAt(DerivedAxioms.notGreater)}),
    new DerivedAxiomInfo("< negate", ("¬≤","!<="), "notGreaterEqual", {case () => useAt(DerivedAxioms.notGreaterEqual)}),
    new DerivedAxiomInfo(">= flip", ">=F", "flipGreaterEqual", {case () => useAt(DerivedAxioms.flipGreaterEqual)}),
    new DerivedAxiomInfo("> flip", ">F", "flipGreater", {case () => useAt(DerivedAxioms.flipGreater)}),
    new DerivedAxiomInfo("<= flip", "<=F", "flipLessEqual", {case () => useAt(DerivedAxioms.flipLessEqual)}),
    new DerivedAxiomInfo("< flip", "<F", "flipLess", {case () => useAt(DerivedAxioms.flipLess)}),
    new DerivedAxiomInfo("<", "<", "less", {case () => useAt(DerivedAxioms.less)}),
    new DerivedAxiomInfo(">", ">", "greater", {case () => useAt(DerivedAxioms.greater)}),

//    new DerivedAxiomInfo("!= elimination", ("≠", "!="), "notEqualElim", {case () => useAt(DerivedAxioms.notEqualElim)}),
//    new DerivedAxiomInfo(">= elimination", ("≥", ">="), "greaterEqualElim", {case () => useAt(DerivedAxioms.greaterEqualElim)}),
//    new DerivedAxiomInfo("> elimination", ">", "greaterElim", {case () => useAt(DerivedAxioms.greaterElim)}),
    new DerivedAxiomInfo("1>0", "1>0", "oneGreaterZero", {case () => useAt(DerivedAxioms.oneGreaterZero)}),
    new DerivedAxiomInfo("nonnegative squares", "^2>=0", "nonnegativeSquares", {case () => useAt(DerivedAxioms.nonnegativeSquares)}),
    new DerivedAxiomInfo(">2!=", ">2!=", "greaterImpliesNotEqual", {case () => useAt(DerivedAxioms.greaterImpliesNotEqual)}),
    new DerivedAxiomInfo("> monotone", ">mon", "greaterMonotone", {case () => useAt(DerivedAxioms.greaterMonotone)}),

    new DerivedAxiomInfo("abs", "abs", "abs", {case () => useAt(DerivedAxioms.absDef)}),
    new DerivedAxiomInfo("min", "min", "min", {case () => useAt(DerivedAxioms.minDef)}),
    new DerivedAxiomInfo("max", "max", "max", {case () => useAt(DerivedAxioms.maxDef)}),
    new DerivedAxiomInfo("& recursor", "& recursor", "andRecursor", {case () => useAt(DerivedAxioms.andRecursor)}),
    new DerivedAxiomInfo("| recursor", "| recursor", "orRecursor", {case () => useAt(DerivedAxioms.orRecursor)}),
    new DerivedAxiomInfo("<= both", "<= both", "intervalLEBoth", {case () => useAt(DerivedAxioms.intervalLEBoth)}),
    new DerivedAxiomInfo("< both", "< both", "intervalLBoth", {case () => useAt(DerivedAxioms.intervalLBoth)}),
    new DerivedAxiomInfo("neg<= up", "neg<=", "intervalUpNeg", {case () => useAt(DerivedAxioms.intervalUpNeg)}),
    new DerivedAxiomInfo("abs<= up", "abs<=", "intervalUpAbs", {case () => useAt(DerivedAxioms.intervalUpAbs)}),
    new DerivedAxiomInfo("max<= up", "max<=", "intervalUpMax", {case () => useAt(DerivedAxioms.intervalUpMax)}),
    new DerivedAxiomInfo("min<= up", "min<=", "intervalUpMin", {case () => useAt(DerivedAxioms.intervalUpMin)}),
    new DerivedAxiomInfo("+<= up", "+<=", "intervalUpPlus", {case () => useAt(DerivedAxioms.intervalUpPlus)}),
    new DerivedAxiomInfo("-<= up", "-<=", "intervalUpMinus", {case () => useAt(DerivedAxioms.intervalUpMinus)}),
    new DerivedAxiomInfo("*<= up", "*<=", "intervalUpTimes", {case () => useAt(DerivedAxioms.intervalUpTimes)}),
    new DerivedAxiomInfo("1Div<= up", "1/<=", "intervalUp1Divide", {case () => useAt(DerivedAxioms.intervalUp1Divide)}),
    new DerivedAxiomInfo("Div<= up", "/<=", "intervalUpDivide", {case () => useAt(DerivedAxioms.intervalUpDivide)}),
    new DerivedAxiomInfo("pow<= up", "pow<=", "intervalUpPower", {case () => useAt(DerivedAxioms.intervalUpPower)}),
    new DerivedAxiomInfo("<=neg down", "<=neg", "intervalDownNeg", {case () => useAt(DerivedAxioms.intervalDownNeg)}),
    new DerivedAxiomInfo("<=abs down", "<=abs", "intervalDownAbs", {case () => useAt(DerivedAxioms.intervalDownAbs)}),
    new DerivedAxiomInfo("<=max down", "<=max", "intervalDownMax", {case () => useAt(DerivedAxioms.intervalDownMax)}),
    new DerivedAxiomInfo("<=min down", "<=min", "intervalDownMin", {case () => useAt(DerivedAxioms.intervalDownMin)}),
    new DerivedAxiomInfo("<=+ down", "<=+", "intervalDownPlus", {case () => useAt(DerivedAxioms.intervalDownPlus)}),
    new DerivedAxiomInfo("<=- down", "<=-", "intervalDownMinus", {case () => useAt(DerivedAxioms.intervalDownMinus)}),
    new DerivedAxiomInfo("<=* down", "<=*", "intervalDownTimes", {case () => useAt(DerivedAxioms.intervalDownTimes)}),
    new DerivedAxiomInfo("<=1Div down", "<=1/", "intervalDown1Divide", {case () => useAt(DerivedAxioms.intervalDown1Divide)}),
    new DerivedAxiomInfo("<=Div down", "<=/", "intervalDownDivide", {case () => useAt(DerivedAxioms.intervalDownDivide)}),
    new DerivedAxiomInfo("<=pow down", "<=pow", "intervalDownPower", {case () => useAt(DerivedAxioms.intervalDownPower)}),
    new DerivedAxiomInfo("! !="
      , AxiomDisplayInfo(("¬≠","!!="), "<span class=\"k4-axiom-key\">(¬(f≠g)</span>↔(f=g))")
      , "notNotEqual", {case () => useAt(DerivedAxioms.notNotEqual)}),
    new DerivedAxiomInfo("! ="
      , AxiomDisplayInfo(("¬ =","! ="), "<span class=\"k4-axiom-key\">(¬(f=g))</span>↔(f≠g)")
      , "notEqual", {case () => useAt(DerivedAxioms.notEqual)}),
    new DerivedAxiomInfo("! <="
      , AxiomDisplayInfo(("¬≤","!<="), "<span class=\"k4-axiom-key\">(¬(f≤g)</span>↔(f>g)")
      , "notLessEqual", {case () => useAt(DerivedAxioms.notLessEqual)}),
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
    new DerivedAxiomInfo("-> self", ("→self","-> self"), "implySelf", {case () => useAt(DerivedAxioms.implySelf)}),
    new DerivedAxiomInfo("-> converse", ("→conv","-> conv"), "converseImply", {case () => useAt(DerivedAxioms.converseImply)}),
    new DerivedAxiomInfo("<-> true", ("↔true","<-> true"), "equivTrue", {case () => useAt(DerivedAxioms.equivTrue)}),
    new DerivedAxiomInfo("Kd diamond modus ponens", "Kd", "Kd", {case () => useAt(DerivedAxioms.KdAxiom)}),
    new DerivedAxiomInfo("Kd2 diamond modus ponens", "Kd2", "Kd2", {case () => useAt(DerivedAxioms.Kd2Axiom)}),
    //@todo internal only
//    new DerivedAxiomInfo("K1", "K1", "K1", {case () => useAt(DerivedAxioms.K1)}),
//    new DerivedAxiomInfo("K2", "K2", "K2", {case () => useAt(DerivedAxioms.K2)}),
    new DerivedAxiomInfo("PC1", "PC1", "PC1", {case () => useAt(DerivedAxioms.PC1)}),
    new DerivedAxiomInfo("PC2", "PC2", "PC2", {case () => useAt(DerivedAxioms.PC2)}),
    new DerivedAxiomInfo("PC3", "PC3", "PC3", {case () => useAt(DerivedAxioms.PC3)}),
    new DerivedAxiomInfo("PC9", "PC9", "PC9", {case () => useAt(DerivedAxioms.PC9)}),
    new DerivedAxiomInfo("PC10", "PC10", "PC10", {case () => useAt(DerivedAxioms.PC10)}),
    new DerivedAxiomInfo("K modal modus ponens &", "K&", "Kand", {case () => useAt(DerivedAxioms.Kand)}),
    new DerivedAxiomInfo("&->", "&->", "andImplies", {case () => useAt(DerivedAxioms.andImplies)}),
    // @internal axioms for unit tests
    new DerivedAxiomInfo("exists dual dummy", "DUMMY", "dummyexistsDualAxiomT", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy", "DUMMY", "dummyallDualAxiom", {case () => ???}),
    new DerivedAxiomInfo("all dual dummy 2", "DUMMY", "dummyallDualAxiom2", {case () => ???}),
    new DerivedAxiomInfo("+id' dummy", "DUMMY", "dummyDplus0", {case () => ???}),
    new DerivedAxiomInfo("+*' reduce dummy", "DUMMY", "dummyDplustimesreduceAxiom", {case () => ???}),
    new DerivedAxiomInfo("+*' expand dummy", "DUMMY", "dummyDplustimesexpandAxiom", {case () => ???}),
    new DerivedAxiomInfo("^' dummy", "DUMMY", "dummyDpowerconsequence", {case () => ???}),

    // metric axioms
    new DerivedAxiomInfo("= expand", "equalExpand", "equalExpand", {case () => useAt(DerivedAxioms.equalExpand)}),
    new DerivedAxiomInfo("<= to <", "leApprox", "leApprox", {case () => useAt(DerivedAxioms.le2l)}),
    new DerivedAxiomInfo("metric <=", "metricLe", "metricLe", {case () => useAt(DerivedAxioms.metricLessEqual)}),
    new DerivedAxiomInfo("metric <", "metricLt", "metricLt", {case () => useAt(DerivedAxioms.metricLess)}),
    new DerivedAxiomInfo("metric <= & <=", "metricAndLe", "metricAndLe", {case () => useAt(DerivedAxioms.metricAndLe)}),
    new DerivedAxiomInfo("metric < & <", "metricAndLt", "metricAndLt", {case () => useAt(DerivedAxioms.metricAndLt)}),
    new DerivedAxiomInfo("metric <= | <=", "metricOrLe", "metricOrLe", {case () => useAt(DerivedAxioms.metricOrLe)}),
    new DerivedAxiomInfo("metric < | <", "metricOrLt", "metricOrLt", {case () => useAt(DerivedAxioms.metricOrLt)}),

    // Note: Tactic info does not cover all tactics yet.
    // Proof rule position PositionTactics
    new PositionTacticInfo("notL"
      , RuleDisplayInfo(("¬L", "!L"), (List("¬P", "&Gamma;"),List("&Delta;")), List((List("&Gamma;"),List("&Delta;","P"))))
      , {case () => SequentCalculus.notL}),
    new PositionTacticInfo("notR"
      , RuleDisplayInfo(("¬R", "!R"), (List("&Gamma;"),List("¬P","&Delta;")), List((List("&Gamma;","P"),List("&Delta;"))))
      , {case () => SequentCalculus.notR}),
    new PositionTacticInfo("andR"
      , RuleDisplayInfo(("∧R", "^R"), (List("&Gamma;"),List("P∧Q","&Delta;")),
        List((List("&Gamma;"),List("P", "&Delta;")),
          (List("&Gamma;"), List("Q", "&Delta;"))))
      , {case () => SequentCalculus.andR}),
    new PositionTacticInfo("andL"
      , RuleDisplayInfo(("∧L", "^L"), (List("P∧Q", "&Gamma;"),List("&Delta;")), List((List("&Gamma;","P","Q"),List("&Delta;"))))
      , {case () => SequentCalculus.andL}),
    new PositionTacticInfo("orL"
      , RuleDisplayInfo(("∨L", "|L"), (List("P∨Q", "&Gamma;"),List("&Delta;")),
        List((List("&Gamma;", "P"),List("&Delta;")),
          (List("&Gamma;", "Q"),List("&Delta;"))))
      , {case () => SequentCalculus.orL}),
    new PositionTacticInfo("orR"
      , RuleDisplayInfo(("∨R", "|R"), (List("&Gamma;"),List("P∨Q","&Delta;")), List((List("&Gamma;"),List("P","Q","&Delta;"))))
      , {case () => SequentCalculus.orR}),
    new PositionTacticInfo("implyR"
      , RuleDisplayInfo(("→R", "->R"), (List("&Gamma;"),List("P→Q", "&Delta;")), List((List("&Gamma;","P"),List("Q","&Delta;"))))
      , {case () => SequentCalculus.implyR}),
    new TwoPositionTacticInfo("implyRi", "implyRi", _ => SequentCalculus.implyRi()),
    new PositionTacticInfo("implyL"
      , RuleDisplayInfo(("→L", "->L"), (List("P→Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P"),List("&Delta;")),
          (List("&Gamma;"),List("Q","&Delta;"))))
      , {case () => SequentCalculus.implyL}),
    new PositionTacticInfo("equivL"
      , RuleDisplayInfo(("↔L", "<->L"), (List("P↔Q","&Gamma;"),List("&Delta;")),
        List((List("&Gamma;","P∧Q"),List("&Delta;")),
          (List("&Gamma;","¬P∧¬Q"),List("&Delta;"))
         ))
      , {case () => SequentCalculus.equivL}),
    new PositionTacticInfo("equivR"
      , RuleDisplayInfo(("↔R", "<->R"), (List("&Gamma;"),List("P↔Q","&Delta;")),
        List((List("&Gamma;","P","Q"),List("&Delta;")),
          (List("&Gamma;","¬P","¬Q"),List("&Delta;"))))
      , {case () => SequentCalculus.equivR}),
    new InputPositionTacticInfo("allL"
      , RuleDisplayInfo(("∀L", "allL"), (List("&Gamma;","∀x P(x)"), List("&Delta;")),
        List((List("&Gamma;", "P(θ)"),List("&Delta;"))))
      , List(TermArg("θ"))
      , _ => ((t:Term) => SequentCalculus.allL(t)): TypedFunc[Term, BelleExpr]),
    new PositionTacticInfo("allR"
      , RuleDisplayInfo(("∀R", "allR"), (List("&Gamma;"), List("∀x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(x)","&Delta;"))))
      , {case () => SequentCalculus.allR}),
    new PositionTacticInfo("existsL"
      , RuleDisplayInfo(("∃L", "existsL"), (List("&Gamma;","∃x P(x)"),List("&Delta;")),
        List((List("&Gamma;","P(x)"),List("&Delta;"))))
      , {case () => SequentCalculus.existsL}),
    new TacticInfo("G"
      , RuleDisplayInfo("G", (List("&Gamma;"), List("[a]P", "&Delta;")), List((List(),List("P"))))
      , {case () => HilbertCalculus.G}),
    new PositionTacticInfo("GV"
      , RuleDisplayInfo("G&ouml;del/Vacuous", (List("&Gamma;"), List("[a]P", "&Delta;"))
      , List((List("&Gamma;<sub>const</sub>"), List("P", "&Delta;<sub>const</sub>"))))
      , {case () => TactixLibrary.abstractionb}),
    new InputPositionTacticInfo("existsR"
      , RuleDisplayInfo(("∃R", "existsR"), (List("&Gamma;"), List("∃x P(x)", "&Delta;")),
        List((List("&Gamma;"),List("P(θ)", "&Delta;"))))
      , List(TermArg("θ"))
      , _ => ((t:Term) => SequentCalculus.existsR(t)): TypedFunc[Term, BelleExpr]),

    new PositionTacticInfo("commuteEquivL", ("↔CL", "<->CL"), {case () => SequentCalculus.commuteEquivL}),
    new PositionTacticInfo("commuteEquivR", ("↔CR", "<->CR"), {case () => SequentCalculus.commuteEquivR}),
    new PositionTacticInfo("equivifyR", ("→↔","-><->"), {case () => SequentCalculus.equivifyR}),
    new PositionTacticInfo("hideL"
      , RuleDisplayInfo("WL", (List("&Gamma;", "P"),List("&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => SequentCalculus.hideL}),
    new PositionTacticInfo("hideR"
      , RuleDisplayInfo("WR", (List("&Gamma;"),List("P", "&Delta;"))
        , List((List("&Gamma;"),List("&Delta;")))),
      {case () => SequentCalculus.hideR}),
    new TacticInfo("smartHide", "smartHide", {case () => ArithmeticSimplification.smartHide}),
    new PositionTacticInfo("cohideL", "W", {case () => SequentCalculus.cohideL}),
    new PositionTacticInfo("cohideR", "W", {case () => SequentCalculus.cohideR}),
    new PositionTacticInfo("closeFalse"
      , RuleDisplayInfo(("⊥L", "falseL"), (List("⊥","&Gamma;"),List("&Delta;")), List())
      , {case () => TactixLibrary.closeF}),
    new PositionTacticInfo("closeTrue"
      , RuleDisplayInfo(("⊤R","trueR"), (List("&Gamma;"), List("⊤","&Delta;")),List())
        ,{case () => TactixLibrary.closeT}),
    new PositionTacticInfo("skolemizeR", "skolem", {case () => ProofRuleTactics.skolemizeR}),
    new PositionTacticInfo("cohide", "W", {case () => SequentCalculus.cohide}),
    new PositionTacticInfo("hide", "W", {case () => SequentCalculus.hide}),
    new PositionTacticInfo("allL2R", "L=R all", {case () => TactixLibrary.exhaustiveEqL2R}),
    new PositionTacticInfo("allR2L", "R=L all", {case () => TactixLibrary.exhaustiveEqR2L}),
    new PositionTacticInfo("minmax", "min/max", {case () => EqualityTactics.minmax}),
    new PositionTacticInfo("absExp", "absExp", {case () => EqualityTactics.abs}),
    new PositionTacticInfo("toSingleFormula", "toSingleFormula", {case () => PropositionalTactics.toSingleFormula}),

    // proof management tactics
    new TacticInfo("debug", "debug", {case () => DebuggingTactics.debug("")}),   // turn into input tactic if message should be stored too
    new TacticInfo("done", "done", {case () => TactixLibrary.done}), // turn into input tactic if message should be stored too

    // Proof rule two-position tactics
    new TwoPositionTacticInfo("coHide2", "W", {case () => SequentCalculus.cohide2}),
    new TwoPositionTacticInfo("equivRewriting", RuleDisplayInfo("equivRewriting", (List("&Gamma;", "∀X p(X) <-> q(X)"), List("p(Z)", "&Delta;")), List((List("&Gamma;", "∀X p(X) <-> q(X)"), List("q(Z)", "&Delta;")))), {case () => PropositionalTactics.equivRewriting}),
    new TwoPositionTacticInfo("instantiatedEquivRewriting", "instantiatedEquivRewriting", {case () => PropositionalTactics.instantiatedEquivRewriting}),
    //    new TwoPositionTacticInfo("exchangeL", "X", {case () => ProofRuleTactics.exchangeL}),
//    new TwoPositionTacticInfo("exchangeR", "X", {case () => ProofRuleTactics.exchangeR}),
    new TacticInfo("closeId",
      RuleDisplayInfo("Close by identity", (List("&Gamma;", "P"), List("P", "&Delta;")), Nil),
      {case () => TactixLibrary.closeId}),
    new TacticInfo("close",
      RuleDisplayInfo("Close by ⊥/⊤", (List("&Gamma;", "P", "⊥"), List("⊤", "P", "&Delta;")), Nil),
      {case () => TactixLibrary.close}),
    new TwoPositionTacticInfo("L2R",
      RuleDisplayInfo("Apply equality",
        /*conclusion*/ (List("&Gamma;", "x=y", "P(x)"), List("Q(x)", "&Delta;")),
        /*premise*/    List((List("&Gamma;", "x=y", "P(y)"), List("Q(y)", "&Delta;")))),
      {case () => (pos: AntePosition) => TactixLibrary.eqL2R(pos)}),
//      {case () => ProofRuleTactics.trivialCloser}), //@todo This is a 4.1b3 merge conflict. I'm not sure what the correct behavior is.

    // Proof rule input tactics
    new InputTacticInfo("cut"
      , RuleDisplayInfo(("Cut","cut")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;"),List("&Delta;","P")),
          (List("&Gamma;", "P"), List("&Delta;"))))
        ,List(FormulaArg("P")), _ => ((fml:Formula) => ProofRuleTactics.cut(fml)): TypedFunc[Formula, BelleExpr]),
    new InputTacticInfo("abbrv"
      , RuleDisplayInfo(("Abbreviate","abbrv")
        ,(List("&Gamma;"), List("&Delta;"))
        ,List(
          (List("&Gamma;", "v=t"),List("&Delta;"))))
      ,List(TermArg("t"),VariableArg("v")), _ => ((t:Term) => ((v: Option[Variable]) => EqualityTactics.abbrv(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),
    // Proof rule input position tactics
    new InputPositionTacticInfo("cutL", "Cut", List(FormulaArg("cutFormula")),
      _ => ((fml:Formula) => TactixLibrary.cutL(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("cutR", "Cut", List(FormulaArg("cutFormula")),
      _ => ((fml:Formula) => TactixLibrary.cutR(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("cutLR", "Cut", List(FormulaArg("cutFormula")),
      _ => ((fml:Formula) => TactixLibrary.cutLR(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("loop",
      RuleDisplayInfo("Loop Induction",(List("&Gamma;"), List("[a*]P", "&Delta;")),
        List(
          (List("&Gamma;"),List("j(x)", "&Delta;")),
          (List("j(x)"),List("[a]j(x)")),
          (List("j(x)"),List("P"))))
      , List(FormulaArg("j(x)")), _ => ((fml: Formula) => TactixLibrary.loop(fml)): TypedFunc[Formula, BelleExpr]),
    new PositionTacticInfo("loopauto", RuleDisplayInfo("loopauto",(List("&Gamma;"), List("[a*]P", "&Delta;")),
      List()), {case () => TactixLibrary.loopauto}, needsGenerator = true),

    new InputPositionTacticInfo("MR",
    RuleDisplayInfo("Monotonicity",(List("&Gamma;"), List("[a]P", "&Delta;")),
      List(
        (List("&Gamma;"),List("[a]Q", "&Delta;")),
        (List("Q"),List("P"))))
    , List(FormulaArg("Q")), _ => ((fml:Formula) => TactixLibrary.generalize(fml)): TypedFunc[Formula, BelleExpr]),
    new InputPositionTacticInfo("transform", "trafo", List(ExpressionArg("to")),
      _ => ((expr:Expression) => TactixLibrary.transform(expr)): TypedFunc[Expression, BelleExpr]),
    new InputPositionTacticInfo("boundRename"
      , RuleDisplayInfo(("BR", "BR"), (List("&Gamma;"), List("∀x P(x)","&Delta;")),
        List((List("&Gamma;"),List("∀y P(y)","&Delta;"))))
      , List(VariableArg("x"),VariableArg("y"))
      , _ => ((x:Variable) => ((y:Variable) => TactixLibrary.boundRename(x,y)): TypedFunc[Variable, BelleExpr]): TypedFunc[Variable, TypedFunc[Variable, BelleExpr]]),
    new InputPositionTacticInfo("stutter"
      , RuleDisplayInfo(("[:=]", "[:=]"), (List("&Gamma;"), List("P","&Delta;"))
      , List((List("&Gamma;"),List("[x:=x]P","&Delta;")))), List(VariableArg("x"))
      , _ => ((x:Variable) => DLBySubst.stutter(x)): TypedFunc[Variable, BelleExpr]),

  //
    new TacticInfo("nil", "nil", {case () => Idioms.nil}),

    new InputPositionTacticInfo(
      "transformEquality",
      "transformEquality",
      FormulaArg("equality") :: Nil,
      _ => ((f:Formula) => ArithmeticSimplification.transformEquality(f)): TypedFunc[Formula, BelleExpr]),

    new InputPositionTacticInfo(
      "discreteGhost",
      RuleDisplayInfo(("[:=] ghost", "[:=] ghost"), (List("&Gamma;"),List("P","&Delta;")),
        List((List("&Gamma;"), List("[gv:=gt;]P","&Delta;")))),
      TermArg("gt") :: VariableArg("gv") :: Nil,
      _ => ((t:Term) => ((v: Option[Variable]) => DLBySubst.discreteGhost(t, v)): TypedFunc[Option[Variable], BelleExpr]): TypedFunc[Term, _]),

    /*new TacticInfo("monb", "Box Monotonicity", {case () => TactixLibrary.monb}),
    new TacticInfo("monb2", "Box Monotonicity 2", {case () => DLBySubst.monb2}),
    //@todo unify axiomatic rule and derived rules mond / mondtodo
    new TacticInfo("mond", "Diamond Monotonicity", {case () => TactixLibrary.mond}),*/

    // TactixLibrary tactics
    new PositionTacticInfo("step", "step", {case () => TactixLibrary.step}),
    new PositionTacticInfo("stepAt", "stepAt", {case () => HilbertCalculus.stepAt}),
    new PositionTacticInfo("normalize", "normalize", {case () => TactixLibrary.normalize}),
    new PositionTacticInfo("unfold", "unfold", {case () => TactixLibrary.unfoldProgramNormalize}),
    new PositionTacticInfo("prop", "prop", {case () => TactixLibrary.prop}),
    new PositionTacticInfo("chase", "chase", {case () => TactixLibrary.chase}),
    new PositionTacticInfo("simplify", "simplify", {case () => SimplifierV3.simpTac()}, needsTool = true),
    // Technically in InputPositionTactic(Generator[Formula, {case () => ???}), but the generator is optional
    new TacticInfo("master", "master", {case () => (gen:Generator.Generator[Formula]) => TactixLibrary.master(gen)}, needsGenerator = true),
    new TacticInfo("auto", "auto", {case () => TactixLibrary.auto}, needsGenerator = true),
    new TacticInfo("QE", "QE",  {case () => TactixLibrary.QE}, needsTool = true),
    new TacticInfo("rcf", "rcf",  {case () => TactixLibrary.RCF}, needsTool = true),
    //new TacticInfo("MathematicaQE", "MathematicaQE", {case () => TactixLibrary.QE}, needsTool = true),
    new TacticInfo("pQE", "pQE",  {case () => TactixLibrary.partialQE}, needsTool = true),
    new TacticInfo("smartQE", "smartQE",  {case () => ArithmeticSpeculativeSimplification.speculativeQE}, needsTool = true),
    new TacticInfo("fullSimplify", "fullSimplify",  {case () => SimplifierV3.fullSimpTac()}, needsTool = true),
    //@todo universal closure may come with list of named symbols
    new PositionTacticInfo("universalClosure", "universalClosure", {case () => FOQuantifierTactics.universalClosure}),

    // Differential tactics
    new PositionTacticInfo("splitWeakInequality", "splitWeakInequality", {case () => DifferentialTactics.splitWeakInequality}, needsTool = true),
    new PositionTacticInfo("ODE",
      "Auto",
      {case () => TactixLibrary.ODE}, needsTool = true),
    new PositionTacticInfo("dgZeroMonomial",
      "dgZeroMonomial",
      {case () => DifferentialTactics.dgZeroMonomial}, needsTool = true),
    new PositionTacticInfo("dgZeroPolynomial",
      "dgZeroPolynomial",
      {case () => DifferentialTactics.dgZeroPolynomial}, needsTool = true),
    new PositionTacticInfo("dI",
    RuleDisplayInfo("Differential Invariant",
      (List("&Gamma;"),List("[{x′ = f(x) & Q}]P","&Delta;")),
      /* premises */ List((List("&Gamma;", "Q"), List("P", "&Delta;"), true /*@todo auto for now, but shouldn't be once we can stop in the middle of dI*/),
        (List("Q"), List("[x′:=f(x)](P)′"), true /*@todo auto for now, but shouldn't be once we can stop in the middle of dI*/))),
    {case () => DifferentialTactics.diffInd()}),
    new InputPositionTacticInfo("diffInvariant"
    , RuleDisplayInfo("Differential Cut + Differential Invariant"
      , (List("&Gamma;"),List("[{x′ = f(x) & Q}]P","&Delta;"))
      , /* premises */ List((List("&Gamma;"), List("[{x′ = f(x) & Q}]R", "&Delta;"), true),
        (List("&Gamma;"), List("[{x′ = f(x) & (Q∧R)}]P","&Delta;"))))
    , List(FormulaArg("R")) //@todo should be ListArg, before merge we already had concrete Bellerophon syntax for lists
    , _ => ((fml:Formula) => TactixLibrary.diffInvariant(fml)): TypedFunc[Formula, BelleExpr]),
    new PositionTacticInfo("solve",
      RuleDisplayInfo("Solution",
        (List("&Gamma;"),List("[{x′ = f(x) & q(x)}]p(x)","&Delta;")),
        List((List("&Gamma;"), List("∀t≥0 ( (∀0≤s≤t q(sol(s))) → [x:=sol(t)]p(x) )")))),
      {case () => TactixLibrary.solve}, needsTool = true),
    new PositionTacticInfo("DGauto",
      "DGauto",
      {case () => TactixLibrary.DGauto}, needsTool = true),

    // DLBySubst
    //new InputPositionTacticInfo("I", "I", List(FormulaArg("invariant")), {case () => (fml:Formula) => TactixLibrary.loop(fml)}),

    new PositionTacticInfo("decomposeController","decomposeController",{case () => {HybridProgramTactics.decomposeController}}),

    // Derived axiomatic rules
    new DerivedRuleInfo("all generalization"
      , RuleDisplayInfo(SimpleDisplayInfo("all gen", "allgen"), SequentDisplay(Nil, "\\forall x P"::Nil), SequentDisplay(Nil, "P"::Nil)::Nil)
      , "allGeneralize", {case () => HilbertCalculus.useAt(DerivedAxioms.allGeneralize)}),
    new DerivedRuleInfo("[] monotone"
      , RuleDisplayInfo(SimpleDisplayInfo("[] monotone", "[]monotone"), SequentDisplay("[a;]P"::Nil, "[a;]Q"::Nil), SequentDisplay("P"::Nil, "Q"::Nil)::Nil)
      , "monb", {case () => HilbertCalculus.useAt(DerivedAxioms.boxMonotone)}),
    new DerivedRuleInfo("[] monotone 2"
      , RuleDisplayInfo(SimpleDisplayInfo("[] monotone 2", "[]monotone 2"), SequentDisplay("[a;]Q"::Nil, "[a;]P"::Nil), SequentDisplay("Q"::Nil, "P"::Nil)::Nil)
      , "monb2", {case () => HilbertCalculus.useAt(DerivedAxioms.boxMonotone2)}),
    new DerivedRuleInfo("Goedel"
      , RuleDisplayInfo(SimpleDisplayInfo("G", "G"), SequentDisplay(Nil, "[a;]P"::Nil), SequentDisplay(Nil, "P"::Nil)::Nil)
      , "Goedel", {case () => HilbertCalculus.useAt(DerivedAxioms.Goedel)}),
    new DerivedRuleInfo("CT term congruence"
      , RuleDisplayInfo(SimpleDisplayInfo("CT term congruence", "CTtermCongruence"), SequentDisplay(Nil, "ctx_(f_(||)) = ctx_(g_(||))"::Nil), SequentDisplay(Nil, "f_(||) = g_(||)"::Nil)::Nil)
      , "CTtermCongruence", {case () => HilbertCalculus.useAt(DerivedAxioms.CTtermCongruence)}),

    // assertions and messages
    InputTacticInfo("print"
      , SimpleDisplayInfo("Print","print")
      ,List(StringArg("msg")), _ => ((msg: String) => DebuggingTactics.printIndexed(msg)): TypedFunc[String, BelleExpr])

  ) ensuring(consistentInfo _, "meta-information on AxiomInfo is consistent with actual (derived) axioms etc.")

  private def consistentInfo(list: List[DerivationInfo]): Boolean = {
    val canonicals = list.map(_.canonicalName)
    val codeNames = list.map(_.codeName).filter(_ != needsCodeName)
    val storedNames = list.filter(_.isInstanceOf[StorableInfo]).map(_.asInstanceOf[StorableInfo].storedName)
    list.forall({
        case ax: CoreAxiomInfo => ProvableSig.axiom.contains(ax.canonicalName) ensuring(r=>r, "core axiom correctly marked as CoreAxiomInfo: " + ax.canonicalName)
        case _: DerivedAxiomInfo => true //@todo can't ask DerivedAxioms.derivedAxiom yet since still initializing, besides that'd be circular
        case _ => true
      }
    ) &&
      (canonicals.length==canonicals.distinct.length ensuring(r=>r, "unique canonical names: " + (canonicals diff canonicals.distinct))) &&
      (codeNames.length==codeNames.distinct.length ensuring(r=>r, "unique code names / identifiers: " + (codeNames diff codeNames.distinct))) &&
      //@note to avoid file storage issues on some OSes, lowercase versions of code names used in files are expected to be unique.
      (storedNames.length==storedNames.distinct.length ensuring(r=>r, "unique stored names / identifiers across all derived axioms: " + (storedNames diff storedNames.distinct)))
  }

  /** code name mapped to derivation information */
  private val byCodeName: Map[String, DerivationInfo] =
  /* @todo Decide on a naming convention. Until then, making everything case insensitive */
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
        acc + ((info.codeName, info))
    }

  /** canonical name mapped to derivation information */
  private val byCanonicalName: Map[String, DerivationInfo] =
    allInfo.foldLeft(HashMap.empty[String,DerivationInfo]){case (acc, info) =>
      acc + ((info.canonicalName, info))
    }

  /** Retrieve meta-information on an inference by the given canonical name `axiomName` */
  def apply(axiomName: String): DerivationInfo = {
    byCanonicalName.getOrElse(axiomName, throw AxiomNotFoundException(axiomName))
  }

  /** Throw an AssertionError if id does not conform to the rules for code names. */
  def assertValidIdentifier(id: String): Unit = { assert(id.forall(_.isLetterOrDigit), "valid code name: " + id)}

  /** Retrieve meta-information on an inference by the given code name `codeName` */
  def ofCodeName(codeName:String): DerivationInfo = {
    assert(byCodeName != null, "byCodeName should not be null.")
    assert(codeName != null, "codeName should not be null.")

    byCodeName.getOrElse(codeName,
      throw new IllegalArgumentException("No such DerivationInfo of identifier " + codeName)
    )
  }

  /** Locate the derivation info for said tactic */
  def locate(t: BelleExpr): Option[DerivationInfo] = t match {
    case n: NamedBelleExpr => try { Some(ofCodeName(n.name)) } catch { case _: Exception => None }
    case AppliedPositionTactic(n, _) => locate(n)
    case AppliedBuiltinTwoPositionTactic(n, _, _) => locate(n)
    //@todo probably more cases
    case _ => None
  }

  def hasCodeName(codeName: String): Boolean = byCodeName.keySet.contains(codeName)
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
case class ExpressionArg (override val name: String) extends ArgInfo {
  val sort = "expression"
}
case class TermArg (override val name: String) extends ArgInfo {
  val sort = "term"
}
case class StringArg (override val name: String) extends ArgInfo {
  val sort = "string"
}
@deprecated("Until lists are actually added to the concrete syntax of Bellerophon.", "4.2b1")
case class ListArg (override val name: String, elementSort: String) extends ArgInfo {
  val sort = "list"
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
  /** Whether the derivation expects the caller to provide it with a way to generate invariants */
  val needsGenerator: Boolean = false
  override def toString: String = "DerivationInfo(" + canonicalName + "," + codeName + ")"
}

/** Meta-Information for a (derived) axiom or (derived) axiomatic rule */
trait ProvableInfo extends DerivationInfo {
  /** The Provable representing this (derived) axiom or (derived) axiomatic rule */
  val provable: ProvableSig
}

/** Storable items (e.g., as lemmas) */
trait StorableInfo extends DerivationInfo {
  val storedName: String = codeName.toLowerCase
}

object ProvableInfo {
  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def locate(name: String): Option[ProvableInfo] =
    DerivationInfo(name) match {
      case info: ProvableInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on a (derived) axiom or (derived) axiomatic rule by the given canonical name `name` */
  def apply(name: String): ProvableInfo =
    DerivationInfo(name) match {
      case info: ProvableInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not.")
    }

  /** Retrieve meta-information on an inference by the given stored name `storedName` */
  def ofStoredName(storedName: String): ProvableInfo = {
    DerivationInfo.allInfo.find({case si: StorableInfo => si.storedName == storedName case _ => false}) match {
      case Some(info: ProvableInfo) => info
      case Some(info) => throw new Exception("Derivation \"" + info.canonicalName + "\" is not an axiom or axiomatic rule, whether derived or not.")
      case _ => throw new Exception("Derivation \"" + storedName + "\" is not a derived axiom or rule.")
    }
  }

  val allInfo:List[ProvableInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[ProvableInfo]).map(_.asInstanceOf[ProvableInfo])
}


/** Meta-Information for an axiom or derived axiom */
trait AxiomInfo extends ProvableInfo {
  /** The valid formula that this axiom represents */
  def formula: Formula
}

/** Meta-Information for an axiom from the prover core */
case class CoreAxiomInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => DependentPositionTactic) extends AxiomInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory
  def belleExpr = codeName by ((pos:Position, seq:Sequent) => expr ()(pos))
  override val formula:Formula = {
    ProvableSig.axiom.get(canonicalName) match {
      case Some(fml) => fml
      case None => throw new AxiomNotFoundException("No formula for core axiom " + canonicalName)
    }
  }
  override lazy val provable:ProvableSig = ProvableSig.axioms(canonicalName)
  override val numPositionArgs = 1
}

/** Information for a derived axiom proved from the core */
case class DerivedAxiomInfo(override val canonicalName: String, override val display: DisplayInfo, override val codeName: String, expr: Unit => DependentPositionTactic) extends AxiomInfo with StorableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory.TacticForNameFactory
  def belleExpr: BelleExpr = codeName by ((pos: Position, _: Sequent) => expr()(pos))
  override lazy val formula: Formula =
    DerivedAxioms.derivedAxiomOrRule(canonicalName).conclusion.succ.head
//  {
//    DerivedAxioms.derivedAxiomMap.get(canonicalName) match {
//      case Some(fml) => fml._1
//      case None => throw new AxiomNotFoundException("No formula for axiom " + canonicalName)
//    }
//  }
  override lazy val provable:ProvableSig = DerivedAxioms.derivedAxiomOrRule(canonicalName)
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

  val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo]).map(_.asInstanceOf[DerivedAxiomInfo])
}

// tactics

/** Meta-information on a tactic performing a proof step (or more) */
class TacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false) extends DerivationInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  val canonicalName = codeName
}

case class PositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 1
}

case class TwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, expr: Unit => Any, needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

case class InputTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_, _], needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator)

case class InputPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_,_], needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 1
}

case class InputTwoPositionTacticInfo(override val codeName: String, override val display: DisplayInfo, override val inputs:List[ArgInfo], expr: Unit => TypedFunc[_, _], needsTool: Boolean = false, override val needsGenerator: Boolean = false)
  extends TacticInfo(codeName, display, expr, needsTool, needsGenerator) {
  override val numPositionArgs = 2
}

/** Information for an axiomatic rule */
case class AxiomaticRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String) extends ProvableInfo {
  // lazy to avoid circular initializer call
  lazy val expr = TactixLibrary.by(provable, codeName)
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr
  lazy val provable: ProvableSig = ProvableSig.rules(canonicalName)
  override val numPositionArgs = 0
}


/** Information for a derived rule proved from the core */
case class DerivedRuleInfo(override val canonicalName:String, override val display: DisplayInfo, override val codeName: String, expr: Unit => Any) extends ProvableInfo with StorableInfo {
  DerivationInfo.assertValidIdentifier(codeName)
  def belleExpr = expr()
  lazy val provable: ProvableSig = DerivedAxioms.derivedAxiomOrRule(canonicalName)
  override val numPositionArgs = 0
}

object DerivedRuleInfo {
  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def locate(ruleName: String): Option[DerivedRuleInfo] =
    DerivationInfo(ruleName) match {
      case info: DerivedRuleInfo => Some(info)
      case _ => None
    }
  /** Retrieve meta-information on a rule by the given canonical name `ruleName` */
  def apply(ruleName: String): DerivedRuleInfo =
    DerivationInfo(ruleName) match {
      case info: DerivedRuleInfo => info
      case info => throw new Exception("Derivation \"" + info.canonicalName + "\" is not a derived rule")
    }

  val allInfo:List[DerivedAxiomInfo] =  DerivationInfo.allInfo.filter(_.isInstanceOf[DerivedAxiomInfo]).map(_.asInstanceOf[DerivedAxiomInfo])
}
