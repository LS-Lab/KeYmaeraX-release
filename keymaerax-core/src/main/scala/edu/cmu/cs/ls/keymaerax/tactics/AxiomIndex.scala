/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import java.lang.Number

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.HilbertCalculus._

import scala.annotation.switch

/**
 * Axiom Indexing data structures.
 * @note Could be generated automatically, yet better in a precomputation fashion, not on the fly.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object AxiomIndex {

  type AxiomIndex = (PosInExpr, List[PosInExpr])

  /**
   * Return (derived) axiom index with key for matching and list of recursors on other sibling, i.e., after useAt/useFor
   * @see [[UnifyUSCalculus.chase()]]
   * @see [[UnifyUSCalculus.chaseFor()]]
   * @todo copy documentation from chase
   */
  def axiomIndex(axiom: String): AxiomIndex = (axiom: @switch) match {
      //@todo axiom.intern() to @switch?
    case "all instantiate" | "all eliminate"
         | "vacuous all quantifier" | "vacuous exists quantifier"
         | "all dual" | "exists dual" => directReduction
    case "const congruence" | "const formula congruence" => reverseReduction
    // [a] modalities and <a> modalities
    case "<> dual" | "[] dual" => (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)
    case "[:=] assign" | "<:=> assign" | "[':=] differential assign" | "<':=> differential assign" => directReduction
    case "[:=] assign equational" | "<:=> assign equational" => (PosInExpr(0::Nil), PosInExpr(Nil)::PosInExpr(0::1::Nil)::Nil)
    case "[:=] assign update" | "<:=> assign update" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    case "[:*] assign nondet" | "<:*> assign nondet" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(Nil)::Nil)
    case "[?] test"    | "<?> test"    => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "[++] choice" | "<++> choice" => binaryDefault
    case "[;] compose" | "<;> compose" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    case "[*] iterate" | "<*> iterate" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)

    case "DW"              => (PosInExpr(Nil), Nil)
    case "DC differential cut" => (PosInExpr(1::0::Nil), PosInExpr(Nil)::Nil)
    case "DE differential effect" | "DE differential effect (system)" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)
    case "DI differential invariant" => (PosInExpr(1::Nil), PosInExpr(1::1::Nil)::Nil)
    case "DG differential ghost" => directReduction
    case "DG differential Lipschitz ghost system" => directReduction
    case "DG++ System" => ???
    case "DG++" => ???
    case ", commute" => (PosInExpr(0::Nil), Nil)
    case "DS& differential equation solution" => (PosInExpr(0::Nil), PosInExpr(0::1::1::Nil)::PosInExpr(Nil)::Nil)
    case "DX differential skip" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "DX diamond differential skip" => (PosInExpr(1::Nil), PosInExpr(1::Nil)::Nil)

    // ' recursors for derivative axioms
    case "&' derive and" => binaryDefault
    case "|' derive or" => binaryDefault
    case "->' derive imply" => binaryDefault
    case "forall' derive forall" | "exists' derive exists" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "c()' derive constant fn" => nullaryDefault
    // recursors for derivative formula axioms
    case "=' derive ="   => binaryDefault
    case ">=' derive >=" => binaryDefault
    case ">' derive >"   => binaryDefault
    case "<=' derive <=" => binaryDefault
    case "<' derive <"   => binaryDefault
    case "!=' derive !=" => binaryDefault
    case "-' derive neg"   => unaryDefault
    case "+' derive sum"   => binaryDefault
    case "-' derive minus" => binaryDefault
    case "*' derive product" => (PosInExpr(0::Nil), PosInExpr(0::0::Nil)::PosInExpr(1::1::Nil)::Nil)
    case "/' derive quotient" => (PosInExpr(0::Nil), PosInExpr(0::0::0::Nil)::PosInExpr(0::1::1::Nil)::Nil)
    case "^' derive power" => (PosInExpr(1::0::Nil), PosInExpr(1::Nil)::Nil)
    case "chain rule" => (PosInExpr(1::1::0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "x' derive var"   => nullaryDefault

    /* @todo Adapt for hybrid games */
    case "V vacuous" => assert(Axiom.axioms(axiom)==Imply(PredOf(Function("p", None, Unit, Bool), Nothing), Box(ProgramConst("a"), PredOf(Function("p", None, Unit, Bool), Nothing))))
      (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)
    case "K modal modus ponens" => (PosInExpr(1::1::Nil), PosInExpr(Nil)::Nil)
    case "I induction" => (PosInExpr(1::Nil), /*PosInExpr(0::Nil)::*/PosInExpr(1::1::Nil)::PosInExpr(1::Nil)::Nil)
    // derived
    case "' linear" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    case "' linear right" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)


    case "DW differential weakening" => (PosInExpr(0::Nil), unknown)
    case "DC differential cut" => (PosInExpr(1::0::Nil), PosInExpr(Nil)::Nil)
    case "DE differential effect" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    //@todo unclear recursor
    case "DE differential effect system" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::Nil)
    //@todo other axioms

      // derived axioms

    case "!& deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "!| deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "!-> deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
    case "!<-> deMorgan" => (PosInExpr(0::Nil), PosInExpr(0::0::Nil)::PosInExpr(0::1::Nil)::PosInExpr(1::0::Nil)::PosInExpr(1::1::Nil)::Nil)
    case "!all" | "!exists" => (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(Nil)::Nil)
    case "![]" | "!<>" => (PosInExpr(0::Nil), PosInExpr(1::Nil)::PosInExpr(Nil)::Nil)

    case "[] split" => binaryDefault
    case "[] split left" | "[] split right" => directReduction
    case "<*> approx" => (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)
    case "<*> stuck" => (PosInExpr(0::Nil), Nil)
    case "<'> stuck" => (PosInExpr(0::Nil), Nil)

    case "+<= up" | "-<= up" | "<=+ down" | "<=- down" => (PosInExpr(1::Nil), PosInExpr(0::0::Nil)::PosInExpr(0::1::Nil)::Nil)

    // default position
    case _ => println("AxiomIndex: defaulted for " + axiom); (PosInExpr(0::Nil), Nil)
  }


  private val nullaryDefault = (PosInExpr(0::Nil), Nil)
  private val unaryDefault = (PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)
  private val binaryDefault = (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
  private val directReduction = (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)
  private val reverseReduction = (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)

  // lookup canonical axioms for an expression (index)

  /** Return the canonical (derived) axiom name that simplifies the expression expr */
  def axiomFor(expr: Expression): Option[String] = axiomsFor(expr) match {
    case first :: _ => Some(first)
    case Nil => None /*throw new IllegalArgumentException("No axiomFor for: " + expr)*/ }

  private val odeList = "DI differential invariant" :: "DC differential cut" :: "DG differential ghost" :: Nil
  // :: "DS& differential equation solution"

  private val unknown = Nil

  /** Return the (derived) axiom names that simplify the expression expr with simpler ones first */
  def axiomsFor(expr: Expression): List[String] = expr match {
    case Differential(t) => t match {
      case _: Variable  => "x' derive var" :: Nil
      case _: Number    => "c()' derive constant fn" :: Nil
      // optimizations
      case t: Term if StaticSemantics.freeVars(t).isEmpty => "c()' derive constant fn" :: Nil
      case _: Neg       => "-' derive neg" :: Nil
      case _: Plus      => "+' derive sum" :: Nil
      case _: Minus     => "-' derive minus" :: Nil
      // optimizations
      case Times(num,_) if StaticSemantics.freeVars(num).isEmpty => "' linear" :: Nil
      case Times(_,num) if StaticSemantics.freeVars(num).isEmpty => "' linear right" :: Nil
      case _: Times     => "*' derive product" :: Nil
      case _: Divide    => "/' derive quotient" :: Nil
      case _: Power     => "^' derive power" :: Nil
      case FuncOf(_,Nothing) => "c()' derive constant fn" :: Nil
    }
    case DifferentialFormula(f) => f match {
      case _: Equal     => "=' derive =" :: Nil
      case _: NotEqual  => "!=' derive !=" :: Nil
      case _: Greater   => ">' derive >" :: Nil
      case _: GreaterEqual => ">=' derive >=" :: Nil
      case _: Less      => "<' derive <" :: Nil
      case _: LessEqual => "<=' derive <=" :: Nil
      case _: And       => "&' derive and" :: Nil
      case _: Or        => "|' derive or" :: Nil
      case _: Imply     => "->' derive imply" :: Nil
      case _: Forall    => "forall' derive forall" :: Nil
      case _: Exists    => "exists' derive exists" :: Nil
    }
    case Box(a, _) => a match {
      case _: Assign    => "[:=] assign" :: "[:=] assign equational" :: "[:=] assign update" :: Nil
      case _: AssignAny => "[:*] assign nondet" :: Nil
      case _: Test      => "[?] test" :: Nil
      case ODESystem(_:AtomicODE,True)   => odeList :+ "DE differential effect"
      case ODESystem(_:AtomicODE,domain) => "DW differential weaken" :: odeList ++ List("DE differential effect")
      case ODESystem(_:DifferentialProduct,True)   => odeList :+ "DE differential effect (system)"
      case ODESystem(_:DifferentialProduct,domain) => "DW differential weaken" :: odeList ++ List("DE differential effect (system)")
      case _: Compose   => "[;] compose" :: Nil
      case _: Choice    => "[++] choice" :: Nil
      case _: Dual      => "[^d] dual" :: Nil
//      case _: Loop      => "[*] iterate" :: Nil
      case _ => unknown
    }
    case Diamond(a, _) => a match {
      case _: Assign    => "<:=> assign" :: "<:=> assign equational" :: "<:=> assign update" :: Nil
      case _: AssignAny => "<:*> assign nondet" :: Nil
      case _: Test      => "<?> test" :: Nil
      //@todo diamond duals of:
//      case ODESystem(_:AtomicODE,True)   => odeList :: "DE differential effect"
//      case ODESystem(_:AtomicODE,domain) => "DW differential weaken" :: odeList :: "DE differential effect" :: Nil
//      case ODESystem(_:DifferentialProduct,True)   => odeList :: "DE differential effect (system)"
//      case ODESystem(_:DifferentialProduct,domain) => "DW differential weaken" :: odeList :: "DE differential effect (system)" :: Nil
      case _: Compose   => "<;> compose" :: Nil
      case _: Choice    => "<++> choice" :: Nil
      case _: Dual      => "<^d> dual" :: Nil
      //      case _: Loop      => "[*] iterate" :: Nil
      case _ => unknown
    }
    case Not(f)         => f match {
      case Box(_,Not(_))=> "<> dual" :: Nil
      case _: Box       => "![]" :: Nil
      case Diamond(_,Not(_))=> "[] dual" :: Nil
      case _: Diamond   => "!<>" :: Nil
      case _: Forall    => "!all" :: Nil
      case _: Exists    => "!exists" :: Nil
      case _: Equal     => "! =" :: Nil
      case _: NotEqual  => "! !=" :: Nil
      case _: Less      => "! <" :: Nil
      case _: LessEqual => "! <=" :: Nil
      case _: Greater   => "! >" :: Nil
      case _: GreaterEqual => "! >=" :: Nil
      case _: Not       => "!! double negation" :: Nil
      case _: And       => "!& deMorgan" :: Nil
      case _: Or        => "!| deMorgan" :: Nil
      case _: Imply     => "!-> deMorgan" :: Nil
      case _: Equiv     => "!<-> deMorgan" :: Nil
    }
    case And(f, _)   if f == True => "true&" :: Nil
    case And(_, g)   if g == True => "&true" :: Nil
    case Imply(f, _) if f == True => "true->" :: Nil
    case Imply(_, g) if g == True => "->true" :: Nil
    //@todo could add And(False, _) etc ....

    case True | False => Nil
    case _ => unknown
  }
}