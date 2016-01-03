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

    case "[] split" | "<> split" => binaryDefault
    case "[] split left" | "[] split right" => directReduction
    case "<*> approx" => (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)
    case "<*> stuck" => (PosInExpr(0::Nil), Nil)
    case "<'> stuck" => (PosInExpr(0::Nil), Nil)

    case "[] post weaken" => (PosInExpr(1::Nil), PosInExpr(Nil)::Nil)

    case "+<= up" | "-<= up" | "<=+ down" | "<=- down" => (PosInExpr(1::Nil), PosInExpr(0::0::Nil)::PosInExpr(0::1::Nil)::Nil)

    // default position
    case _ => (PosInExpr(0::Nil), Nil)
  }


  private val nullaryDefault = (PosInExpr(0::Nil), Nil)
  private val unaryDefault = (PosInExpr(0::Nil), PosInExpr(0::Nil)::Nil)
  private val binaryDefault = (PosInExpr(0::Nil), PosInExpr(0::Nil)::PosInExpr(1::Nil)::Nil)
  private val directReduction = (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)
  private val reverseReduction = (PosInExpr(0::Nil), PosInExpr(Nil)::Nil)

  // lookup canonical axioms for an expression (index)

  /** Return the canonical (derived) axiom name that simplifies the expression expr */
  def axiomFor(expr: Expression): Option[String] = axiomsFor(expr, exhaustive = false) match {
    case first :: _ => Some(first)
    case Nil => None /*throw new IllegalArgumentException("No axiomFor for: " + expr)*/ }

  private val odeList = "DI differential invariant" :: "DC differential cut" :: "DG differential ghost" :: Nil
  // :: "DS& differential equation solution"

  private val unknown = Nil

  //@todo purpose unclear. Document or delete.
  private def preferredAxiom(expr: Expression): Option[String] = {
    expr match {
      case Differential(t) => t match {
        case _: Variable => Some("x' derive var")
        case _: Number => Some("c()' derive constant fn")
        // optimizations
        case t: Term if StaticSemantics.freeVars(t).isEmpty => Some("c()' derive constant fn")
        case _: Neg => Some("-' derive neg")
        case _: Plus => Some("+' derive sum")
        case _: Minus => Some("-' derive minus")
        // optimizations
        case Times(num, _) if StaticSemantics.freeVars(num).isEmpty => Some("' linear")
        case Times(_, num) if StaticSemantics.freeVars(num).isEmpty => Some("' linear right")
        case _: Times => Some("*' derive product")
        case _: Divide => Some("/' derive quotient")
        case _: Power => Some("^' derive power")
        case FuncOf(_, Nothing) => Some("c()' derive constant fn")
        case _ => None
      }
      case DifferentialFormula(f) => f match {
        case _: Equal => Some("=' derive =")
        case _: NotEqual => Some("!=' derive !=")
        case _: Greater => Some(">' derive >")
        case _: GreaterEqual => Some(">=' derive >=")
        case _: Less => Some("<' derive <")
        case _: LessEqual => Some("<=' derive <=")
        case _: And => Some("&' derive and")
        case _: Or => Some("|' derive or")
        case _: Imply => Some("->' derive imply")
        case _: Forall => Some("forall' derive forall")
        case _: Exists => Some("exists' derive exists")
        case _ => None
      }
      case Box(a, _) => a match {
        // Note: Using this axiom name to look up a tactic via AxiomInfo actually gives you assignb,
        // which handles several assignment axioms.
        case _: Assign => Some("[:=] assign")
        case _: AssignAny => Some("[:*] assign nondet")
        case _: Test => Some("[?] test")
        case _: Compose => Some("[;] compose")
        case _: Choice => Some("[++] choice")
        case _: Dual => Some("[] dual")
        case _ => None
      }
      case Diamond(a, _) => a match {
        case _: Assign => Some("<:=> assign")
        case _: AssignAny => Some("<:*> assign nondet")
        case _: Test => Some("<?> test")
        case _: Compose => Some("<;> compose")
        case _: Choice => Some("<++> choice")
        case _: Dual => Some("<^d> dual")
        case _ => None
      }
      case Not(f) => f match {
        case Box(_, Not(_)) => Some("<> dual")
        case _: Box => Some("![]")
        case Diamond(_, Not(_)) => Some("[] dual")
        case _: Diamond => Some("!<>")
        case _: Forall => Some("!all")
        case _: Exists => Some("!exists")
        case _: Equal => Some("! =")
        case _: NotEqual => Some("! !=")
        case _: Less => Some("! <")
        case _: LessEqual => Some("! <=")
        case _: Greater => Some("! >")
        case _: GreaterEqual => Some("! >=")
        case _: Not => Some("!! double negation")
        case _: And => Some("!& deMorgan")
        case _: Or => Some("!| deMorgan")
        case _: Imply => Some("!-> deMorgan")
        case _: Equiv => Some("!<-> deMorgan")
        case _ => None
      }
      case _ => None
    }
  }

  private def extendedAxioms(expr: Expression): List[String] = {
    expr match {
      case Box(p, _) => p match {
        // @todo diamond duals
        case ODESystem(_:AtomicODE,True)   => odeList :+ "DE differential effect"
        case ODESystem(_:AtomicODE,domain) => "DW differential weakening" :: odeList ++ List("DE differential effect")
        case ODESystem(_:DifferentialProduct,True)   => odeList :+ "DE differential effect (system)"
        case ODESystem(_:DifferentialProduct,domain) => "DW differential weakening" :: odeList ++ List("DE differential effect (system)")
        case _: Loop => "[*] iterate" :: Nil
        case _ => Nil
      }
      case And(f, _)   if f == True => "true&" :: Nil
      case And(_, g)   if g == True => "&true" :: Nil
      case Imply(f, _) if f == True => "true->" :: Nil
      case Imply(_, g) if g == True => "->true" :: Nil
      //@todo could add And(False, _) etc ....
      case _ => Nil
    }
//@todo use this
//      case ODESystem(_:AtomicODE,True)   => if (post.isInstanceOf[DifferentialFormula]) "DE differential effect" +: odeList else odeList :+ "DE differential effect"
//      case ODESystem(_:AtomicODE,domain) => if (post.isInstanceOf[DifferentialFormula]) "DE differential effect" :: "DW differential weakening" :: odeList else "DW differential weakening" :: odeList ++ List("DE differential effect")
//      case ODESystem(_:DifferentialProduct,True)   => if (post.isInstanceOf[DifferentialFormula]) "DE differential effect (system)" +: odeList else odeList :+ "DE differential effect (system)"
//      case ODESystem(_:DifferentialProduct,domain) => if (post.isInstanceOf[DifferentialFormula]) "DE differential effect (system)" :: "DW differential weakening" :: odeList else "DW differential weakening" :: odeList ++ List("DE differential effect (system)")
  }
  /** Return the (derived) axiom names that simplify the expression expr with simpler ones first */
  def axiomsFor(expr: Expression, exhaustive: Boolean = false): List[String] =
    preferredAxiom(expr).toList ++ (if(exhaustive) extendedAxioms(expr) else Nil)

  def propositionalRuleFor(pos:Position, expr: Expression):Option[String] = {
    if (!pos.isTopLevel) {
      None
    }
    (expr, pos.isAnte) match {
      case (_: Not, true) => Some("NotL")
      case (_: Not, false) => Some("NotR")
      case (_: And, true) => Some("AndL")
      case (_: And, false) => Some("AndR")
      case (_: Or, true) => Some("OrL")
      case (_: Or, false) => Some("OrR")
      case (_: Imply, true) => Some("ImplyL")
      case (_: Imply, false) => Some("ImplyR")
      case (_: Equiv, true) => Some("EquivL")
      case (_: Equiv, false) => Some("EquivR")
      case (_: Forall, false) => Some("AllR")
      case (_: Exists, true) => Some("ExistsL")
      case _ => None
    }
  }
  
  private def extendedTacticsFor(pos:Position, expr: Expression): List[String] = {
    if (!pos.isTopLevel) {
      Nil
    } else {
      expr match {
        case Box(p, _) => p match {
          case _: Loop => "loop" :: Nil
          case _: ODESystem => "diffInvariant" :: "diffInd" :: Nil
          case _ => Nil
        }
      }
    }
  }
  
  /** Return the (non-axiom) tactic names that simplify the expression expr with simpler ones first */
  def tacticsFor(pos:Position, expr: Expression): List[String] = {
    propositionalRuleFor(pos, expr).toList ++ extendedTacticsFor(pos, expr)
  }
}