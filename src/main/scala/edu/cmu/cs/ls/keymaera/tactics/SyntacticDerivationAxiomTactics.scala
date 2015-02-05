package edu.cmu.cs.ls.keymaera.tactics

//@todo minimize imports
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

/**
 * Contains the axiom tactics and wrapper tactics for syntactic derivation of formulas and terms.
 * The axiom tactics go both directions; for this reason, there are three tactics per axiom:
 *    - The AxiomNameT tactic is the actual axiom.
 *    - The AxiomNameAtomizeT tactic derives in the typical left-to-right direction; that is, it takes a derivative
 *      term and constructs a non-derivative term.
 *    - The AxiomNameAggregateT tactic goes in the typical right-to-left direction.
 *
 * Created by nfulton on 2/4/15.
 */
object SyntacticDerivationAxiomTactics {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 1: "Derivatives" of Formulas
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  /*
   * Axiom "&' derive and".
   *   (p & q)' <-> ((p') & (q'))
   * End.
   */
  def AndDerivativeT = new AxiomTactic("&' derive and", "&' derive and") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(And(_,_))              => true
      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aP  = PredicateConstant("p") //@todo not sure if this is correct.
      val aQ  = PredicateConstant("q")

      f match {
        case FormulaDerivative(And(p,q)) => {
          val g = And(FormulaDerivative(p), FormulaDerivative(q))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aP, p),
            SubstitutionPair(aQ, q)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case And(FormulaDerivative(p), FormulaDerivative(q)) => {
          val g = FormulaDerivative(And(p,q))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aP, p),
            SubstitutionPair(aQ, q)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def AndDerivativeAtomizeT = new PositionTactic("&' derive and Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && (s(p) match {
        case FormulaDerivative(And(_,_)) => true
        case _ => false
      })
    }

    override def apply(p: Position): Tactic = AndDerivativeT(p)
  }

  def AndDerivativeAggregateT = new PositionTactic("&' derive and Aggregate") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _                                               => false
    })

    override def apply(p: Position): Tactic = AndDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "|' derive or".
   *   (p | q)' <-> ((p') | (q'))
   * End.
   */
  def OrDerivativeT = new AxiomTactic("|' derive or","|' derive or") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Or(_,_)) => true
      case Or(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aP = PredicateConstant("p") //@todo not sure if this is correct.
      val aQ = PredicateConstant("q")

      f match {
        case FormulaDerivative(Or(p,q)) => {
          val g = Or(FormulaDerivative(p), FormulaDerivative(q))
          val axiomInstance = Equiv(f,g)

          val subst = Substitution(List(
            SubstitutionPair(aP, p),
            SubstitutionPair(aQ, q)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case Or(FormulaDerivative(p), FormulaDerivative(q)) => {
          val g = FormulaDerivative(Or(p,q))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aP, p),
            SubstitutionPair(aQ, q)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def OrDerivativeAtomizeT = new PositionTactic("|' derive or\",\"|' derive or Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case FormulaDerivative(Or(_,_)) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = OrDerivativeT(p)
  }

  def OrDerivativeAggregateT = new PositionTactic("|' derive or\",\"|' derive or Aggregate") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && (s(p) match {
      case Or(FormulaDerivative(_)) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = OrDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // @TODO A lot of things are missing from the axiom file...

  /*
   * Axiom "=' derive =".
   *   (s = t)' <-> ((s') = (t'))
   * End.
   */
  def EqualsDerivativeT = new AxiomTactic("=' derive =", "=' derive =") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Equals(eqSort, s, t)) => {
        true
      }
      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = ProgramConstant("s")      //@todo not sure...
      val aT = ProgramConstant("t")

      f match {
        case FormulaDerivative(Equals(eqSort, s, t)) => {
          val g = Equals(eqSort, Derivative(s.sort, t), Derivative(s.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aS, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(Equals(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aS, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def EqualsDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(Equals(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = EqualsDerivativeT(p)
  }

  def EqualsDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = EqualsDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom ">=' derive >=".
   *   (s >= t)' <-> ((s') >= (t'))
   * End.
   */
  def GreaterEqualDerivativeT = new AxiomTactic("=' derive =", "=' derive =") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => {
        true
      }
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = ProgramConstant("s")      //@todo not sure...
      val aT = ProgramConstant("t")

      f match {
        case FormulaDerivative(GreaterEqual(eqSort, s, t)) => {
          val g = GreaterEqual(eqSort, Derivative(s.sort, t), Derivative(s.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aS, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(Equals(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aS, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def GreaterEqualDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterEqualDerivativeT(p)
  }

  def GreaterEqualDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterEqualDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
}
