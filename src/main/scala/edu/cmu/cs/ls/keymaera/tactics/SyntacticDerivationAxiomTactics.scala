package edu.cmu.cs.ls.keymaera.tactics

//@todo minimize imports

import edu.cmu.cs.ls.keymaera.core
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.ExpressionTraversalFunction
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
 * There is some code duplication in this file, but I figured it is probably not the end of the for such fundamental
 * tactics to be implement on a stand-alone basis.
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
   *   (p | q)' <-> ((p') & (q'))
   * End.
   */
  def OrDerivativeT = new AxiomTactic("|' derive or","|' derive or") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Or(_,_)) => true
      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
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
          val g = And(FormulaDerivative(p), FormulaDerivative(q))
          val axiomInstance = Equiv(f,g)

          val subst = Substitution(List(
            SubstitutionPair(aP, p),
            SubstitutionPair(aQ, q)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case And(FormulaDerivative(p), FormulaDerivative(q)) => {
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
      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
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
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = Variable("s",None,Real)      //@todo not sure...
      val aT = Variable("t",None,Real)

      f match {
        case FormulaDerivative(Equals(eqSort, s, t)) => {
          val g = Equals(eqSort, Derivative(s.sort, s), Derivative(t.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
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
            SubstitutionPair(aT, t)
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
  def GreaterEqualDerivativeT = new AxiomTactic(">=' derive >=", ">=' derive >=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => {
        true
      }
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = Variable("s",None,Real)      //@todo not sure...
      val aT = Variable("t", None, Real)

      f match {
        case FormulaDerivative(GreaterEqual(eqSort, s, t)) => {
          val g = GreaterEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(GreaterEqual(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
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

  /*
   * Axiom ">' derive >".
   *   (s > t)' <-> ((s') >= (t'))
   * End.
   */
  def GreaterThanDerivativeT = new AxiomTactic(">' derive >", ">' derive >") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) => {
        true
      }
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = Variable("s",None,Real)      //@todo not sure...
      val aT = Variable("t", None, Real)

      f match {
        case FormulaDerivative(GreaterThan(eqSort, s, t)) => {
          val g = GreaterEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(GreaterThan(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def GreaterThanDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterThanDerivativeT(p)
  }

  def GreaterThanDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = GreaterThanDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "<=' derive <=".
   *   (s <= t)' <-> ((s') <= (t'))
   * End.
   */
  def LessEqualDerivativeT = new AxiomTactic("<=' derive <=", "<=' derive <=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) => {
        true
      }
      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = Variable("s",None,Real)      //@todo not sure...
      val aT = Variable("t", None, Real)

      f match {
        case FormulaDerivative(LessEqual(eqSort, s, t)) => {
          val g = LessEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(LessEqual(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def LessEqualDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = LessEqualDerivativeT(p)
  }

  def LessEqualDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = LessEqualDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////



  /*
   * Axiom "<' derive <".
   *   (s < t)' <-> ((s') <= (t'))
   * End.
   */
  def LessThanDerivativeT = new AxiomTactic("<' derive <", "<' derive <") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(LessThan(eqSort, s, t)) => {
        true
      }
      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = Variable("s",None,Real)      //@todo not sure...
      val aT = Variable("t", None, Real)

      f match {
        case FormulaDerivative(LessThan(eqSort, s, t)) => {
          val g = LessEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(LessThan(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def LessThanDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(LessThan(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = LessThanDerivativeT(p)
  }

  def LessThanDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = LessThanDerivativeT(p)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /*
   * Axiom "!=' derive !=".
   *   (s != t)' <-> ((s') = (t'))
   * End.
   */
  def NotEqualsDerivativeT = new AxiomTactic("!=' derive !=", "!=' derive !=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) => {
        true
      }
      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
        true
      }
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && p.inExpr == HereP && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula, ax: Formula, pos: Position):
    Option[(Formula, Formula, Substitution, Option[PositionTactic], Option[PositionTactic])] = {
      val aS = Variable("s",None,Real)      //@todo not sure...
      val aT = Variable("t", None, Real)

      f match {
        case FormulaDerivative(NotEquals(eqSort, s, t)) => {
          val g = Equals(eqSort, Derivative(s.sort, s), Derivative(t.sort, t))
          val axiomInstance = Equiv(f, g)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
        case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          assert(sSort == tSort, "There should be a non-ambiguous way of deciding what the sort of the outer term will be")
          val sort = sSort

          val g = FormulaDerivative(NotEquals(sSort, s, t))
          val axiomInstance = Equiv(g,f)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(ax, axiomInstance, subst, None, None)
        }
      }
    }
  }

  def NotEqualsDerivativeAtomizeT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) => true
    }
    override def apply(p: Position): Tactic = NotEqualsDerivativeT(p)
  }

  def NotEqualsDerivativeAggregateT = new PositionTactic("=' derive = Atomize") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
    }
    override def apply(p: Position): Tactic = NotEqualsDerivativeT(p)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section 2. Syntactic Total Derivation of Terms.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo throughout this section, the <- direction applicability is disabled in comments because the Atomize/Aggregate thing isn't possible to implement without position tactics for terms.
  //@todo when re-enabliong these applies lines, uncomment and re-run the relevant tests in SyntacticDerivationTests

  /*
   * Axiom "-' derive neg".
   *   (-s)' = -(s')
   * End.
   */
  def NegativeDerivativeT = new TermAxiomTactic("-' derive neg","-' derive neg") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(_,Neg(_,_)) => true
//      case Neg(_,Derivative(_,_)) => true //@todo add term position derivatives and re-enable this case, then uncomment test cases.
      case _ => false
    }

    override def constructInstanceAndSubst(t: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      t match {
        case Derivative(dSort, Neg(nSort, s)) => {
          val sort = nSort; assert(nSort == dSort)

          val aS = Variable("s", None, sort)

          val subst = Substitution(List(
            SubstitutionPair(aS, s)
          ))

          val right = Neg(sort, Derivative(sort, s))
          val axiomInstance = Equals(sort, t, right)

          Some(axiomInstance, subst)
        }
        case Neg(nSort, Derivative(dSort, s)) => {
          val sort = nSort; assert(nSort == dSort)

          val aS = Variable("s", None, sort)

          val subst = Substitution(List(
            SubstitutionPair(aS, s)
          ))

          val left = Derivative(sort, Neg(sort, s))
          val axiomInstance = Equals(sort, left, t)

          Some(axiomInstance, subst)
        }
      }
    }
  }

  /*
   * Axiom "+' derive sum".
   *  (s + t)' = (s') + (t')
   * End.
   */
  def AddDerivativeT = new TermAxiomTactic("+' derive sum","+' derive sum") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(_, Add(_, s, t)) => true
//      case Add(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      term match {
        case Derivative(dSort, Add(aSort, s, t)) => {
          val sort = aSort; assert(dSort == aSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val right = Add(sort, Derivative(sort, s), Derivative(sort, t))
          val axiomInstance = Equals(sort, term, right)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
        case Add(aSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          val sort = aSort; assert(aSort == sSort && sSort == tSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val left = Derivative(sort, Add(sort, s, t))
          val axiomInstance = Equals(sort, left, term)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
      }
    }
  }

  /*
   * Axiom "-' derive minus".
   *   (s - t)' = (s') - (t')
   * End.
 */
  def SubtractDerivativeT = new TermAxiomTactic("-' derive minus","-' derive minus") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(_, Subtract(_, s, t)) => true
//      case Subtract(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      term match {
        case Derivative(dSort, Subtract(aSort, s, t)) => {
          val sort = aSort; assert(dSort == aSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val right = Subtract(sort, Derivative(sort, s), Derivative(sort, t))
          val axiomInstance = Equals(sort, term, right)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
        case Subtract(aSort, Derivative(sSort, s), Derivative(tSort, t)) => {
          val sort = aSort; assert(aSort == sSort && sSort == tSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val left = Derivative(sort, Subtract(sort, s, t))
          val axiomInstance = Equals(sort, left, term)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
      }
    }
  }

  /*
Axiom "*' derive product".
  (s * t)' = ((s')*t) + (s*(t'))
End.
   */
  def MultiplyDerivativeT = new TermAxiomTactic("*' derive product","*' derive product") {
    override def applies(t: Term): Boolean = t match {
      case Derivative(_, Multiply(_, s, t)) => true
      case Add(_, Multiply(_,Derivative(_,_), _),Multiply(_,_,Derivative(_))) => true
//      case Subtract(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      term match {
        case Derivative(dSort, Multiply(aSort, s, t)) => {
          val sort = aSort; assert(dSort == aSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val right = Add(sort, Multiply(sort, Derivative(sort, s), t), Multiply(sort, s, Derivative(sort, t)))
          val axiomInstance = Equals(sort, term, right)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
        case Add(aSort, Multiply(mSort,Derivative(_,s),t), Multiply(_,_,_)) => {
          val sort = aSort; assert(aSort == mSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val left = Derivative(sort, Multiply(sort, s, t))
          val axiomInstance = Equals(sort, left, term)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
      }
    }
  }

  /*
  Axiom "/' derive quotient".
  (s / t)' = (((s')*t) - (s*(t'))) / (t^2)
End.
   */
  def DivideDerivativeT = new TermAxiomTactic("/' derive quotient","/' derive quotient") {
    override def applies(term: Term): Boolean = term match {
      case Derivative(_, Divide(_, s, t)) => true
//      case Divide(dSort, Subtract(_, Multiply(_,Derivative(_,s), _),Multiply(_,_,Derivative(_))), Exp(_, t, Number(_))) => true
      case _ => throw new Exception("doesn't apply to "  + term.getClass())
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      term match {
        case Derivative(dSort, Divide(aSort, s, t)) => {
          val sort = aSort; assert(dSort == aSort)

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val right = Divide(dSort,
            Subtract(sort,
              Multiply(sort,Derivative(sort,s), t),
              Multiply(sort,s,Derivative(sort,t))
            ),
            Exp(sort, t, Number(2))
          )
          val axiomInstance = Equals(sort, term, right)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
        case Divide(dSort, Exp(_, t, Number(_)), Subtract(_, Multiply(_,Derivative(_,s), _),Multiply(_,_,Derivative(_)))) => {
          val sort = dSort

          val aS = Variable("s", None, sort)
          val aT = Variable("t", None, sort)

          val left = Derivative(Real, Divide(Real, s, t))
          val axiomInstance = Equals(sort, left, term)

          val subst = Substitution(List(
            SubstitutionPair(aS, s),
            SubstitutionPair(aT, t)
          ))

          Some(axiomInstance, subst)
        }
      }
    }
  }


  //So that when this gets refactored we're not stuck changing a bunch of stuff.
  def NegativeDerivativeAtomizeT = NegativeDerivativeT
  def AddDerivativeAtomizeT      = AddDerivativeT
  def SubtractDerivativeAtomizeT = SubtractDerivativeT
  def MultiplyDerivativeAtomizeT = MultiplyDerivativeT
  def DivideDerivativeAtomizeT   = DivideDerivativeT

  val termDerivativeTactics : List[TermAxiomTactic] =
    NegativeDerivativeAtomizeT ::
      AddDerivativeAtomizeT ::
      SubtractDerivativeAtomizeT ::
      MultiplyDerivativeAtomizeT ::
      DivideDerivativeAtomizeT ::
      Nil

  def termSyntacticDerivationT = new PositionTactic("Total Syntactic Derivation of Terms") {

    def applies(s: Sequent, p: Position): Boolean = {
      def tacticApplies(tactic : TermAxiomTactic) = theTraversal(s(p), tactic) match {
        case Some(_) => true
        case None => false
      }

      termDerivativeTactics.foldLeft(true)((b, tat : TermAxiomTactic) => {
        tacticApplies(tat) && b
      })
    }

    /**
     * @todo this code is kind of complicated and probably deserves some refactoring.
     */
    override def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        /**
         * Returns a list of positions, together with the first applicable tactic at each position.
         */
        def firstApplicableTacticForEachPosition(seq : IndexedSeq[Formula]) : Seq[Option[(TermAxiomTactic, Int, PosInExpr)]] = {
          seq.zipWithIndex.map(p => {
            val formula = p._1
            val index: Int = p._2

            val tacticAndPos : Option[(TermAxiomTactic, PosInExpr)] = {
              //Check each of the tactics to determine if any apply.
              def findApplicablePosInFormula(tactic : TermAxiomTactic) : Option[PosInExpr] = {
                theTraversal(formula, tactic) match {
                  case Some((posInExpr, term)) => Some(posInExpr)
                  case None => None
                }
              }

              val applicableTactics = termDerivativeTactics.map(t => findApplicablePosInFormula(t) match {
                case Some(posInExpr) => Some(t,posInExpr)
                case None => None
              }).filter(_.isDefined)

              if(applicableTactics.length == 0) {
                None
              }
              else {
                applicableTactics.last //just the first applicable tactic.
              }
            }

            tacticAndPos match {
              case Some((tactic:TermAxiomTactic, posInExpr:PosInExpr)) => Some(tactic, index, posInExpr)
              case None => None
            }
          }).filter(_.isDefined)
        }

        val antePositions = firstApplicableTacticForEachPosition(node.sequent.ante)
        if(antePositions.length > 0) {
          antePositions.last match {
            case Some((tactic:TermAxiomTactic, anteIndex, posInExpr)) => Some(tactic(AntePosition(anteIndex, posInExpr)))
            case _ => None
          }
        }
        else {
          val succPositions = firstApplicableTacticForEachPosition(node.sequent.succ)
          if(succPositions.length > 0) {
            succPositions.last match {
              case Some((tactic:TermAxiomTactic, succIndex, posInExpr)) => Some(tactic(SuccPosition(succIndex, posInExpr)))
              case _ => None
            }
          }
          else {
            None
          }
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }

    def theTraversal(expression : Expr, tactic : TermAxiomTactic) : Option[(PosInExpr, Term)] = {
      val traversal = new ExpressionTraversalFunction {
        var mPosition : Option[PosInExpr] = None
        var mTerm : Option[Term] = None

        override def preT(p:PosInExpr, t:Term) = {
          if(tactic.applies(t)) {
            mPosition = Some(p);
            mTerm = Some(t);
            Left(Some(ExpressionTraversal.stop)) //stop once we find one applicable location.
          }
          else{
            Left(None)
          }
        }
      }

      expression match {
        case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
        case expression : Term => ExpressionTraversal.traverse(traversal, expression)
        case expression : Program => ExpressionTraversal.traverse(traversal, expression)
        case _ => ???
      }

      (traversal.mPosition, traversal.mTerm) match {
        case (Some(p:PosInExpr), Some(t:Term)) => Some((p,t))
        case (None,None) => None
        case _ => ???
      }
    }

  }

  /**
   * The "mater" syntactic derivation tactic.
   *
   */
  def SyntacticDerivationT = new PositionTactic("Syntactic Derivation") {
    override def applies(s: Sequent, p: Position): Boolean = s(p) match {
      case FormulaDerivative(_) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = {
      ((AndDerivativeAtomizeT(p) ~
        OrDerivativeAtomizeT(p) ~
        EqualsDerivativeAtomizeT(p) ~
        GreaterEqualDerivativeAtomizeT(p) ~
        GreaterThanDerivativeAtomizeT(p) ~
        LessEqualDerivativeAtomizeT(p) ~
        LessThanDerivativeAtomizeT(p) ~
        NotEqualsDerivativeAtomizeT(p))*) ~ (termSyntacticDerivationT(p) *)
    }
  }
}
