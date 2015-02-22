package edu.cmu.cs.ls.keymaera.tactics

//@todo minimize imports

import edu.cmu.cs.ls.keymaera.core
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.AxiomCloseT
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl.hideT
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

/**
 * @todo The tactics do not actually do this -- the AxiomNameT only got the "correct" direction in the new implementation.
 *       The atomize and aggregate tactics are out-of-date.
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
 * Axiom "->' derive imply".
 *   (p -> q)' <-> (!p | q)'
 * End.
 */
  def ImplyDerivativeT = new DerivativeAxiomInContextTactic("->' derive imply", "->' derive imply") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Imply(_,_))              => true
      //      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(Imply(p, q)) => {
        val g = FormulaDerivative(Or(Not(p), q))
        val axiomInstance = Equiv(f,g)

        Some(g, None)
      }
      case _ => None
    }
  }


  /*
   * Axiom "&' derive and".
   *   (p & q)' <-> ((p') & (q'))
   * End.
   */
  def AndDerivativeT = new DerivativeAxiomInContextTactic("&' derive and", "&' derive and") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(And(_,_))              => true
//      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(And(p,q)) => {
        Some(And(FormulaDerivative(p), FormulaDerivative(q)), None)
      }
      case _ => None
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
  def OrDerivativeT = new DerivativeAxiomInContextTactic("|' derive or","|' derive or") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(Or(_,_)) => true
//      case And(FormulaDerivative(_), FormulaDerivative(_)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(Or(p,q)) => Some(And(FormulaDerivative(p), FormulaDerivative(q)), None)
      case _ => None
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
  def EqualsDerivativeT = new DerivativeAxiomInContextTactic("=' derive =", "=' derive =") {
    override def applies(f: Formula): Boolean = {
      f match {
        case FormulaDerivative(Equals(eqSort, s, t)) => true
        //      case Equals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
        case _ => false
      }
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    /**
     * This method constructs the desired result before the renaming.
     *
     * @param f the formula that should be rewritten
     * @return Desired result before executing the renaming
     */
    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(Equals(eqSort, s, t)) => Some(Equals(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), None)
      case _ => None
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
  def GreaterEqualDerivativeT = new DerivativeAxiomInContextTactic(">=' derive >=", ">=' derive >=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => true
//      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }


    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(GreaterEqual(eqSort, s, t)) => Some(GreaterEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), None)
      case _ => None
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
  def GreaterThanDerivativeT = new DerivativeAxiomInContextTactic(">' derive >", ">' derive >") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) => true
//      case GreaterEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(GreaterThan(eqSort, s, t)) => Some(GreaterEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), None)
      case _ => None
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
  def LessEqualDerivativeT = new DerivativeAxiomInContextTactic("<=' derive <=", "<=' derive <=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) => true
//      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f : Formula) = f match {
      case FormulaDerivative(LessEqual(eqSort, s, t)) => Some(LessEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), None)
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
  def LessThanDerivativeT = new DerivativeAxiomInContextTactic("<' derive <", "<' derive <") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(LessThan(eqSort, s, t)) => true
//      case LessEqual(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => {println(this.getClass() + " is not applicable to: " + f); false}
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(LessThan(eqSort, s, t)) => Some( LessEqual(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), None)
      case _ => None
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
  def NotEqualsDerivativeT = new DerivativeAxiomInContextTactic("!=' derive !=", "!=' derive !=") {
    override def applies(f: Formula): Boolean = f match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) => true
//      case NotEquals(eqSort, Derivative(sSort, s), Derivative(tSort, t)) => true
      case _ => false
    }

    override def applies(s: Sequent, p: Position): Boolean = {
      !p.isAnte && super.applies(s, p)
    }

    override def constructInstanceAndSubst(f: Formula) = f match {
      case FormulaDerivative(NotEquals(eqSort, s, t)) => Some(Equals(eqSort, Derivative(s.sort, s), Derivative(t.sort, t)), None)
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

  trait ApplicableAtTerm {
    def applies(t : Term) : Boolean
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

          val aS = Apply(Function("s", None, Unit, sort), Nothing)
          val aT = Apply(Function("t", None, Unit, sort), Nothing)

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

          val aS = Apply(Function("s", None, Unit, sort), Nothing)
          val aT = Apply(Function("t", None, Unit, sort), Nothing)

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
//      case Add(_, Multiply(_,Derivative(_,_), _),Multiply(_,_,Derivative(_))) => true
//      case Subtract(_, Derivative(_,_), Derivative(_,_)) => true //@todo need tests when added.
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      term match {
        case Derivative(dSort, Multiply(aSort, s, t)) => {
          val sort = aSort; assert(dSort == aSort)

          val aS = Apply(Function("s", None, Unit, sort), Nothing)
          val aT = Apply(Function("t", None, Unit, sort), Nothing)

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

          val aS = Apply(Function("s", None, Unit, sort), Nothing)
          val aT = Apply(Function("t", None, Unit, sort), Nothing)

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
      case _ => false
    }

    override def constructInstanceAndSubst(term: Term, ax: Formula, pos: Position): Option[(Formula, Substitution)] = {
      term match {
        case Derivative(dSort, Divide(aSort, s, t)) => {
          val sort = aSort; assert(dSort == aSort)

          val aS = Apply(Function("s", None, Unit, sort), Nothing)
          val aT = Apply(Function("t", None, Unit, sort), Nothing)

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

          val aS = Apply(Function("s", None, Unit, sort), Nothing)
          val aT = Apply(Function("t", None, Unit, sort), Nothing)

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

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof rule implementations
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //
  def SyntacticDerivationRulesT : Tactic = (SearchTacticsImpl.locateTerm(ConstantDerivativeT) *) ~ (SearchTacticsImpl.locateTerm(MonomialDerivativeT) *)
  def ConstantDerivativeT : PositionTactic = new PositionTactic("Monomial Derivative") {
    /**
     *
     * @param p The position of a term.
     * @return true iff the position exists in the sequent and is a monomial.
     */
    override def applies(s: Sequent, p: Position): Boolean = {
      getApplicableTerm(s,p).isDefined
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val term = getApplicableTerm(node.sequent, p).getOrElse(throw new Exception("MonomialDerivative.applies is incorrect."))

        val newHypothesisCutLocation = AntePosition(node.sequent.ante.length, HereP)

        val buildConstantEqualityHypothesis : Tactic = new ApplyRule(new DeriveConstant(term)) {
          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }

        val equalityRewrite : Tactic = new ApplyRule(new EqualityRewriting(newHypothesisCutLocation, p)) {
          override def applicable(node: ProofNode): Boolean = true //@todo?
        }

        //Build the equality, put it to work, and dispense after use. Also dispense of the current position, because we'll now have a new sequent.
        val topLevelPosition = if(p.isAnte) {
          new AntePosition(p.getIndex)
        }
        else {
          new SuccPosition(p.getIndex)
        }

        Some(buildConstantEqualityHypothesis & equalityRewrite & hideT(newHypothesisCutLocation) & hideT(topLevelPosition))
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    def getApplicableTerm(sequent : Sequent, position : Position) : Option[Term] = {
      var foundTerm : Option[Term] = None

      val fn = new ExpressionTraversalFunction {
        override def preT(pos : PosInExpr, t : Term) = {
          if(pos == position.inExpr && isConstant(t)) {
            foundTerm = Some(t)
            Left(Some(ExpressionTraversal.stop))
          }
          else {
            Left(None)
          }
        }
      }
      ExpressionTraversal.traverse(fn, sequent(position))
      foundTerm
    }

    def isConstant(term : Term) = term match {
      case Derivative(Real, Number(Real, n)) => true //copied from the rule itself.
      case _ => false
    }
  }

  def MonomialDerivativeT : PositionTactic = new PositionTactic("Monomial Derivative") {
    /**
     *
     * @param p The position of a term.
     * @return true iff the position exists in the sequent and is a monomial.
     */
    override def applies(s: Sequent, p: Position): Boolean = {
      getApplicableTerm(s,p).isDefined
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val term = getApplicableTerm(node.sequent, p).getOrElse(throw new Exception("MonomialDerivative.applies is incorrect."))

        val newHypothesisCutLocation = AntePosition(node.sequent.ante.length, HereP)

        val buildMonomialEqualityHypothesis : Tactic = new ApplyRule(new DeriveMonomial(term)) {
          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
        }

        val equalityRewrite : Tactic = new ApplyRule(new EqualityRewriting(newHypothesisCutLocation, p)) {
          override def applicable(node: ProofNode): Boolean = true //@todo?
        }

        //Build the equality, put it to work, and dispense after use. Also dispense of the current position, because we'll now have a new sequent.
        val topLevelPosition = if(p.isAnte) {
          new AntePosition(p.getIndex)
        }
        else {
          new SuccPosition(p.getIndex)
        }

        Some(buildMonomialEqualityHypothesis & equalityRewrite & hideT(newHypothesisCutLocation) & hideT(topLevelPosition))
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    def getApplicableTerm(sequent : Sequent, position : Position) : Option[Term] = {
      var foundTerm : Option[Term] = None

      val fn = new ExpressionTraversalFunction {
        override def preT(pos : PosInExpr, t : Term) = {
          if(pos == position.inExpr && isMonomial(t)) {
            foundTerm = Some(t)
            Left(Some(ExpressionTraversal.stop))
          }
          else {
            Left(None)
          }
        }
      }
      ExpressionTraversal.traverse(fn, sequent(position))
      foundTerm
    }

    def isMonomial(term : Term) = term match {
      case Derivative(Real, Exp(Real, base, Number(Real, n))) => true //copied from the rule itself.
      case _ => false
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Atomize for Term Tactics @todo
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //@todo So that when this gets refactored we're not stuck changing a bunch of stuff.
  def NegativeDerivativeAtomizeT = NegativeDerivativeT
  def AddDerivativeAtomizeT      = AddDerivativeT
  def SubtractDerivativeAtomizeT = SubtractDerivativeT
  def MultiplyDerivativeAtomizeT = MultiplyDerivativeT
  def DivideDerivativeAtomizeT   = DivideDerivativeT


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for term syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /**
   * This list of *all* the atomizing TermAxiomTactics is used in the implementation of wrapper tactics.
   */
  val termDerivativeTactics : List[TermAxiomTactic] =
    NegativeDerivativeAtomizeT ::
      AddDerivativeAtomizeT ::
      SubtractDerivativeAtomizeT ::
      MultiplyDerivativeAtomizeT ::
      DivideDerivativeAtomizeT ::
      Nil

  val formulaDerivativeTactics : List[DerivativeAxiomInContextTactic] =
    AndDerivativeT          ::
    OrDerivativeT           ::
    EqualsDerivativeT       ::
    GreaterEqualDerivativeT ::
    GreaterThanDerivativeT  ::
    LessEqualDerivativeT    ::
    LessThanDerivativeT     ::
    NotEqualsDerivativeT    ::
    ImplyDerivativeT      ::
    Nil

  /**
   * Finds a position in ``expression" where ``tactic" is applicable, or else returns None if ``tactic" is never applicable
   * in subexpressions of ``expression".
   *
   * This is used in the implementation of wrapper tactics.
   * @param expression
   * @param tactic
   */
  def findApplicablePositionForTermAxiom(expression : Expr, tactic : TermAxiomTactic) : Option[(PosInExpr, Term)] = {
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

  /**
   * The wrapper tactic for total synactic derivation of *terms*.
   * In a single step, this tactic finds *one* location where *one* of the atomizing term derivative rewrites applies,
   * and then applies that tactic.
   */
  def TermSyntacticDerivationT = new PositionTactic("Total Syntactic Derivation of Terms") {
    def applies(s: Sequent, p: Position): Boolean = {
      def tacticApplies(tactic : TermAxiomTactic) = findApplicablePositionForTermAxiom(s(p), tactic) match {
        case Some(_) => true
        case None => false
      }

      termDerivativeTactics.foldLeft(false)((b, tat : TermAxiomTactic) => {
        tacticApplies(tat) || b
      })
    }

    /**
     * @todo this code is kind of complicated and probably deserves some refactoring.
     *       The formula version is much cleaner .
     */
    override def apply(pos: Position): Tactic = new ConstructionTactic(name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        /**
         * Returns a list of positions, together with the first applicable tactic at each position.
         */
        def firstApplicableTacticForEachPosition(seq : IndexedSeq[Formula]) : Seq[(TermAxiomTactic, Int, PosInExpr)] = {
          seq.zipWithIndex.map(p => {
            val formula = p._1
            val index: Int = p._2

            val tacticAndPos : Option[(TermAxiomTactic, PosInExpr)] = {
              //Check each of the tactics to determine if any apply.
              def findApplicablePosInFormula(tactic : TermAxiomTactic) : Option[PosInExpr] = {
                findApplicablePositionForTermAxiom(formula, tactic) match {
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
          }).filter(_.isDefined).map(_.get)
        }

        //First check the ante for any applicable tactics and positions; if there is one, return that one.
        //Else move on to the succ and so the same thing.
        val antePositions = firstApplicableTacticForEachPosition(node.sequent.ante)
        if(antePositions.length > 0) {
          val elmt      = antePositions.last
          val tactic    = elmt._1
          val anteIndex = elmt._2
          val posInExpr = elmt._3
          val position  = AntePosition(anteIndex, posInExpr)

          Some(tactic(position))
        }
        else {
          val succPositions = firstApplicableTacticForEachPosition(node.sequent.succ)
          if(succPositions.length > 0) {
            val elmt      = succPositions.last
            val tactic    = elmt._1
            val anteIndex = elmt._2
            val posInExpr = elmt._3
            Some(tactic(SuccPosition(anteIndex, posInExpr)))
          }
          else {
            None
          }
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)
    }



  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for formula syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  def FormulaSyntacticDerivationT = new PositionTactic("Formula Syntactic Derivation") {
    override def applies(s: Sequent, p: Position): Boolean = {
      formulaDerivativeTactics.map(t => findApplicablePositionForFormulaDerivativeAxiom(s(p), t) match {
        case Some(_) => true
        case None    => false
      }).reduce(_ | _)
    }

    override def apply(p:Position) : Tactic = new ConstructionTactic("Formula Syntactic Derivation") {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        //I think this will be easier to read than the mapping approach.
        for((anteF : Formula, idx : Int) <- node.sequent.ante.zipWithIndex) {
          val applicableTactics : Seq[(PositionTactic, PosInExpr)] =
            formulaDerivativeTactics.map(t => (t, findApplicablePositionForFormulaDerivativeAxiom(anteF, t))).filter(_._2.isDefined).map(p => (p._1, p._2.get._1))
          if(applicableTactics.length > 0) {
            val tactic    = applicableTactics.last._1
            val posInExpr = applicableTactics.last._2
            return Some(tactic(AntePosition(idx, posInExpr)));
          }
        }

        for((succF, idx : Int) <- node.sequent.succ.zipWithIndex) {
          val applicableTactics : Seq[(PositionTactic, PosInExpr)] =
            formulaDerivativeTactics.map(t => (t, findApplicablePositionForFormulaDerivativeAxiom(succF, t))).filter(_._2.isDefined).map(p => (p._1, p._2.get._1))
          if(applicableTactics.length > 0) {
            println("Found an applicable tactic!")
            val tactic    = applicableTactics.last._1
            val posInExpr = applicableTactics.last._2
            println(tactic.name + " " + idx + " " + posInExpr.toString())
            return Some(tactic(SuccPosition(idx, posInExpr)));
          }
        }

        return None;
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }

    def findApplicablePositionForFormulaDerivativeAxiom(expression : Expr, tactic : DerivativeAxiomInContextTactic) : Option[(PosInExpr, Formula)] = {
      val traversal = new ExpressionTraversalFunction {
        var mPosition : Option[PosInExpr] = None
        var mFormula : Option[Formula]    = None

        override def preF(p:PosInExpr, f:Formula) = {
          if(tactic.applies(f)) {
            println("Found an applicable tactic: " + tactic.name + " for formila " + f)
            mPosition = Some(p);
            mFormula  = Some(f);

            Left(Some(ExpressionTraversal.stop)) //stop once we find one applicable location.
          }
          else{
            Left(None)
          }
        }
      }

      expression match {
        case expression : Formula => ExpressionTraversal.traverse(traversal, expression)
        case expression : Term    => ExpressionTraversal.traverse(traversal, expression)
        case expression : Program => ExpressionTraversal.traverse(traversal, expression)
        case _ => ???
      }

      (traversal.mPosition, traversal.mFormula) match {
        case (Some(p:PosInExpr), Some(f:Formula)) => Some((p,f))
        case (None,None) => None
        case _ => ???
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Section: Wrapper tactic for syntactic derivation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def SyntacticDerivationT = new PositionTactic("Formula Syntactic Derivation") {
    override def applies(s: Sequent, p: Position): Boolean = TermSyntacticDerivationT.applies(s,p) | FormulaSyntacticDerivationT.applies(s,p)

    override def apply(p: Position): Tactic = (FormulaSyntacticDerivationT(p) *) ~ (TermSyntacticDerivationT(p) *)
  }


//  def SyntacticDerivationInContextT(position : Position) : Tactic = ((new TacticInContextT(SyntacticDerivationT(position)) {
//    override def applies(f: Formula) = f match {
//      case FormulaDerivative(_) => true
//      case _ => false
//    }
//
//    override def constructInstanceAndSubst(f: Formula): Option[(Formula, Option[PositionTactic])] = f match {
//      case Derivative(f) => Some(phi, None)
//      case _ => None
//    }
//  })(position) ~ SearchTacticsImpl.locateSucc(ImplyRightT) ~ AxiomCloseT)
}
