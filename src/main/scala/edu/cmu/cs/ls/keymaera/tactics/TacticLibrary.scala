package edu.cmu.cs.ls.keymaera.tactics

// favoring immutable Seqs

import edu.cmu.cs.ls.keymaera.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaera.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaera.tactics.SearchTacticsImpl._

import scala.collection.immutable.Seq
import scala.collection.immutable.List

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}

import BuiltinHigherTactics._

/**
 * In this object we collect wrapper tactics around the basic rules and axioms.
 *
 * Created by Jan-David Quesel on 4/28/14.
 * @author Jan-David Quesel
 * @author aplatzer
 */
object TacticLibrary {

  object TacticHelper {
    def getFormula(s: Sequent, p: Position): Formula = {
      if (p.inExpr == HereP) {
        if(p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex)
      } else {
        var f: Formula = null
        ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
            f = e
            Left(Some(ExpressionTraversal.stop))
          }
        }), if (p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex))
        if (f != null) f
        else throw new IllegalArgumentException("Sequent " + s + " at position " + p + " is not a formula")
      }
    }

    def getTerm(s: Sequent, p: Position): Term = {
      require(p.inExpr != HereP)
      var t: Term = null
      ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          t = e
          Left(Some(ExpressionTraversal.stop))
        }
      }), if (p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex))
      if (t != null) t
      else throw new IllegalArgumentException("Sequent " + s + " at position " + p + " is not a term")
    }

    def freshIndexInFormula(name: String, f: Formula) =
      if (Helper.names(f).exists(_.name == name)) {
        val vars = Helper.names(f).map(n => (n.name, n.index)).filter(_._1 == name)
        require(vars.size > 0)
        val maxIdx: Option[Int] = vars.map(_._2).foldLeft(None: Option[Int])((acc: Option[Int], i: Option[Int]) =>
          acc match {
            case Some(a) => i match {
              case Some(b) => if (a < b) Some(b) else Some(a)
              case None => Some(a)
            }
            case None => i
          })
        maxIdx match {
          case None => Some(0)
          case Some(a) => Some(a + 1)
        }
      } else None

    def freshIndexInSequent(name: String, s: Sequent) =
      if (Helper.names(s).exists(_.name == name))
        (s.ante.map(freshIndexInFormula(name, _)) ++ s.succ.map(freshIndexInFormula(name, _))).max
      else None

    def freshNamedSymbol[T <: NamedSymbol](t: T, f: Formula): T =
      if (Helper.names(f).exists(_.name == t.name)) t match {
        case Variable(vName, _, vSort) => Variable(vName, freshIndexInFormula(vName, f), vSort).asInstanceOf[T]
        case Function(fName, _, fDomain, fSort) => Function(fName, freshIndexInFormula(fName, f), fDomain, fSort).asInstanceOf[T]
        case _ => ???
      } else t

    def freshNamedSymbol[T <: NamedSymbol](t: T, s: Sequent): T =
      if (Helper.names(s).exists(_.name == t.name)) t match {
        case Variable(vName, _, vSort) => Variable(vName, freshIndexInSequent(vName, s), vSort).asInstanceOf[T]
        case Function(fName, _, fDomain, fSort) => Function(fName, freshIndexInSequent(fName, s), fDomain, fSort).asInstanceOf[T]
        case _ => ???
      } else t
  }

  /*******************************************************************
   * Debug tactics
   *******************************************************************/

  def debugT(s: String): Tactic = new Tactic("Debug") {
    override def applicable(node: ProofNode): Boolean = true

    override def apply(tool: Tool, node: ProofNode): Unit = {
      println("===== " + s + " ==== " + node.sequent + " =====")
      continuation(this, Success, Seq(node))
    }
  }

  /*******************************************************************
   * Major tactics
   *******************************************************************/
 
  /**
   * Default tactics without any invariant generation.
   */
  def master = BuiltinHigherTactics.master _
  def default = BuiltinHigherTactics.master(new NoneGenerate(), exhaustive = true)
  def defaultNoArith = BuiltinHigherTactics.noArith(new NoneGenerate(), exhaustive = true)

  /**
   * Make a step in a proof at the given position (except when decision needed)
   */
  def step : PositionTactic = BuiltinHigherTactics.stepAt(beta = true, simplifyProg = true, quantifiers = true,
    equiv = true)

  /**
   * Tactic that applies propositional proof rules exhaustively.
   */
  // TODO Implement for real. This strategy uses more than propositional steps.
  def propositional = (closeT | locate(stepAt(beta = true, simplifyProg = false,
                                                                   quantifiers = false, equiv = true)))*

  def indecisive(beta: Boolean, simplifyProg: Boolean, quantifiers: Boolean, equiv: Boolean = false) =
    stepAt(beta, simplifyProg, quantifiers, equiv)

  /*******************************************************************
   * Arithmetic tactics
   *******************************************************************/

  /**
   * Tactic for arithmetic.
   * @return The tactic.
   */
  def arithmeticT = ArithmeticTacticsImpl.hideUnnecessaryLeftEqT ~
    ArithmeticTacticsImpl.quantifierEliminationT("Mathematica")

  /**
   * Quantifier elimination.
   */
  def quantifierEliminationT(toolId: String) = ArithmeticTacticsImpl.quantifierEliminationT(toolId)

  /*******************************************************************
   * Elementary tactics
   *******************************************************************/

  def universalClosure(f: Formula): Formula = {
    val vars = Helper.certainlyFreeNames(f)
    if(vars.isEmpty) f else Forall(vars.toList, f)
  }

  def abstractionT: PositionTactic = new PositionTactic("Abstraction") {
    override def applies(s: Sequent, p: Position): Boolean = p.inExpr == HereP && (s(p) match {
      case BoxModality(_, _) => true
      case DiamondModality(_, _) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ApplyRule(new AbstractionRule(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  /*********************************************
   * Basic Tactics
   *********************************************/

  def locateAnte(posT: PositionTactic) = SearchTacticsImpl.locateAnte(posT)
  def locateSucc(posT: PositionTactic) = SearchTacticsImpl.locateSucc(posT)

  /**
   * tactic locating an antecedent or succedent position where PositionTactic is applicable.
   */
  def locate(posT: PositionTactic): Tactic = locateSuccAnte(posT)

  /**
   * tactic locating an antecedent or succedent position where PositionTactic is applicable.
   */
  def locateAnteSucc(posT: PositionTactic): Tactic = locateAnte(posT) | locateSucc(posT)

  /**
   * tactic locating an succedent or antecedent position where PositionTactic is applicable.
   */
  def locateSuccAnte(posT: PositionTactic): Tactic = locateSucc(posT) | locateAnte(posT)

  /*********************************************
   * Propositional Tactics
   *********************************************/

  def AndLeftT = PropositionalTacticsImpl.AndLeftT
  def AndRightT = PropositionalTacticsImpl.AndRightT
  def OrLeftT = PropositionalTacticsImpl.OrLeftT
  def OrRightT = PropositionalTacticsImpl.OrRightT
  def ImplyLeftT = PropositionalTacticsImpl.ImplyLeftT
  def ImplyRightT = PropositionalTacticsImpl.ImplyRightT
  def EquivLeftT = PropositionalTacticsImpl.EquivLeftT
  def EquivRightT = PropositionalTacticsImpl.EquivRightT
  def NotLeftT = PropositionalTacticsImpl.NotLeftT
  def NotRightT = PropositionalTacticsImpl.NotRightT

  def hideT = PropositionalTacticsImpl.hideT
  def cutT(f: Option[Formula]) = PropositionalTacticsImpl.cutT(f)

  def closeT : Tactic = AxiomCloseT | locateSucc(CloseTrueT) | locateAnte(CloseFalseT)
  def AxiomCloseT(a: Position, b: Position) = PropositionalTacticsImpl.AxiomCloseT(a, b)
  def AxiomCloseT = PropositionalTacticsImpl.AxiomCloseT
  def CloseTrueT = PropositionalTacticsImpl.CloseTrueT
  def CloseFalseT = PropositionalTacticsImpl.CloseFalseT

  /*********************************************
   * Equality Rewriting Tactics
   *********************************************/

  def equalityRewriting(eqPos: Position, p: Position, checkDisjoint: Boolean = true) =
    EqualityRewritingImpl.equalityRewriting(eqPos, p, checkDisjoint)
  def equalityRewritingLeft(eqPos: Position) = EqualityRewritingImpl.equalityRewritingLeft(eqPos)
  def equalityRewritingRight(eqPos: Position) = EqualityRewritingImpl.equalityRewritingRight(eqPos)
  def eqLeft(exhaustive: Boolean) = EqualityRewritingImpl.eqLeft(exhaustive)
  def eqRight(exhaustive: Boolean) = EqualityRewritingImpl.eqLeft(exhaustive)

  /*********************************************
   * First-Order Quantifier Tactics
   *********************************************/

  def skolemizeT = FOQuantifierTacticsImpl.skolemizeT
  def decomposeQuanT = FOQuantifierTacticsImpl.decomposeQuanT
  def instantiateQuanT(q: Variable, t: Term) = FOQuantifierTacticsImpl.instantiateT(q, t)

  /*********************************************
   * Hybrid Program Tactics
   *********************************************/

  // TODO replace this with the assignment axiom tactic
  def assignment = HybridProgramTacticsImpl.assignment

  def derivativeAssignment = HybridProgramTacticsImpl.derivativeAssignment

  // axiom wrappers

  // axiomatic version of assignment axiom assignaxiom
  def boxAssignT = HybridProgramTacticsImpl.boxAssignT
  def boxDerivativeAssignT = HybridProgramTacticsImpl.boxDerivativeAssignT
  def assignT = boxAssignT /*@TODO | diamondAssignT*/

  def boxTestT = HybridProgramTacticsImpl.boxTestT
  def boxNDetAssign = HybridProgramTacticsImpl.boxNDetAssign
  def boxSeqT = HybridProgramTacticsImpl.boxSeqT
  def boxInductionT = HybridProgramTacticsImpl.boxInductionT
  def boxChoiceT = HybridProgramTacticsImpl.boxChoiceT
  def inductionT(inv: Option[Formula]) = HybridProgramTacticsImpl.inductionT(inv)
  def diffInductionT(inv : Option[Formula]) = TacticLibrary.differentialInvariant(inv)
  def diffInvariantSystem = ODETactics.diffInvariantT

  def alphaRenamingT(from: String, fromIdx: Option[Int], to: String, toIdx: Option[Int]): PositionTactic =
      new PositionTactic("Alpha Renaming") {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = true // @TODO: really check applicability

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def varBoundInPrg(x: Variable, prg: Program) =
          x.name == from && x.index == fromIdx &&
            Substitution.maybeBoundVariables(prg).exists(v => v.name == from && v.index == fromIdx)
        def rename() = {
          val nextToIdx = toIdx match { case Some(i) => Some(i+1) case None => Some(0) }
          new ApplyRule(new AlphaConversion(p.second, from, fromIdx, to, nextToIdx)) {
            override def applicable(node: ProofNode): Boolean = true
          } & hideT(p.topLevel)
        }

        val prepareRenaming = node.sequent(p) match {
          // TODO find first program that binds x, if it is an ODE or a loop, then rename that one first
          case BoxModality(NDetAssign(x: Variable), BoxModality(prg: ContEvolveProgram, _))
            if varBoundInPrg(x, prg) => rename()
          case BoxModality(Assign(x: Variable, _), BoxModality(prg: ContEvolveProgram, _))
            if varBoundInPrg(x, prg) => rename()
          case BoxModality(Assign(x: Variable, _), BoxModality(prg: Loop, _))
            if varBoundInPrg(x, prg) => rename()
          case _ => NilT
        }
        Some(prepareRenaming & new ApplyRule(new AlphaConversion(p, from, fromIdx, to, toIdx)) {
          override def applicable(node: ProofNode): Boolean = true
        } & hideT(p.topLevel))
      }
    }
  }

  /*********************************************
   * Differential Tactics
   *********************************************/
  def diffWeakenT = ODETactics.diffWeakenT

  def diffInvariant = ODETactics.diffInvariantT

      //not at all sure about this...
  def differentialInvariant(invariant : Option[Formula]) : PositionTactic = new PositionTactic("differential induction") {
    /**
     *
     * @param g
     * @return the body of the continuous evolution operation.
     */
    def getBody(g: Formula): Option[Formula] = g match {
      case BoxModality(ContEvolve(a), _) => Some(a)
      case BoxModality(NFContEvolve(variables, x, theta, f), _) => Some(And(Equals(Real, x, theta), f)) //?
      case _ => None
    }

    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.inExpr == HereP && getBody(s(p)).isDefined

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      def ind(cutSPos: Position, cont: Tactic) = differentialInduction(cutSPos) & AndRightT(cutSPos) &(LabelBranch("Close Next"), abstractionT(cutSPos) & hideT(cutSPos) & cont)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = invariant match {
        case Some(f) => {
          //cutAPos is the location where the differential invariant is cut into the antecedent.
          val cutAPos = AntePosition(node.sequent.ante.length, HereP)

          //This is copied from the box induction tactic and I'm not so sure about it.
          val prepareKMP = new ConstructionTactic("Prepare K modus ponens") {
            override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
              case x@BoxModality(a, _) =>
                val cPos = AntePosition(node.sequent.ante.length)
                val b1 = ImplyLeftT(cPos) & AxiomCloseT
                val b2 = hideT(p)
                Some(cutT(Some(Imply(BoxModality(a, f), x))) & onBranch((cutUseLbl, b1), (cutShowLbl, b2)))
              case _ => None
            }

            override def applicable(node: ProofNode): Boolean = true
          }

          //cutSPos is the location of the box containg the diffeq?
          val cutSPos = SuccPosition(node.sequent.succ.length - 1, HereP)

          //not sure what this is for.
          val useCase = prepareKMP & hideT(cutAPos) & kModalModusPonensT(cutSPos) & abstractionT(cutSPos) & hideT(cutSPos) & LabelBranch(indUseCaseLbl)

          //@todo change these so that the proof closes appropriately.
          val branch1Tactic = ImplyLeftT(cutAPos) &(hideT(p) & LabelBranch(indInitLbl), useCase)
          val branch2Tactic = hideT(p) &
            ImplyRightT(cutSPos) &
            ind(cutSPos, hideT(cutAPos) & LabelBranch(indStepLbl)) &
            onBranch(("Close Next", AxiomCloseT))

          //Cut in the assumption and
          getBody(node.sequent(p)) match {
            case Some(a) =>
              Some(cutT(Some(Imply(f, BoxModality(ContEvolve(a), f)))) & onBranch((cutUseLbl, branch1Tactic), (cutShowLbl, branch2Tactic)))
            case None => None
          }
        }
        case None => Some(ind(p, NilT) & LabelBranch(indStepLbl))
      }
    }
  }

  def diffCutT(h: Formula): PositionTactic = new PositionTactic("Differential cut with ") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(BoxModality(_: ContEvolve, _)) => true
      case Some(BoxModality(_: NFContEvolve, _)) => true
      case Some(BoxModality(_: ContEvolveProduct, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ApplyRule(new DiffCut(p, h)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def differentialInduction: PositionTactic = new PositionTactic("Perform differential induction") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(BoxModality(ContEvolve(_), _)) => true
      case Some(BoxModality(_: NFContEvolve, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(diffIndT(p) & abstractionT(p) & skolemizeT(p) & ImplyRightT(p) & deriveFormulaT(p))
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def diffIndT: PositionTactic = new PositionTactic("Differential Induction") {

    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(BoxModality(ContEvolve(_), _)) => true
      case Some(BoxModality(_: NFContEvolve, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ApplyRule(new DiffInd(p)) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveFormulaT: PositionTactic = new PositionTactic("Derive Formula") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.formula(s, p) match {
      case Some(FormulaDerivative(_)) => true
      case Some(a) => println("Not applicable to " + a.prettyString); false
      case None => println("Not applicable to None"); false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        println("Constructing at " + p);
        Retrieve.formula(node.sequent, p) match {
          case Some(FormulaDerivative(And(_, _))) => Some(deriveAndT(p) ~ deriveFormulaT(p.first) ~ deriveFormulaT(p.second))
          case Some(FormulaDerivative(Or(_, _))) => Some(deriveOrT(p) ~ deriveFormulaT(p.first) ~ deriveFormulaT(p.second))
          case Some(FormulaDerivative(Equals(Real, _, _))) => println("found equals"); Some(deriveEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(NotEquals(Real, _, _))) => Some(deriveNotEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(GreaterThan(Real, _, _))) => Some(deriveGreaterThanT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(GreaterEqual(Real, _, _))) => Some(deriveGreaterEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(LessThan(Real, _, _))) => Some(deriveLessThanT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(FormulaDerivative(LessEqual(Real, _, _))) => Some(deriveLessEqualsT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case _ => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveTermT: PositionTactic = new PositionTactic("Derive Term") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.term(s, p) match {
      case Some(Derivative(_, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        println("Checking " + Retrieve.term(node.sequent, p))
        Retrieve.term(node.sequent, p) match {
          case Some(Derivative(Real, Neg(Real, _))) => Some(deriveNegT(p) ~ deriveTermT(p.first))
          case Some(Derivative(Real, Add(Real, _, _))) => println("Found sum"); Some(deriveSumT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(Derivative(Real, Subtract(Real, _, _))) => Some(deriveMinusT(p) ~ deriveTermT(p.first) ~ deriveTermT(p.second))
          case Some(Derivative(Real, Multiply(Real, _, _))) => Some(deriveProductT(p) ~ deriveTermT(p.first.first) ~ deriveTermT(p.second.second))
          case Some(Derivative(Real, Divide(Real, _, _))) => Some(deriveQuotientT(p) ~ deriveTermT(p.first.first) ~ deriveTermT(p.second.second))
          case Some(Derivative(Real, Exp(Real, Variable(_,_,Real), Number(Real, _)))) => Some(deriveMonomialT(p))
          case Some(Derivative(Real, Number(Real, _))) => Some(deriveConstantT(p))
          case _ => println("Don't know what to do"); None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveAndT: PositionTactic = new AxiomTactic("&' derive and", "&' derive and") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(And(_, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(And(p, q))) =>
        // construct substitution
        val aP = PredicateConstant("p")
        val aQ = PredicateConstant("q")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aQ, q))
        val g = And(FormulaDerivative(p), FormulaDerivative(q))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None, None)
      case _ => None
    }  }

  def deriveOrT: PositionTactic = new AxiomTactic("|' derive or", "|' derive or") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(Or(_, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(Or(p, q))) =>
        // construct substitution
        val aP = PredicateConstant("p")
        val aQ = PredicateConstant("q")
        val l = List(new SubstitutionPair(aP, p), new SubstitutionPair(aQ, q))
        val g = And(FormulaDerivative(p), FormulaDerivative(q))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None, None)
      case _ => None
    }
  }

  def deriveEqualsT: PositionTactic = new AxiomTactic("=' derive =", "=' derive =") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(Equals(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(Equals(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = Equals(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None, None)
      case _ => None
    }
  }

  def deriveNotEqualsT: PositionTactic = new AxiomTactic("!=' derive !=", "!=' derive !=") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(NotEquals(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(NotEquals(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = Equals(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None, None)
      case _ => None
    }
  }

  def deriveGreaterEqualsT: PositionTactic = new AxiomTactic(">=' derive >=", ">=' derive >=") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(GreaterEqual(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(GreaterEqual(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = GreaterEqual(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None, None)
      case _ => None
    }
  }

  def deriveGreaterThanT: PositionTactic = new AxiomTactic(">' derive >", ">' derive >") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(GreaterThan(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(GreaterThan(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = GreaterEqual(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equiv(f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => None
      }
  }

   def deriveLessEqualsT: PositionTactic = new AxiomTactic("<=' derive <=", "<=' derive <=") {
     def applies(f: Formula) = ???
     override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(LessEqual(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(LessEqual(Real, s, t))) =>
        // construct substitution
        val aS = Variable("s", None, Real)
        val aT = Variable("t", None, Real)
        val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
        val g = LessEqual(Real, Derivative(Real, s), Derivative(Real, t))
        val axiomInstance = Equiv(f, g)
        Some(ax, axiomInstance, Substitution(l), None, None)
      case _ => None
    }
  }

  def deriveLessThanT: PositionTactic = new AxiomTactic("<' derive <", "<' derive <") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subFormula(s(p), p.inExpr) match {
      case Some(FormulaDerivative(LessThan(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subFormula(in, pos.inExpr) match {
        case Some(f@FormulaDerivative(LessThan(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = LessEqual(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equiv(f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => None
      }
  }

  def deriveNegT: PositionTactic = new AxiomTactic("-' derive neg", "-' derive neg") {
     def applies(f: Formula) = ???
     override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
       case Some(Derivative(Neg(Real, _))) => true
       case _ => false
     })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Neg(Real, s))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val l = List(new SubstitutionPair(aS, s))
          val g = Neg(Real, Derivative(Real, s))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => None
    }
  }

   def deriveSumT: PositionTactic = new AxiomTactic("+' derive sum", "+' derive sum") {
     def applies(f: Formula) = ???
     override def applies(s: Sequent,p:Position): Boolean = {
       axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
         case Some(Derivative(Real, Add(Real, _, _))) => true
         case _ => false
       })
     }

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Add(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Add(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => println("Not applicable deriveSumT to " + in.prettyString() + " at " + pos); None
    }
  }

  def deriveMinusT: PositionTactic = new AxiomTactic("-' derive minus", "-' derive minus") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Subtract(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Subtract(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Subtract(Real, Derivative(Real, s), Derivative(Real, t))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => None
      }
  }

   def deriveProductT: PositionTactic = new AxiomTactic("*' derive product", "*' derive product") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Multiply(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Multiply(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Add(Real, Multiply(Real, Derivative(Real, s), t), Multiply(Real, s, Derivative(Real, t)))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => None
    }
  }

  def deriveQuotientT: PositionTactic = new AxiomTactic("/' derive quotient", "/' derive quotient") {
    def applies(f: Formula) = ???
    override def applies(s: Sequent,p:Position): Boolean = axiom.isDefined && (Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Divide(Real, _, _))) => true
      case _ => false
    })

    override def constructInstanceAndSubst(in: Formula, ax: Formula, pos: Position): Option[(Formula, Formula,
        Substitution, Option[PositionTactic], Option[PositionTactic])] =
      Retrieve.subTerm(in, pos.inExpr) match {
        case Some(f@Derivative(Real, Divide(Real, s, t))) =>
          // construct substitution
          val aS = Variable("s", None, Real)
          val aT = Variable("t", None, Real)
          val l = List(new SubstitutionPair(aS, s), new SubstitutionPair(aT, t))
          val g = Divide(Real, Subtract(Real, Multiply(Real, Derivative(Real, s), t), Multiply(Real, s, Derivative(Real, t))), Exp(Real, t, Number(2)))
          val axiomInstance = Equals(Real, f, g)
          Some(ax, axiomInstance, Substitution(l), None, None)
        case _ => None
    }
  }
  def deriveMonomialT: PositionTactic = new PositionTactic("Derive Monomial") {
    override def applies(s: Sequent,p:Position): Boolean = Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Exp(Real, Variable(_,_,Real), Number(Real,_)))) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Retrieve.subTerm(node.sequent(p), p.inExpr) match {
          case Some(f@Derivative(Real, Exp(Real, Variable(_,_,Real), Number(Real,_)))) =>
            val app = new ApplyRule(DeriveMonomial(f)) {
              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
            val eqPos = AntePosition(node.sequent.ante.length)
            Some(app & equalityRewriting(eqPos, p, false) & hideT(p.topLevel) & hideT(eqPos))
          case None => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  def deriveConstantT: PositionTactic = new PositionTactic("Derive Constant") {
    override def applies(s: Sequent, p: Position): Boolean = Retrieve.subTerm(s(p), p.inExpr) match {
      case Some(Derivative(Real, Number(_, _))) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Retrieve.subTerm(node.sequent(p), p.inExpr) match {
          case Some(f@Derivative(Real, num@Number(Real, n))) =>
            val app = new ApplyRule(DeriveConstant(f)) {
              override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
            }
            val eqPos = AntePosition(node.sequent.ante.length)
            Some(app & equalityRewriting(eqPos, p) & hideT(p.topLevel) & hideT(eqPos))
          case None => None
        }
      }

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
    }
  }

  object Retrieve {
    val stop = Left(Some(new StopTraversal {}))
    def formula(s: Sequent, p: Position): Option[Formula] = subFormula(s(p), p.inExpr)

    def subFormula(in: Formula, inExpr: PosInExpr): Option[Formula] =
      if(inExpr == HereP) Some(in) else {
        var f: Option[Formula] = None
        ExpressionTraversal.traverse(TraverseToPosition(inExpr, new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = { f = Some(e); stop }
        }), in)
        f
      }

    def term(s: Sequent, p: Position): Option[Term] = subTerm(s(p), p.inExpr)

    def subTerm(f: Formula, inExpr: PosInExpr): Option[Term] = {
      var t: Option[Term] = None
      ExpressionTraversal.traverse(TraverseToPosition(inExpr, new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = { t = Some(e); stop }
      }), f)
      t
    }
  }

  /**
   * @todo not sure if this isn't already defined.
   * @param t the tactic to repeat
   * @return * closure of t
   */
  def ClosureT(t:PositionTactic) = new PositionTactic("closure") {
    override def applies(s: Sequent, p: Position): Boolean = t.applies(s,p)
    override def apply(p: Position): Tactic = (t(p) *)
  }
}
