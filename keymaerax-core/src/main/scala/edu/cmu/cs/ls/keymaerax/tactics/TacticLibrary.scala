package edu.cmu.cs.ls.keymaerax.tactics

// favoring immutable Seqs

import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable.Seq

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.onesidedCongruenceT
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.cohide2T
import ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import AxiomaticRuleTactics.boxMonotoneT
import FOQuantifierTacticsImpl.instantiateT
import PropositionalTacticsImpl.NonBranchingPropositionalT
import SearchTacticsImpl.{lastAnte,lastSucc,onBranch}
import HybridProgramTacticsImpl.boxVacuousT
import AlphaConversionHelper.replace
import BranchLabels._

import BuiltinHigherTactics._

import scala.collection.immutable.IndexedSeq
import scala.language.postfixOps

/**
 * In this object we collect wrapper tactics around the basic rules and axioms.
 *
 * Created by Jan-David Quesel on 4/28/14.
 * @author Jan-David Quesel
 * @author aplatzer
 * @author Stefan Mitsch
 */
object TacticLibrary {

  object TacticHelper {
    def getTerm(f : Formula, p : PosInExpr) = {
      var retVal : Option[Term] = None
      ExpressionTraversal.traverse(TraverseToPosition(p, new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
          retVal = Some(e)
          Left(Some(ExpressionTraversal.stop))
        }
      }), f);
      retVal
    }

    def isFormula(s: Sequent, p: Position): Boolean = {
      if (p.isTopLevel) {
        if (p.isAnte) p.index < s.ante.length else p.index < s.succ.length
      } else {
        isFormula(s(p), p.inExpr)
      }
    }

    def isFormula(fml: Formula, p: PosInExpr): Boolean = {
      if (p == HereP) true
      else {
        var f: Formula = null
        ExpressionTraversal.traverse(TraverseToPosition(p, new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
            f = e
            Left(Some(ExpressionTraversal.stop))
          }
        }), fml)
        f != null
      }
    }

    def getFormula(s: Sequent, p: Position): Formula = {
      if (p.isTopLevel) {
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

    /**
     * @deprecated this is very special-purpose.
     */
    def getTerm(f: Formula, p: Position): Term = {
      getTerm(Sequent(Nil, scala.collection.immutable.IndexedSeq(), scala.collection.immutable.IndexedSeq(f)), p)
    }

    def getTerm(s: Sequent, p: Position): Term = try {
        require(p.inExpr != HereP) //should not be at a formula.
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
      catch {
        case e : IndexOutOfBoundsException => throw new Exception("Index out of bounds when accessing position " + p.toString() + " in sequent: " + s)
      }

    def freshIndexInFormula(name: String, f: Formula) =
      if (symbols(f).exists(_.name == name)) {
        val vars = symbols(f).map(n => (n.name, n.index)).filter(_._1 == name)
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

    def symbols(f: Formula): Set[NamedSymbol] = {
      var symbols = Set[NamedSymbol]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case v: Variable => symbols += v; Left(None)
          case FuncOf(fn: Function, _) => symbols += fn; Left(None)
          case _ => Left(None)
        }
      }, f)
      symbols
    }

    def names(s: Sequent) = s.ante.flatMap(symbols) ++ s.succ.flatMap(symbols)

    def freshIndexInSequent(name: String, s: Sequent) =
      if (names(s).exists(_.name == name))
        (s.ante.map(freshIndexInFormula(name, _)) ++ s.succ.map(freshIndexInFormula(name, _))).max
      else None

    def freshNamedSymbol[T <: NamedSymbol](t: T, f: Formula): T =
      if (symbols(f).exists(_.name == t.name)) t match {
        case Variable(vName, _, vSort) => Variable(vName, freshIndexInFormula(vName, f), vSort).asInstanceOf[T]
        case Function(fName, _, fDomain, fSort) => Function(fName, freshIndexInFormula(fName, f), fDomain, fSort).asInstanceOf[T]
        case _ => ???
      } else t

    def freshNamedSymbol[T <: NamedSymbol](t: T, s: Sequent): T =
      if (names(s).exists(_.name == t.name)) t match {
        case Variable(vName, _, vSort) => Variable(vName, freshIndexInSequent(vName, s), vSort).asInstanceOf[T]
        case Function(fName, _, fDomain, fSort) => Function(fName, freshIndexInSequent(fName, s), fDomain, fSort).asInstanceOf[T]
        case _ => ???
      } else t

    def findFormulaByStructure(s: Sequent, f: Formula): Option[Formula] = {
      val fStructure = f.dottify

      val anteStructure = s.ante.map(_.dottify)
      val succStructure = s.succ.map(_.dottify)

      if (anteStructure.contains(fStructure)) Some(s.ante(anteStructure.indexOf(fStructure)))
      else if (succStructure.contains(fStructure)) Some(s.succ(succStructure.indexOf(fStructure)))
      else None
    }
  }

  /*******************************************************************
   * Debug tactics
   *******************************************************************/

  def debugT(s: => Any): Tactic = new Tactic("Debug") {
    override def applicable(node: ProofNode): Boolean = true

    override def apply(tool: Tool, node: ProofNode): Unit = {
      println("===== " + s + " ==== " + node.sequent + " =====")
      continuation(this, Success, Seq(node))
    }
  }

  def debugAtT(s: => Any): PositionTactic = new PositionTactic("Debug") {
    def applies(s: Sequent, p: Position): Boolean = true
    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        if (TacticHelper.isFormula(node.sequent, p)) {
          Some(debugT(s"$s at $p: ${TacticHelper.getFormula(node.sequent, p)}"))
        } else {
          val term = try {
            Some(TacticHelper.getTerm(node.sequent, p))
          }
          catch {
            case _ : Exception => None
          }
          val parentPos =
            if (p.isAnte) AntePosition(p.index, PosInExpr(p.inExpr.pos.init))
            else SuccPosition(p.index, PosInExpr(p.inExpr.pos.init))
          Some(debugT(s"$s at $p is invalid; but might contain term: " + term) & debugAtT(s"looking for valid formula")(parentPos))
        }
      }
    }
  }

  /*******************************************************************
   * Major tactics
   *******************************************************************/
 
  /**
   * Default tactics without any invariant generation.
   */
  def master = BuiltinHigherTactics.master _
  def default = BuiltinHigherTactics.master(new NoneGenerate(), exhaustive = true, "Mathematica")
  def default(toolId : String) = BuiltinHigherTactics.master(new NoneGenerate(), exhaustive = true, toolId)
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

  /**
   * Default arithmeticT
   * Use Mathematica
   */
  def arithmeticT = repeatT(locateAnte(NonBranchingPropositionalT) | locateSucc(NonBranchingPropositionalT)) & repeatT(locateAnte(eqThenHideIfChanged)) &
    PropositionalTacticsImpl.ConsolidateSequentT & assertT(0, 1) & lastSucc(FOQuantifierTacticsImpl.universalClosureT) & debugT("Handing to Mathematica/Z3") &
    (ArithmeticTacticsImpl.quantifierEliminationT("Mathematica") | ArithmeticTacticsImpl.quantifierEliminationT("Z3"))

  /**
   * Alternative arithmeticT
   * @param toolId quantifier elimination tool, could be: Mathematica, Z3, ...
   */
  def arithmeticT(toolId : String) = repeatT(locateAnte(NonBranchingPropositionalT) | locateSucc(NonBranchingPropositionalT)) & repeatT(locateAnte(eqThenHideIfChanged)) &
    PropositionalTacticsImpl.ConsolidateSequentT & assertT(0, 1) & lastSucc(FOQuantifierTacticsImpl.universalClosureT) & debugT("Handing to " + toolId) &
    ArithmeticTacticsImpl.quantifierEliminationT(toolId)

  private def eqThenHideIfChanged: PositionTactic = new PositionTactic("Eq and Hide if Changed") {
    override def applies(s: Sequent, p: Position): Boolean = eqLeft(exhaustive = true).applies(s, p)

    override def apply(p: Position): Tactic = new Tactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def apply(tool: Tool, node: ProofNode) = {
        val eq = eqLeft(exhaustive = true)(p)
        val hide = SearchTacticsImpl.locateAnte(assertPT(node.sequent(p), "Wrong position when hiding EQ") & hideT, _ == node.sequent(p))
        hide.continuation = continuation
        eq.continuation = onChangeAndOnNoChange(node, onChange(node, hide), continuation)
        eq.dispatch(this, node)
      }
    }
  }

  /**
   * Quantifier elimination.
   */
  def quantifierEliminationT(toolId: String) = PropositionalTacticsImpl.ConsolidateSequentT &
    FOQuantifierTacticsImpl.universalClosureT(SuccPosition(0)) & ArithmeticTacticsImpl.quantifierEliminationT(toolId)

  /*******************************************************************
   * Elementary tactics
   *******************************************************************/

  def universalClosure(f: Formula): Formula = FOQuantifierTacticsImpl.universalClosure(f)

  def abstractionT: PositionTactic = new PositionTactic("Abstraction") {
    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && !p.isAnte && (s(p) match {
      case Box(_,_) => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      require(!p.isAnte, "No abstraction in antecedent")

      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case b@Box(prg, phi) =>
          val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
          //else throw new IllegalArgumentException("Cannot handle non-concrete programs")
          val qPhi =
            if (vars.isEmpty) phi //Forall(Variable("$abstractiondummy", None, Real)::Nil, phi)
            else
              vars.to[scala.collection.immutable.SortedSet]. //sortWith((l, r) => l.name < r.name || l.index.getOrElse(-1) < r.index.getOrElse(-1)). // sort by name; if same name, next by index
                foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))

          //val numQuantifiers = if (vars.isEmpty) 1 else vars.length

          Some(cutT(Some(Imply(qPhi, Box(prg, qPhi)))) & onBranch(
            (cutUseLbl, lastAnte(ImplyLeftT) &&(
              hideT(p) /* result */,
              cohide2T(AntePosition(node.sequent.ante.length), p.topLevel) &
                assertT(1, 1) & lastAnte(assertPT(Box(prg, qPhi))) & lastSucc(assertPT(b)) & (boxMonotoneT | NilT) &
                assertT(1, 1) & lastAnte(assertPT(qPhi)) & lastSucc(assertPT(phi)) & (lastAnte(instantiateT)*vars.length) &
                assertT(1, 1) & assertT(s => s.ante.head match { case Forall(_,_) => phi match { case Forall(_,_) => true case _  => false } case _ => true }) &
                (AxiomCloseT | debugT("Abstraction cut use: Axiom close failed unexpectedly") & stopT)
              )),
            (cutShowLbl, hideT(p) & lastSucc(ImplyRightT) & lastSucc(boxVacuousT) &
              (AxiomCloseT | debugT("Abstraction cut show: Axiom close failed unexpectedly") & stopT))
          ))
      }
    }
  }
//  def abstractionT: PositionTactic = new PositionTactic("Abstraction") {
//    override def applies(s: Sequent, p: Position): Boolean = p.isTopLevel && !p.isAnte && (s(p) match {
//      case Box(_, _) => true
//      case _ => false
//    })
//
//    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
//      require(!p.isAnte, "No abstraction in antecedent")
//
//      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
//      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
//        case b@Box(prg, phi) =>
//          val vars = StaticSemantics.boundVars(prg).intersect(StaticSemantics.freeVars(phi)).toSet.to[Seq]
//          //else throw new IllegalArgumentException("Cannot handle non-concrete programs")
//          val qPhi =
//            if (vars.isEmpty) Forall(Variable("$abstractiondummy", None, Real)::Nil, phi)
//            else
//              vars.to[scala.collection.immutable.SortedSet]. //sortWith((l, r) => l.name < r.name || l.index.getOrElse(-1) < r.index.getOrElse(-1)). // sort by name; if same name, next by index
//              foldRight(phi)((v, f) => Forall(v.asInstanceOf[Variable] :: Nil, f))
//
//          Some(cutT(Some(Imply(qPhi, Box(prg, qPhi)))) & onBranch(
//            (cutUseLbl, lastAnte(ImplyLeftT) &&(
//              hideT(p) /* result */,
//              cohide2T(AntePosition(node.sequent.ante.length), p.topLevel) &
//                assertT(1, 1) & lastAnte(assertPT(Box(prg, qPhi))) & lastSucc(assertPT(b)) & (boxMonotoneT | NilT) &
//                assertT(1, 1) & lastAnte(assertPT(qPhi)) & lastSucc(assertPT(phi)) & (lastAnte(instantiateT)*) &
//                assertT(1, 1) & assertT(s => s.ante.head match { case Forall(_, _) => false case _ => true }) &
//                (AxiomCloseT | debugT("Abstraction cut use: Axiom close failed unexpectedly") & stopT)
//              )),
//            (cutShowLbl, hideT(p) & lastSucc(ImplyRightT) & lastSucc(boxVacuousT) &
//              (AxiomCloseT | debugT("Abstraction cut show: Axiom close failed unexpectedly") & stopT))
//          ))
//      }
//    }
//  }

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

  def eqLeft(exhaustive: Boolean) = EqualityRewritingImpl.eqLeft(exhaustive)

  /*********************************************
   * First-Order Quantifier Tactics
   *********************************************/

  def skolemizeT = FOQuantifierTacticsImpl.skolemizeT
  def instantiateQuanT(q: Variable, t: Term) = FOQuantifierTacticsImpl.instantiateT(q, t)

  /*********************************************
   * Hybrid Program Tactics
   *********************************************/

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
  def inductionT(inv: Option[Formula]) = HybridProgramTacticsImpl.wipeContextInductionT(inv)
  def diffInvariantSystemT = ODETactics.diffInvariantT
  def diffSolutionT = ODETactics.diffSolution(None)

  @deprecated("Use alphaRenamingT(Variable,Variable) instead.")
  def alphaRenamingT(from: String, fromIdx: Option[Int], to: String, toIdx: Option[Int]): PositionTactic =
    alphaRenamingT(Variable(from, fromIdx, Real), Variable(to, toIdx, Real))

  def alphaRenamingT(from: Variable, to: Variable): PositionTactic =
      new PositionTactic("Bound Renaming") {
    override def applies(s: Sequent, p: Position): Boolean = {
      var applicable = false
      ExpressionTraversal.traverse(TraverseToPosition(p.inExpr, new ExpressionTraversalFunction {
        override def preF(pos: PosInExpr, f: Formula): Either[Option[StopTraversal], Formula] = {
          f match {
            case Forall(vars, _) => applicable = vars.contains(from)
            case Exists(vars, _) => applicable = vars.contains(from)
              //@todo accept DiffSymbol(from) to occur as well
            case a@Box(_, _) => applicable = StaticSemantics(a).bv.contains(from)
            case a@Diamond(_, _) => applicable = StaticSemantics(a).bv.contains(from)
            case _ => applicable = false //@todo is this over-writing when we're already applicable?!
          }
          Left(Some(ExpressionTraversal.stop))
        }
      }), s(p))
//      if(!applicable) s(p) match {
//        case Forall(vars, _) => applicable = {println("Variables in " + s(p) + " are: " + vars.mkString(",")); vars.contains(from)}
//        case Exists(vars, _) => applicable = vars.contains(from)
//        case _ => println("Not a forall or exists: " + s(p))
//      }
//      else {
//        println("apparently is applicable: " + s(p))
//      }
//      println("Found that this renaming of " + from.prettyString() + " is applicable: " + applicable + " for " + s(p).prettyString() + " with inExpr position: " + p.inExpr)

      applicable
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val fml = TacticHelper.getFormula(node.sequent, p)
        val findResultProof = Provable.startProof(Sequent(node.sequent.pref, IndexedSeq(), IndexedSeq(fml)))
        val desiredResult = findResultProof(new BoundRenaming(from, to), 0).subgoals.head.succ.head
        if (p.isAnte) {
          Some(cutT(Some(node.sequent(p.topLevel).replaceAt(p.inExpr, desiredResult))) & onBranch(
            (cutShowLbl, cohide2T(p.topLevel, SuccPos(node.sequent.succ.length)) &
              onesidedCongruenceT(p.inExpr) & assertT(0, 1) & assertPT(Equiv(fml, desiredResult))(SuccPosition(0)) &
              EquivRightT(SuccPosition(0)) & br & (AxiomCloseT | debugT("alpha: AxiomCloseT failed unexpectedly") & stopT)),
            (cutUseLbl, hideT(p.topLevel))
          ))
        } else {
          Some(cutT(Some(node.sequent(p.topLevel).replaceAt(p.inExpr, desiredResult))) & onBranch(
            (cutShowLbl, hideT(p.topLevel)),
            (cutUseLbl, cohide2T(AntePos(node.sequent.ante.length), p.topLevel) &
              onesidedCongruenceT(p.inExpr) & assertT(0, 1) & assertPT(Equiv(desiredResult, fml))(SuccPosition(0)) &
              EquivRightT(SuccPosition(0)) & br & (AxiomCloseT | debugT("alpha: AxiomCloseT failed unexpectedly") & stopT))
              ))
        }
      }

      private def br = new ApplyRule(new BoundRenaming(from, to)) {
        override def applicable(node: ProofNode): Boolean = true
      }
    }
  }

  @deprecated("Use globalAlphaRenamingT(Variable,Variable) instead.")
  def globalAlphaRenamingT(from: String, fromIdx: Option[Int], to: String, toIdx: Option[Int]): Tactic =
    globalAlphaRenamingT(Variable(from, fromIdx, Real), Variable(to, toIdx, Real))
  def globalAlphaRenamingT(from: Variable, to: Variable): Tactic =
    new ConstructionTactic("Bound Renaming") {
      import scala.language.postfixOps
      override def applicable(node: ProofNode): Boolean = true

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        Some(new ApplyRule(new BoundRenaming(from, to)) {
          override def applicable(node: ProofNode): Boolean = true
        } & initialValueTactic(node.sequent.ante, AntePosition.apply)
          & initialValueTactic(node.sequent.succ, SuccPosition.apply))
      }

      private def initialValueTactic(formulas: IndexedSeq[Formula], factory: (Int, PosInExpr) => Position) = {
        (0 to formulas.length-1).map(i => {
          val pos = factory(i, HereP); (abstractionT(pos) | NilT) & (skolemizeT(pos) | NilT)
        }).foldLeft(Tactics.NilT)((a, b) => a & b)
      }
    }


  /*********************************************
   * Differential Tactics
   *********************************************/
  def diffWeakenT = ODETactics.diffWeakenT

  def diffInvariant = ODETactics.diffInvariantT

  def diffCutT(h: Formula) = ODETactics.diffCutT(h)

  /**
   * @todo not sure if this isn't already defined.
   * @param t the tactic to repeat
   * @return * closure of t
   */
  def ClosureT(t : PositionTactic) = new PositionTactic("closure") {
    override def applies(s: Sequent, p: Position): Boolean = t.applies(s,p)
    override def apply(p: Position): Tactic = t(p)*
  }
}
