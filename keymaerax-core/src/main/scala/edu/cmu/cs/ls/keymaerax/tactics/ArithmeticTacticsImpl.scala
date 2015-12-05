/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.AxiomaticRuleTactics.equivalenceCongruenceT
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{axiomLookupBaseT, uncoverAxiomT}
import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
import edu.cmu.cs.ls.keymaerax.tactics.ContextTactics.cutInContext
import edu.cmu.cs.ls.keymaerax.tactics.EqualityRewritingImpl.equivRewriting
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{TraverseToPosition, StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{Propositional, uniformSubstT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.onBranch
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._

import TacticLibrary.{closeT, hideT, debugT, locate}
import PropositionalTacticsImpl.{AndLeftT,NotLeftT,EquivLeftT,cohideT,kModalModusPonensT,NotT,ImplyT,cutT, CloseId}
import SearchTacticsImpl.{lastAnte,lastSucc,locateAnte,locateSucc,onBranch}
import AxiomaticRuleTactics.goedelT
import TacticLibrary.TacticHelper.{getFormula, getTerm}
import edu.cmu.cs.ls.keymaerax.tools.{NoCountExException, Mathematica, Tool}

import scala.collection.immutable
import scala.collection.immutable.List
import scala.language.postfixOps

/**
 * Implementation of arithmetic tactics.
 */
object ArithmeticTacticsImpl {

  /**
   * Creates a new tactic that uses local quantifier elimination to turn a formula into an equivalent formula.
   * @return The tactic.
   */
  def localQuantifierElimination: PositionTactic = new PositionTactic("Local Quantifier Elimination") {
    override def applies(s: Sequent, p: Position): Boolean = isQeApplicable(getFormula(s, p))

    override def apply(p: Position): Tactic = new Tactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def apply(tool: Tool, node: ProofNode) = {
        val t = new ConstructionTactic(name) {
          override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

          override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = tool match {
            case x: Mathematica =>
              val f = getFormula(node.sequent, p)
              val (solution, _) = x.qeEvidence(f)
              val result = Equiv(f, solution)
              Some(cutInContext(result, p) & onBranch(
                (cutShowLbl, lastSucc(cohideT) & equivalenceCongruenceT(p.inExpr) & quantifierEliminationT(tool.name)),
                (cutUseLbl, equivRewriting(AntePosition(node.sequent.ante.length), p.topLevel))
              ))
          }
        }
        t.scheduler = Tactics.MathematicaScheduler
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }
  }

  private def isQeApplicable(f: Formula): Boolean = {
    var qeAble = true

    //@todo different tools? problem: isQeApplicable is called when the tool is not known yet
    val specialFunctions: immutable.Set[String] = immutable.Set("abs", "min", "max")

    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        e match {
          case Box(_, _) => qeAble = false
          case Diamond(_, _) => qeAble = false
          case PredOf(_, _) => qeAble = false
          case _ =>
        }
        if (qeAble) Left(None) else Left(Some(new StopTraversal {}))
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case FuncOf(Function(_, _, Unit, _), Nothing) => true
          case FuncOf(fun, _) => specialFunctions.contains(fun.asString) // check if fun is an external (special) function
          case Differential(_) => qeAble = false
          case _ =>
        }
        if (qeAble) Left(None) else Left(Some(new StopTraversal {}))
      }
    }
    ExpressionTraversal.traverse(fn, f)
    qeAble
  }

  /**
   * The quantifier elimination tactic.
   * @param toolId The quantifier elimination tool to use.
   * @return The tactic.
   */
  def quantifierEliminationT(toolId: String): Tactic = new Tactic("Quantifier Elimination") {
    def qeApplicable(s: Sequent): Boolean = s.ante.isEmpty && s.succ.length == 1 && isQeApplicable(s.succ.head)

    override def applicable(node: ProofNode): Boolean = qeApplicable(node.sequent) && toolIsInitialized()

    override def apply(tool: Tool, node: ProofNode): Unit = {
      var tacticName : String = ""

      if (toolId.equals("Mathematica")) tacticName = "Mathematica QE"
      else if (toolId.equals("Z3")) tacticName = "Z3 QE"
      else if (toolId.equals("Polya")) tacticName = "Polya QE"

      val t: Tactic = new ConstructionTactic(tacticName) {
        override def applicable(node: ProofNode): Boolean = true

        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
          try {
            tool match {
              case qe: QETool =>
                val lemmaDB = LemmaDBFactory.lemmaDB
                val lemma = RCF.proveArithmetic(qe, node.sequent.succ.head)
                val id = lemmaDB.add(lemma)

                lemma.fact.conclusion.succ.head match {
                  case lemmaFml@Equiv(res, True) => {

                    val applyLemma = new ApplyRule(LookupLemma(lemmaDB, id)) {
                      override def applicable(node: ProofNode): Boolean = true
                    }

                    val closeTactic = (closeT | locateSucc(Propositional) | locateAnte(Propositional)) *

                    val tactic = cutT(Some(lemmaFml)) & onBranch(
                      (cutShowLbl, lastSucc(cohideT) & applyLemma),
                      (cutUseLbl, lastAnte(EquivLeftT) & onBranch(
                        (equivLeftLbl, lastAnte(AndLeftT) & closeTactic),
                        (equivRightLbl, lastAnte(AndLeftT) & lastAnte(NotLeftT) & closeT)
                      ))
                    )
                    Some(tactic)
                  }
                  case f => println("Only apply QE if the result is true, have " + f.prettyString); None
                }
            }
          } catch {
            case ex: IllegalArgumentException => Some(debugT("QE failed: " + ex.getMessage) & stopT)
            case ex: IllegalStateException => Some(debugT("QE failed: " + ex.getMessage) & stopT)
          }
        }
      }

      if (toolId.equals("Mathematica")) t.scheduler = Tactics.MathematicaScheduler
      else if (toolId.equals("Z3")) t.scheduler = Tactics.Z3Scheduler.get
      else if (toolId.equals("Polya")) t.scheduler = Tactics.PolyaScheduler.get
      else throw new Exception("Cannot find the QE tool")

      t.continuation = continuation
      t.dispatch(this, node)
    }

    private def toolIsInitialized(): Boolean = {
      // HACK access singletons, because applies/applicable does not have a tool instance parameter
      if (toolId == "Mathematica") MathematicaScheduler.isInitialized
      else if (toolId == "Z3") true
      else if (toolId == "Polya") PolyaScheduler.get.isInitialized
      else false
    }
  }

  /**
   * The counter example generation tactic
   * @param toolId  The counter example generation tool
   * @return  Tactic
   */
  def counterExampleT(toolId: String): Tactic = new Tactic("Counter Example") {
    var showCntExInfo : String = ""

    def qeApplicable(s: Sequent): Boolean = s.ante.isEmpty && s.succ.length == 1 && isQeApplicable(s.succ.head)

    override def applicable(node: ProofNode): Boolean = qeApplicable(node.sequent) && toolIsInitialized()

    override def apply(tool: Tool, node: ProofNode): Unit = {
      var tacticName : String = ""

      if (toolId.equals("Mathematica")) tacticName = "Mathematica Counter Example"

      val t: Tactic = new ConstructionTactic(tacticName) {
        override def applicable(node: ProofNode): Boolean = true

        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
          try {
            tool match {
              case qe: QETool =>
                showCntExInfo = showCounterExample(tool, node)
                node.tacticInfo.infos += ("counterExample" -> showCntExInfo)
                None
            }
          } catch {
            case ex: IllegalArgumentException => Some(debugT("QE failed: " + ex.getMessage) & stopT)
            case ex: IllegalStateException => Some(debugT("QE failed: " + ex.getMessage) & stopT)
          }
        }
      }

      if (toolId.equals("Mathematica")) t.scheduler = Tactics.MathematicaScheduler
      else throw new Exception("Cannot find tool to generate counter example.")

      t.continuation = continuation
      t.dispatch(this, node)
    }

    private def toolIsInitialized(): Boolean = {
      // HACK access singletons, because applies/applicable does not have a tool instance parameter
      if (toolId == "Mathematica") MathematicaScheduler.isInitialized
      else false
    }
  }

  private def skolemize(sequent: Sequent, fml: Formula, pos: Position): Formula = {
    var s = sequent
    var f = fml

    while (fml.isInstanceOf[Forall]) {
      s = Skolemize(pos)(s)(pos.index)
      f = s.succ(pos.index)
    }
    fml
  }

  /**
   * Detemermine whether the given tool can find a counterexample for the given formula.
   * @param tool The counter example generation tool
   * @param proofNode
   * @param position
   * @return Whether a counterexample could be found.
   */
  def hasCounterexample (tool: Tool, node: ProofNode, pos: Position): Boolean = {
    val sequent = node.sequent
    val fml = if (pos.isAnte) sequent.ante(pos.index) else sequent.succ(pos.index)
    tool.name.equals("Mathematica") &&
      !tool.asInstanceOf[Mathematica].getCounterExample(skolemize(sequent, fml, pos)).equals("false")
  }

  /**
   * Detemermine whether the given tool can determine that the formula is contradictory
   * @param tool The counter example generation tool
   * @param proofNode
   * @param position
   * @return Whether a contradiction could be found
   */
  def isContradiction (tool: Tool, node: ProofNode, pos: Position): Boolean = {
    val sequent = node.sequent
    val fml = if (pos.isAnte) sequent.ante(pos.index) else sequent.succ(pos.index)
    // fml is contradictory (never true) iff Not(fml) doesn't have a counterexample (is always true)
    tool.name.equals("Mathematica") &&
      tool.asInstanceOf[Mathematica].getCounterExample(skolemize(sequent, Not(fml), pos)).equals("false")
  }

  /**
   * Shows counter example information as String
   * @param tool The counter example generation tool
   * @param node ProofNode
   * @return  Counter example information
   */
  def showCounterExample(tool: Tool, node: ProofNode) : String = {
    var showCntExInfo = ""
    val f = node.sequent.succ.head
    if(counterExampleT(tool.name).applicable(node)) {
      if(tool.name.equals("Mathematica")) {
        val forallF = skolemize(node.sequent, f, SuccPos(0))
        try {
          val counterExample = tool.asInstanceOf[Mathematica].getCounterExample(forallF)
          if(counterExample.equals("false"))
          {
            showCntExInfo = "No counter example exists for\n" + f.prettyString +"\nIt is probably provable."
            println(showCntExInfo)
          }
          else {
            showCntExInfo = "Cannot prove:\n" + f.prettyString + "\nCounter example generated by " + tool.name + " is:\n" + counterExample
            println(showCntExInfo)
          }
        } catch {
          case e: NoCountExException => showCntExInfo = e.getMessage; println(showCntExInfo)
        }
      } else {
        showCntExInfo = "Cannot use " + tool.name + " to generate counter example for " + f.prettyString
      }
    } else {
      showCntExInfo = "Counter example generation is not applicable for " + f.prettyString
    }
    showCntExInfo
  }

  /**
   * Turns a sequent into a form suitable for quantifier elimination.
   * @param s The sequent.
   * @return The desequentialized form.
   */
  private def desequentialization(s: Sequent) = {
    //TODO-nrf Not sure what to do with pref. Matters in non-taut case.
    if (s.ante.isEmpty && s.succ.isEmpty) False
    else {
      val assumption =
        if (s.ante.isEmpty) True
        else s.ante.reduce((l, r) => And(l, r))

      val implicant =
        if (s.succ.isEmpty) Not(assumption)
        else s.succ.reduce((l, r) => Or(l, r))

      if (s.ante.isEmpty) implicant
      else Imply(assumption, implicant)
    }
  }

  /**
   * Creates a new axiom tactic for commuting over equality: f()=g()) <-> (g()=f()
   * @return The axiom tactic.
   */
  @deprecated("Use TactixLibrary.useAt(\"= commute\") instead")
  def commuteEqualsT : PositionTactic = new PositionTactic("= commute") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
      case Some(Equal(_, _)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(Equal(_, _)) => Some(TactixLibrary.useAt("= commute")(p))
      }
    }
  }

  /**
   * Creates a new axiom tactic for negating equality: s=t <-> !(s!=t)
   * @return The axiom tactic.
   */
  @deprecated("Use TactixLibrary.useAt(\"= negate\") instead")
  def NegateEqualsT: PositionTactic = new PositionTactic("= negate") {
    /** Checks whether this position tactic will be applicable at the indicated position of the given sequent */
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
      case Some(Equal(_, _)) => true
      case Some(Not(NotEqual(_, _))) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(Equal(_, _)) => Some(TactixLibrary.useAt("= negate", PosInExpr(1::Nil))(p))
        case Some(Not(NotEqual(_, _))) => Some(TactixLibrary.useAt("= negate")(p))
      }
    }
  }

  /**
   * Creates a new axiom tactic for negating equality: s=t <-> !(s!=t)
   * @return The axiom tactic.
   */
  @deprecated("Use TactixLibrary.useAt(\"< negate\") instead")
  def NegateLessThanT: PositionTactic = new PositionTactic("< negate") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
      case Some(Less(_, _)) => true
      case Some(Not(GreaterEqual(_, _))) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(Less(_, _)) => Some(TactixLibrary.useAt("< negate", PosInExpr(1::Nil))(p))
        case Some(Not(GreaterEqual(_, _))) => Some(TactixLibrary.useAt("< negate")(p))

      }
    }
  }

  @deprecated("Use TactixLibrary.useAt(\"! <=\") instead")
  def NegateGreaterThanT: PositionTactic = new PositionTactic("> negate") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
      case Some(Greater(_, _)) => true
      case Some(Not(LessEqual(_, _))) => true
      case _ => false
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(Greater(s, t)) => Some(TactixLibrary.useAt("! <=", PosInExpr(1::Nil))(p))
        case Some(Not(LessEqual(s, t))) => Some(TactixLibrary.useAt("! <=")(p))
        case _ => None
      }
    }
  }

  @deprecated("Use TactixLibrary.useAt(\"! >\") instead")
  def NegateLessEqualsT: PositionTactic = new PositionTactic("<= negate") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
      case Some(LessEqual(_, _)) => true
      case Some(Not(Greater(_, _))) => true
      case _ => false
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(LessEqual(s, t)) => Some(TactixLibrary.useAt("! >", PosInExpr(1::Nil))(p))
        case Some(Not(Greater(s, t))) => Some(TactixLibrary.useAt("! >")(p))
        case _ => None
      }
    }
  }

  /**
   * Creates a new tactic for negating =: s!=t <-> !(s=t)
   * @return The tactic.
   */
  @deprecated("Use TactixLibrary.useAt(\"!= negate\") instead")
  def NegateNotEqualsT = new PositionTactic("!= negate") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
        case Some(NotEqual(_, _)) => true
        case Some(Not(Equal(_, _))) => true
        case _ => false
      }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(NotEqual(_, _)) => Some(TactixLibrary.useAt("!= negate", PosInExpr(1::Nil))(p))
        case Some(Not(Equal(_, _))) => Some(TactixLibrary.useAt("!= negate")(p))
      }
    }
  }

  /**
   * Creates a new tactic for negating >=: s < t <-> !(s>=t)
   * @return The tactic.
   */
  @deprecated("Use TactixLibrary.useAt(\"! <\") instead")
  def NegateGreaterEqualsT = new PositionTactic(">= negate") {
    override def applies(s: Sequent, p: Position): Boolean = s(p.topLevel).sub(p.inExpr) match {
      case Some(GreaterEqual(_, _)) => true
      case Some(Not(Less(_, _))) => true
      case _ => false
    }

    override def apply(p: Position) = new ConstructionTactic(name) {
      override def applicable(node: ProofNode) = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p.topLevel).sub(p.inExpr) match {
        case Some(GreaterEqual(_, _)) => Some(TactixLibrary.useAt("! <", PosInExpr(1::Nil))(p))
        case Some(Not(Less(_, _))) => Some(TactixLibrary.useAt("! <")(p))
      }
    }
  }


  /**
   * Creates a new axiom tactic for closing by = reflexivity.
   * @example{{{
   *         EqualReflexiveT(SuccPosition(0))
   *
   *          *
   *          --------
   *          |- s = s
   * }}}
   * @return The axiom tactic.
   */
  @deprecated("Use TactixLibrary.byUS(\"= reflexive\") instead")
  def EqualReflexiveT: PositionTactic = new PositionTactic("= reflexive") {
    override def applies(s: Sequent, p: Position): Boolean = !p.isAnte && p.isTopLevel && (s(p) match {
      case Equal(s1, s2) if s1 == s2 => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case Equal(s1, s2) if s1 == s2 => Some(cohideT(p) & TactixLibrary.byUS("= reflexive"))
      }
    }
  }

  def AbsT: PositionTactic = new PositionTactic("Abs") {
    override def applies(s: Sequent, pos: Position): Boolean = s(pos.topLevel).sub(pos.inExpr) match {
      case Some(FuncOf(Function("abs", None, Real, Real), _)) => true
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("Abs") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos.topLevel).sub(pos.inExpr) match {
        case Some(abs@FuncOf(Function(fn, None, Real, Real), _)) if fn == "abs" =>
          val freshAbsIdx = TacticLibrary.TacticHelper.freshIndexInSequent(fn, node.sequent)
          val absVar = Variable(fn, freshAbsIdx)

          Some(EqualityRewritingImpl.abbrv(abs, Some(absVar))
            & locateAnte(TactixLibrary.useAt("= commute"), _ == Equal(absVar, abs))
            & locateAnte(TactixLibrary.useAt(fn), _ == Equal(abs, absVar))
          )
        case _ => throw new IllegalStateException("Impossible by applies")
      }
    }
  }

  def MinMaxT: PositionTactic = new PositionTactic("MinMax") {
    override def applies(s: Sequent, pos: Position): Boolean = s(pos.topLevel).sub(pos.inExpr) match {
      case Some(FuncOf(Function("min", None, Tuple(Real, Real), Real), Pair(f, g))) => true
      case Some(FuncOf(Function("max", None, Tuple(Real, Real), Real), Pair(f, g))) => true
      case _ => false
    }

    override def apply(pos: Position): Tactic = new ConstructionTactic("MinMax") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, pos)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(pos.topLevel).sub(pos.inExpr) match {
        case Some(minmax@FuncOf(Function(fn, None, Tuple(Real, Real), Real), Pair(f, g))) if fn == "min" || fn == "max" =>
          val freshMinMaxIdx = TacticLibrary.TacticHelper.freshIndexInSequent(fn, node.sequent)
          val minmaxVar = Variable(fn, freshMinMaxIdx)

          Some(EqualityRewritingImpl.abbrv(minmax, Some(minmaxVar))
            & locateAnte(TactixLibrary.useAt("= commute"), _ == Equal(minmaxVar, minmax))
            & locateAnte(TactixLibrary.useAt(fn), _ == Equal(minmax, minmaxVar))
          )
        case _ => throw new IllegalStateException("Impossible by applies")
      }
    }
  }
}