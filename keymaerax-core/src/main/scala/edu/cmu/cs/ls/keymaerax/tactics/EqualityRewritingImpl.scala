/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.ArithmeticTacticsImpl.EqualReflexiveT
import edu.cmu.cs.ls.keymaerax.tactics.FormulaConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ContextTactics.replaceInContext
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.{instantiateT, skolemizeT}
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{cutT, EquivLeftT}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{lastSucc,locateAnte}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import PropositionalTacticsImpl._
import BranchLabels._
import SearchTacticsImpl.{lastAnte,onBranch}
import edu.cmu.cs.ls.keymaerax.tactics.AxiomTactic.{uncoverConditionalAxiomT,uncoverConditionalTermAxiomT,axiomLookupBaseT}
import TacticLibrary.TacticHelper.getTerm
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable.{TreeSet, SortedSet, Set}

/**
 * Implementation of equality rewriting.
 */
object EqualityRewritingImpl {
  /**
   * Returns a new tactic for rewriting a formula in the succedent according to an equivalence appearing in the
   * antecedent. Uses propositional tactics instead of builtin rules.
   * @param eqPos The position where the equivalence appears in the antecedent.
   * @param p The position where to rewrite in the succedent.
   * @return The newly created tactic.
   */
  def equivRewriting(eqPos: Position, p: Position): Tactic =
    new ConstructionTactic("Equivalence Rewriting") {
    override def applicable(node: ProofNode): Boolean = eqPos.isAnte && eqPos.isTopLevel && p.isTopLevel &&
      (node.sequent(eqPos) match {
        case Equiv(_, _) => true
        case _ => false
    })

    def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(eqPos) match {
      case Equiv(a, b) if a == node.sequent(p) && !p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) & AxiomCloseT),
          (equivRightLbl, AndLeftT(eqPos) & hideT(p) & NotLeftT(AntePos(node.sequent.ante.length)) & hideT(AntePos(node.sequent.ante.length - 1)))
        ))
      case Equiv(a, b) if a == node.sequent(p) && p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) &
            (if (p.index < eqPos.index) hideT(AntePosition(node.sequent.ante.length - 1)) & hideT(p)
             else hideT(AntePosition(node.sequent.ante.length - 1)) & hideT(AntePosition(p.index - 1)))),
          (equivRightLbl, AndLeftT(eqPos) & lastAnte(NotLeftT) & lastAnte(NotLeftT) & AxiomCloseT)
        ))
      case Equiv(a, b) if b == node.sequent(p) && !p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) & AxiomCloseT),
          (equivRightLbl, AndLeftT(eqPos) & hideT(p) & NotLeftT(eqPos) & hideT(eqPos))
        ))
      case Equiv(a, b) if b == node.sequent(p) && p.isAnte =>
        Some(EquivLeftT(eqPos) & onBranch(
          (equivLeftLbl, AndLeftT(eqPos) &
            (if (p.index < eqPos.index) hideT(AntePosition(node.sequent.ante.length)) & hideT(p)
             else hideT(AntePosition(node.sequent.ante.length)) & hideT(AntePosition(p.index - 1)))),
          (equivRightLbl, AndLeftT(eqPos) & lastAnte(NotLeftT) & lastAnte(NotLeftT) & AxiomCloseT)
        ))
      case _ => None
    }
  }

  def constFormulaCongruenceT(eqPos: Position, left: Boolean, exhaustive: Boolean = true): PositionTactic = new PositionTactic("const formula congruence") {
    override def applies(s: Sequent, p: Position): Boolean = eqPos.isAnte && eqPos.isTopLevel && (s(eqPos) match {
      case Equal(lhs, rhs) if !exhaustive &&  left => getTerm(s, p) == lhs
      case Equal(lhs, rhs) if !exhaustive && !left => getTerm(s, p) == rhs
      case Equal(lhs, rhs) if  exhaustive => true
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(eqPos) match {
        case Equal(lhs, rhs) =>
          if (exhaustive) {
            def axiomInstance(f: Formula): Formula = {
              val cond = node.sequent(eqPos)
              if (left) Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(lhs, rhs)))
              else      Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(rhs, lhs)))
            }
            Some(uncoverConditionalAxiomT("const formula congruence", axiomInstance, _ => constFormulaCongruenceCondT,
              _ => constFormulaCongruenceBaseT(left, p.inExpr, exhaustive))(p))
          } else {
            def axiomInstance(t: Term): Formula = {
              val cond = node.sequent(eqPos)
              if (exhaustive && left) Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(lhs, rhs)))
              if (exhaustive && !left) Imply(cond, Equiv(node.sequent(p), SubstitutionHelper.replaceFree(node.sequent(p))(rhs, lhs)))
              else Imply(cond, replaceInContext(node.sequent(p), node.sequent(eqPos), p.inExpr))
            }
            Some(uncoverConditionalTermAxiomT("const formula congruence", axiomInstance, _ => constFormulaCongruenceCondT,
              _ => constFormulaCongruenceBaseT(left, p.inExpr, exhaustive))(p))
          }
      }
    }
  }
  /** Shows condition in const formula congruence */
  private def constFormulaCongruenceCondT: PositionTactic = new PositionTactic("const formula congruence cond") {
    override def applies(s: Sequent, p: Position): Boolean = true
    override def apply(p: Position): Tactic = AxiomCloseT
  }
  /** Base tactic for const formula congruence */
  private def constFormulaCongruenceBaseT(isLeft: Boolean, where: PosInExpr, exhaustive: Boolean): PositionTactic = new PositionTactic("const formula congruence base") {
    override def applies(s: Sequent, p: Position): Boolean = true

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        def subst(fml: Formula): List[SubstitutionPair] = fml match {
          case Imply(Equal(s, t), Equiv(lhs, rhs)) =>
            val aS = FuncOf(Function("s", None, Unit, Real), Nothing)
            val aT = FuncOf(Function("t", None, Unit, Real), Nothing)
            val aCtx = PredOf(Function("ctxF_", None, Real, Bool), DotTerm)

            if (exhaustive) {
              val substF = if (isLeft) lhs else rhs
              SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) ::
                SubstitutionPair(aCtx, SubstitutionHelper.replaceFree(substF)(if (isLeft) s else t, DotTerm)) :: Nil
            } else {
              // does not check whether substituting is admissible! use with caution, tactic will result in substitution clashes
              val ctx = if (isLeft) lhs.replaceAt(s, where, DotTerm) else rhs.replaceAt(t, where, DotTerm)
              SubstitutionPair(aS, s) :: SubstitutionPair(aT, t) :: SubstitutionPair(aCtx, ctx) :: Nil
            }
        }
        Some(axiomLookupBaseT("const formula congruence", subst, _ => NilPT, (f, ax) => ax)(p))
      }
    }
  }

  def smartEqualityRewritingT:Tactic = SearchTacticsImpl.locateAnte(smartEqPos("Look for equality in antecedent and apply it"))

  def positionsOf(t: Term, fml: Formula): Set[PosInExpr] = {
    var positions: Set[PosInExpr] = Set.empty
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        if (e == t && !positions.exists(_.isPrefixOf(p))) positions += p
        Left(None)
      }
    }, fml)
    positions
  }

  def positionsOf(t: Term, s: Sequent): Set[Position] = {
    val ante = s.ante.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => AntePosition(i, p)) })
    val succ = s.succ.zipWithIndex.flatMap({ case (f, i) => positionsOf(t, f).map(p => SuccPosition(i, p)) })
    (ante ++ succ).toSet
  }

  /**
   * Applies an equality at a position everywhere in the sequent if it makes the sequent "simpler" for some definition of simpler.
   * Hides the equality if no possible uses remain.
   * @example{{{
   *               |- x < 5
   *   ----------------------------------
   *   x = y^2 + 1 |- y^2 + 1 < 5
   * }}}
   * @todo Check whether it's safe to apply this tactic in more cases than eqPos due to the complexity checks.
   * @todo Hide assumptions when you're done with them, unless the assumption is strong enough to give us false.
   */
  private def smartEqPos(name: String): PositionTactic = new PositionTactic(name) {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position):Boolean = p.isAnte && (s(p) match {
      case Equal(lhs,rhs) =>
        val cmp = compareTermComplexity(lhs,rhs)
        if (cmp == 0) {
          false
        } else {
          val what = if (cmp > 0) lhs else rhs
          val repl = if (cmp > 0) rhs else lhs
          val occurrences : Set[Position] = positionsOf(what, s).filter(pos => pos.isAnte != p.isAnte || pos.index != p.index).
            filter(pos => StaticSemanticsTools.boundAt(s(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty)
          // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
          !what.isInstanceOf[Number] && what != repl &&
            positionsOf(what, s).exists(pos => (pos.isAnte != p.isAnte || pos.index != p.index) &&
              StaticSemanticsTools.boundAt(s(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty) &&
            occurrences.size != 0

          }
      case _ => false })


    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case eq@Equal(lhs, rhs) =>
          val cmp = compareTermComplexity(lhs, rhs)
          val what = if (cmp > 0) lhs else rhs
          val repl = if (cmp > 0) rhs else lhs
          assert(!what.isInstanceOf[Number] && what != repl && cmp != 0)
          // positions are not stable, so we need to search over and over again (we even need to search eqPos, since it
          // may shift)
          val occurrences = positionsOf(what, node.sequent).filter(pos => pos.isAnte != p.isAnte || pos.index != p.index).
            filter(pos => StaticSemanticsTools.boundAt(node.sequent(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty)
          val tactic = constFormulaCongruenceT(p, left = cmp > 0, exhaustive = false)(occurrences.head) &
            (locateAnte(eqPos(name, cmp > 0, true), _ == eq) | NilT)
          // Hide the equality if we think we won't need it for the rest of the proof. We test for counterexamples first because if
          // the equality has a counterexample then we can derive false, it which case we definitely don't want to throw it out.
          if (ArithmeticTacticsImpl.hasCounterexample(tool, node, p)) {
            Some(tactic)
          } else {
            val hide = SearchTacticsImpl.locateAnte(assertPT(node.sequent(p), "Wrong position when hiding EQ") & hideT, _ == node.sequent(p))
            Some(tactic & hide)
          }
      }
    }
  }


  /**
   * Creates a new tactic to rewrite an equality.
   * @param name The name of the tactic.
   * @param left If true: rewrite right to left; if false: rewrite left to right
   * @param exhaustive Indicates whether to rewrite exhaustively.
   * @return The new tactic.
   */
  private def eqPos(name: String, left: Boolean, exhaustive: Boolean): PositionTactic = new PositionTactic(name) {
    import scala.language.postfixOps
    override def applies(s: Sequent, p: Position): Boolean = p.isAnte && (s(p) match {
      case Equal(lhs, rhs) =>
        val what = if (left) lhs else rhs
        val repl = if (left) rhs else lhs
        // prevent endless self rewriting (e.g., 0=0) -> compute dependencies first to figure out what to rewrite when
        !what.isInstanceOf[Number] && what != repl &&
        StaticSemantics.symbols(what).intersect(StaticSemantics.symbols(repl)).isEmpty &&
          positionsOf(what, s).exists(pos => (pos.isAnte != p.isAnte || pos.index != p.index) &&
            StaticSemanticsTools.boundAt(s(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty)
      case _ => false
    })

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)
      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent(p) match {
        case eq@Equal(lhs, rhs) =>
          val what = if (left) lhs else rhs
          val repl = if (left) rhs else lhs
          assert(!what.isInstanceOf[Number] && what != repl)
          // positions are not stable, so we need to search over and over again (we even need to search eqPos, since it
          // may shift)
          val occurrences = positionsOf(what, node.sequent).filter(pos => pos.isAnte != p.isAnte || pos.index != p.index).
            filter(pos => StaticSemanticsTools.boundAt(node.sequent(pos), pos.inExpr).intersect(StaticSemantics.freeVars(what)).isEmpty)
          if (exhaustive) {
            Some(constFormulaCongruenceT(p, left=left, exhaustive=false)(occurrences.head) &
              (locateAnte(eqPos(name, left, exhaustive), _ == eq) | NilT))
          } else {
            Some(constFormulaCongruenceT(p, left=left, exhaustive=false)(occurrences.head))
          }
      }
    }
  }

  /**
   * Creates a new tactic to rewrite occurrences of the left-hand side of an equality into the right-hand side.
   * @param exhaustive True: apply exhaustively; false: apply only once at the first occurrence found.
   * @return The new tactic.
   */
  def eqLeft(exhaustive: Boolean): PositionTactic = eqPos("Find Left and Apply Right to Left", left=true, exhaustive=exhaustive)
  /**
   * Creates a new tactic to rewrite occurrences of the right-hand side of an equality into the left-hand side.
   * @param exhaustive True: apply exhaustively; false: apply only once at the first occurrence found.
   * @return The new tactic.
   */
  def eqRight(exhaustive: Boolean): PositionTactic = eqPos("Find Right and Apply Left to Right", left=false, exhaustive=exhaustive)

  /**
   * Abbreviates a term at a position to a variable.
   * @example{{{
   *   maxcd = max(c,d) |- a+b <= maxcd+e
   *   ----------------------------------------abbrv(Variable("maxcd"))(SuccPosition(0).second.first)
   *                    |- a+b <= max(c, d) + e
   * }}}
   * @param abbrvV The abbreviation.
   * @return The tactic.
   */
  def abbrv(abbrvV: Variable): PositionTactic = new PositionTactic("abbrv") {
    override def applies(s: Sequent, p: Position): Boolean = getTerm(s, p) != null // just to test that there is no exception

    override def apply(p: Position): Tactic = new ConstructionTactic("abbrv") {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val t = getTerm(node.sequent, p)
        Some(abbrv(t, Some(abbrvV)))
      }
    }
  }

  /**
   * Abbreviates a term to a variable.
   * @example{{{
   *   max_0 = max(c,d) |- a+b <= max_0+e
   *   ----------------------------------------abbrv("max(c,d)".asTerm)
   *                    |- a+b <= max(c, d) + e
   * }}}
   * @param abbrvV The abbreviation. If None, the tactic picks a name based on the top-level operator of the term.
   * @return The tactic.
   */
  def abbrv(t: Term, abbrvV: Option[Variable] = None): Tactic = new ConstructionTactic("abbrv") {
    override def applicable(node: ProofNode): Boolean = abbrvV match {
      case Some(v) => !TacticHelper.names(node.sequent).contains(v)
      case None => true
    }

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val v = abbrvV match {
        case Some(vv) => vv
        case None => t match {
          case FuncOf(Function(n, _, _, sort), _) => Variable(n, TacticHelper.freshIndexInSequent(n, node.sequent), sort)
          case Variable(n, _, sort) => Variable(n, TacticHelper.freshIndexInSequent(n, node.sequent), sort)
          case _ => Variable(t.kind.toString, TacticHelper.freshIndexInSequent(t.kind.toString, node.sequent), t.sort)
        }
      }
      Some(cutT(Some(Exists(v :: Nil, Equal(v, t)))) & onBranch(
        (cutShowLbl, lastSucc(cohideT) &
          //@note cannot use instantiateT, because during \exists generalize we don't know which part of z=z we should generalize
          cutT(Some(Equiv(Exists(v :: Nil, Equal(v, t)), Equal(t, t)))) & onBranch(
          (cutShowLbl, lastSucc(EquivRightT) & onBranch(
            (equivLeftLbl, AxiomCloseT),
            (equivRightLbl, FOQuantifierTacticsImpl.existentialGenPosT(v, HereP.first :: Nil)(AntePosition(0)) & AxiomCloseT)
          )),
          (cutUseLbl, equivRewriting(AntePosition(0), SuccPosition(0)) & EqualReflexiveT(SuccPosition(0)))
        )),
        (cutUseLbl, lastAnte(skolemizeT) & lastAnte(eqRight(exhaustive = true)))
      ))
    }
  }

  /** To compare the complexity of terms we first normalize them to polynomials (where we include differential symbols in the
    * set of possible variables). Since quotients and exponentials cannot be normalized to polynomials, we consider quotients
    * more complex than polynomials and exponentials most complex of all.
    *
    * This comparison is based on the graded lexicographic ordering often used when computing Groebner bases with Buchberger's algorithm,
    * though it may vary in some of the details.
    *
    *  The type Monomial encodes a monomial as a coefficient and a set of variables raised to positive exponents. Constant terms are encoded
    *  as coefficients with no variables. A PolyTerm represents a polynomial over BigDecimals where the variables are program variables and
    *  their differential symbols.
    */
  type Monomial = (BigDecimal, Set[(Term, Int)])
  type PolyTerm = Set[Monomial]

  private def zeroMon : Monomial = (BigDecimal(0), Set.empty[(Term,Int)])
  private def zeroPoly : PolyTerm = Set.empty[Monomial]

  // Remove all variables from vs1 that appear in vs2 (possibly with different exponents)
  private def removeVarsOf(vs1: Set[(Term, Int)], vs2: Set[(Term, Int)]): Set[(Term, Int)] =
    vs1.filter(xn => !vs2.exists(ym => xn._1 == ym._1))

  // Remove all monomials from p1 that appear in p2 (possibly with different coefficients)
  private def removeMonomialsOf(p1: PolyTerm, p2: PolyTerm): PolyTerm =
    p1.filter(p1 => !p2.exists(p2 => p1._2 == p2._2))

  // Compute the variables that appear in both vs1 and vs2 with their associated exponents.
  private def commonVars(vs1: Set[(Term, Int)], vs2: Set[(Term, Int)]): Set[(Term, Int, Int)] =
    vs1.flatMap((xn: (Term, Int)) => {
      val (found: Option[(Term, Int)]) = vs2.find(ym => xn._1 == ym._1)
      found match {
        case None => Set.empty[(Term, Int, Int)]
        case Some(ym: (Term, Int)) => Set.empty.+((xn._1, ym._2, xn._2))
      }
    })

  // Computes the product of two monomials
  private def multiplyMon(mon1: Monomial, mon2: Monomial): Monomial = {
    (mon1, mon2) match {
      case ((c1, vs1), (c2, vs2)) =>
        val common = commonVars(vs1, vs2).map(cvs => (cvs._1, cvs._2 + cvs._3))
        (c1 * c2, removeVarsOf(vs1, common) ++ removeVarsOf(vs2, common) ++ common)
    }
  }

  private def syntacticDerivative(t: Term): Term =
    t match {
      case Differential(t1) => syntacticDerivative(syntacticDerivative(t1))
      case Plus(t1, t2) => Plus(syntacticDerivative(t1), syntacticDerivative(t2))
      case Minus(t1, t2) => Minus(syntacticDerivative(t1), syntacticDerivative(t2))
      case Times(t1, t2) => Plus(Times(t1, syntacticDerivative(t2)), Times(t2, syntacticDerivative(t1)))
      case Divide(t1, t2) => Divide(Minus(Times(syntacticDerivative(t1), t2), Times(t1, syntacticDerivative(t2))), Times(t2, t2))
      case x@Variable(_, _, _) => DifferentialSymbol(x)
      case Neg(t1) => Neg(syntacticDerivative(t1))
      case Number(_) => Number(0)
      case DifferentialSymbol(_) => ??? // @todo Decide whether it's better to introduce auxilliary variables or just fail
    }

  // Exceptions for reporting terms that can't be turned into polynomials.
  class BadDivision extends Exception {}
  class BadPower extends Exception {}

  // Create a polynomial of form c for some real c.
  private def constPoly(x: BigDecimal): PolyTerm =
    Set.empty.+((x, Set.empty[(Term, Int)]))

  // Create a polynomial of form x (or x')/
  private def variablePoly(x: Term): PolyTerm =
    Set.empty.+((BigDecimal(1), Set.empty.+((x, 1))))

  // Expand constant powers to iterated products.
  private def expandPower(t: Term, n: BigInt): Term = {
    (n == BigInt(0), n == BigInt(1)) match {
      case (true, false) => Number(BigDecimal(1))
      case (false, true) => t
      case _ => Times(t, expandPower(t, n - 1))
    }
  }

  // Find the common elements of norm1 and norm2, combining corresponding elements with f
  private def mapCommon (norm1: Set[Monomial], norm2: Set[Monomial], f: (BigDecimal,BigDecimal) => BigDecimal): Set[Monomial] = {
    norm1.flatMap(mon1 =>
      norm2.find(mon2 => mon1._2 == mon2._2) match {
        case None => Set.empty[Monomial]
        case Some(mon2) => Set.empty.+((f(mon1._1,mon2._1), mon1._2))
    })
  }

  private def addPolyTerms(p1:PolyTerm,p2:PolyTerm):PolyTerm = {
    val commonMonomials = mapCommon(p1, p2, { case (x, y) => x + y })
    commonMonomials ++ removeMonomialsOf(p1, commonMonomials) ++ removeMonomialsOf(p2,commonMonomials)
  }

  // Main loop for normalizing terms to polynomials. Throws an exception if the term has no normal form.
  // Breaks the invariant that all coefficients are non-zero
  private def normLoop(t: Term): PolyTerm = {
    t match {
      case Times(t1: Term, t2: Term) =>
        val normT2 = normLoop(t2)
        normLoop(t1).foldLeft(zeroPoly){case (acc,mon1) =>
          normT2.foldLeft(acc)({case (acc,mon2) =>
            addPolyTerms(acc,Set(multiplyMon(mon1, mon2)))})}
    case Plus(t1: Term, t2: Term) =>
        val (norm1, norm2) = (normLoop(t1), normLoop(t2))
        addPolyTerms(norm1,norm2)
      case Minus(t1: Term, t2: Term) =>
        val (norm1, norm2) = (normLoop(t1), normLoop(t2))
        val commonMonomials = mapCommon(norm1,norm2,{case (x,y) => x-y})
        var negNorm2 = norm2.map({case (n,x) => (-n, x)})
        commonMonomials ++ removeMonomialsOf(norm1,commonMonomials) ++ removeMonomialsOf(norm2,commonMonomials)
      case Neg(t1:Term) => normLoop(Minus(Number(BigDecimal(0)),t1))
      case Differential(t1) => normLoop(syntacticDerivative(t1))
      case Divide(t1, Number(x)) =>
        if (x == BigDecimal(0)) {
          throw new BadDivision
        }
        else
          normLoop(Times(t1, Number(1 / x)))
      case Divide(_,_) => throw new BadDivision
      case Number(x) => constPoly(x)
      case x@Variable(_, _, _) => variablePoly(x)
      case x@DifferentialSymbol(_) => variablePoly(x)
      case Power(t1, Number(x)) =>
        x.toBigIntExact() match {
          case None => throw new BadPower
          case Some(n) =>
            if (n < BigInt(0)) {
              throw new BadPower
            }
            normLoop(expandPower(t1, n))
        }
      case Power(_,_) => throw new BadPower
      }
  }

  // Compute the normal form of a term, or throws an exception if none exists
  def norm(t:Term):PolyTerm = {
    // Since normLoop breaks the invariant that coefficients are nonzero, we restore it here.
    normLoop(t).filter({case (n,vs) => BigDecimal(0) != n})
  }
  
  
  sealed trait NormResult {}
  case class NormalForm (polyTerm: PolyTerm) extends NormResult
  case class BadPowerResult () extends NormResult
  case class BadDivResult () extends NormResult

  private def totalNorm(t: Term): NormResult = {
     try {
       NormalForm(norm(t))
     } catch {
       case ex: BadDivision => BadDivResult()
       case ex: BadPower => BadPowerResult()
     }
   }

  private object VariableComparator extends Ordering[(Term,Int)] {
    def compare(t1: (Term,Int), t2: (Term,Int)): Int = compareVars (t1._1, t2._1)
  }

  private def sortVars(s: Set[(Term, Int)]): SortedSet[(Term, Int)] = {
    val ss : SortedSet[(Term,Int)] = TreeSet[(Term,Int)]()(VariableComparator)
    s.foldLeft(ss)({case (ss, xn) => ss.+(xn)})
  }

  private def totalDegree(mon:Monomial): Int = {
     mon._2.foldLeft(0)({case (n1,(v,n2)) => n1+n2})
  }

  // Compares two variables in a polynomial, ordered by complexity. We consider differential symbols more complex
  // than program variables because it seems likely that eliminating them will usually make proofs simpler.
  private def compareVars(x1:Term,x2:Term):Int = {
    (x1,x2) match {
      case (v1@Variable(_,_,_),v2@Variable(_,_,_)) => v1.compare(v2)
      case (v1@DifferentialSymbol(_), v2@DifferentialSymbol(_)) =>
        v1.compare(v2)
      case (DifferentialSymbol(_),Variable(_,_,_)) => 1
      case (Variable(_,_,_), DifferentialSymbol(_)) => -1
    }
  }

  // Compares the variables of two monomials (assumes the input lists are sorted on the variables)
  private def compareSortedVars(l1:List[(Term,Int)],l2:List[(Term,Int)]):Int = {
    (l1, l2) match {
      case (Nil, Nil) => 0
      case ((x: (Term, Int)) :: _, Nil) => x._2.compare(0)
      case (Nil, (x: (Term, Int)) :: _) => 0.compare(x._2)
      case ((x: (Term, Int)) :: xs, (y: (Term, Int)) :: ys) =>
        val varCmp = compareVars(x._1, y._1)
        if (varCmp < 0) {
          x._2.compare(0)
        } else if (varCmp > 0) {
          0.compare(y._2)
        } else {
          val expCmp = x._2.compare(y._2)
          if (expCmp != 0) {
            expCmp
          } else {
            compareSortedVars(xs, ys)
          }
        }
    }
  }

  private def compareMonomialVars(s1:Set[(Term,Int)],s2:Set[(Term,Int)]):Int = {
    compareSortedVars(sortVars(s1).toList,sortVars(s2).toList)
  }

  // Graded lexicographic monomial ordering, commonly used when finding Groebner bases.
  // @todo Consider a "doubly-graded" ordering (on POLYnomials) where the number of monomials comes
  // after the total degree of the leading term
  object MonomialGrlex extends Ordering[Monomial] {
    def compare(mon1: Monomial, mon2: Monomial): Int = {
      val cmpDegree = totalDegree(mon1).compare(totalDegree(mon2))
      if (cmpDegree != 0) {
        cmpDegree
      } else {
        val cmpVars = compareMonomialVars(mon1._2, mon2._2)
        if (cmpVars != 0) {
          cmpVars
        } else {
          mon1._1.compare(mon2._1)
        }
      }
    }
  }

  // Compares two polynomials assuming their monomials are in sorted order
  private def compareSortedPolyTerms(l1:List[Monomial],l2:List[Monomial]):Int = {
    (l1,l2) match {
      case (Nil,Nil) => 0
      case ((x:Monomial) :: _, Nil) => MonomialGrlex.compare(x, zeroMon)
      case (Nil, (x:Monomial) ::_) => MonomialGrlex.compare(zeroMon, x)
      case ((x:Monomial)::xs,(y:Monomial)::ys) =>
        val varCmp = compareMonomialVars(x._2,y._2)
        if (varCmp < 0) {
          MonomialGrlex.compare(x,zeroMon)
        } else if (varCmp > 0) {
          MonomialGrlex.compare(zeroMon, y)
        } else {
          x._1.compare(y._1)
        }
    }
  }

  private def compareNormalTerms(l:PolyTerm, r:PolyTerm) : Int = {
    val ls = l.foldLeft(TreeSet()(MonomialGrlex))({case (s,mon) => s.+(mon)}).toList
    val rs = r.foldLeft(TreeSet()(MonomialGrlex))({case (s,mon) => s.+(mon)}).toList
    compareSortedPolyTerms(ls,rs)
  }

  /** Compares two terms by complexity. l > r if replacing l with r would likely simplify the formula, and vice versa.
    * If l = r, this indicates that it is unclear which term is more complex, and we should not substitute either one with
    * the other. */
  def compareTermComplexity(l:Term, r:Term) : Int = {
    (totalNorm(l), totalNorm(r)) match {
      case (NormalForm(norm1), NormalForm(norm2)) => compareNormalTerms(norm1, norm2)
      case (BadPowerResult(), BadPowerResult()) => 0
      case (BadPowerResult(), _) => 1
      case (_, BadPowerResult()) => -1
      case (BadDivResult(), BadDivResult()) => 0
      case (BadDivResult(), _) => 1
      case (_, BadDivResult()) => -1
    }
  }
}
