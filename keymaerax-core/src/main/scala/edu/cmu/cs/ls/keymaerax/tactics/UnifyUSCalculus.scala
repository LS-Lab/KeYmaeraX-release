/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.StaticSemantics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary.assertT
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable._

/**
 * Automatic unification-based Uniform Substitution Calculus with indexing.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[AxiomIndex.axiomIndex()]]
 * @see [[HilbertCalculus]]
 * @see [[TactixLibrary]]
 */
trait UnifyUSCalculus {
  import Tactic.DEBUG

  type Subst = UnificationMatch.Subst

  /*******************************************************************
    * unification and matching based auto-tactics (backward tableaux/sequent)
    *******************************************************************/

  /** US(form) reduce the proof to a proof of form by a suitable uniform substitution obtained by unification */
  //def US(form: Sequent): Tactic = US(form)

  /** useAt(fact, tactic)(pos) uses the given fact (that'll be proved by tactic after unification) at the given position in the sequent (by unifying and equivalence rewriting). */
  //def useAt(fact: Formula, key: PosInExpr, tactic: Tactic, inst: Subst=>Subst): PositionTactic = useAt(fact, key, tactic, inst)
  //def useAt(fact: Formula, key: PosInExpr, tactic: Tactic): PositionTactic = useAt(fact, key, tactic)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Formula, key: PosInExpr, inst: Subst=>Subst): PositionTactic = useAt(fact, key, skip, inst)
  def useAt(fact: Formula, key: PosInExpr): PositionTactic = useAt(fact, key, skip)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Provable, key: PosInExpr, inst: Subst=>Subst): PositionTactic = {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
    useAt(fact.conclusion.succ.head, key, byUS(fact), inst)
  }
  def useAt(fact: Provable, key: PosInExpr): PositionTactic = {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
    require(fact.isProved, "(no strict requirement, but) the best usable facts are proved " + fact)
    useAt(fact.conclusion.succ.head, key, byUS(fact))
  }
  // like useAt(fact,key) yet literally without uniform substitution of fact
//  private[tactics] def useDirectAt(fact: Provable, key: PosInExpr): PositionTactic = {
//    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
//    require(fact.isProved, "(no strict requirement, but) the best usable facts are proved " + fact)
//    useAt(fact.conclusion.succ.head, key, by(fact))
//  }
  /** useAt(lem)(pos) uses the given lemma at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(lem: Lemma, key:PosInExpr, inst: Subst=>Subst): PositionTactic = useAt(lem.fact, key, inst)
  def useAt(lem: Lemma, key:PosInExpr): PositionTactic = useAt(lem.fact, key)
  def useAt(lem: Lemma)       : PositionTactic = useAt(lem.fact, PosInExpr(0::Nil))
  /** useAt(axiom)(pos) uses the given axiom at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(axiom: String, key: PosInExpr, inst: Subst=>Subst): PositionTactic =
    if (Axiom.axioms.contains(axiom)) useAt(Axiom.axiom(axiom), key, inst)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useAt(DerivedAxioms.derivedAxiom(axiom), key, inst)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  def useAt(axiom: String, key: PosInExpr): PositionTactic =
    if (Axiom.axioms.contains(axiom)) useAt(Axiom.axiom(axiom), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useAt(DerivedAxioms.derivedAxiom(axiom), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  def useAt(axiom: String, inst: Subst=>Subst): PositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1, inst)
  def useAt(axiom: String): PositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1)

  /** by(provable) is a pseudo-tactic that uses the given Provable to continue or close the proof (if it fits to what has been proved) */
  def by(provable: Provable)  : Tactic = new ByProvable(provable)
  /** by(lemma) is a pseudo-tactic that uses the given Lemma to continue or close the proof (if it fits to what has been proved) */
  def by(lemma: Lemma)        : Tactic = by(lemma.fact)
  /** byUS(provable) proves by a uniform substitution instance of provable */
  def byUS(provable: Provable): Tactic = US(provable.conclusion) & by(provable)
  /** byUS(lemma) proves by a uniform substitution instance of lemma */
  def byUS(lemma: Lemma)      : Tactic  = byUS(lemma.fact)
  /** byUS(axiom) proves by a uniform substitution instance of axiom */
  def byUS(axiom: String)     : Tactic =
    if (Axiom.axioms.contains(axiom)) byUS(Axiom.axiom(axiom))
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) byUS(DerivedAxioms.derivedAxiom(axiom))
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

  /*******************************************************************
    * unification and matching based auto-tactics (backward tableaux/sequent)
    *******************************************************************/

  /**
   * US(form) uses a suitable uniform substitution to reduce the proof to instead proving form.
   * Unifies the sequent with form and uses that as a uniform substitution.
   *
   * @author Andre Platzer
   * @param form the sequent to reduce this proof node to by a Uniform Substitution
   */
  def US(form: Sequent): Tactic = new ConstructionTactic("US") {
    def applicable(node: ProofNode) = try {
      UnificationMatch(form,node.sequent)
      true
    } catch {case e: ProverException =>
      if (DEBUG) println(e.inContext("US(" + form + ")\n(" + node.sequent + ") inapplicable since un-unifiable"))
      false
    }

    def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
      val subst = UnificationMatch(form, node.sequent)
      if (DEBUG) println("  US(" + form.prettyString + ") unify: " + node.sequent + " matches against form " + form + " by " + subst)
      assert(node.sequent == subst(form), "unification matched successfully: " + node.sequent + " is " + subst(form) + " which is " + form + " instantiated by " + subst)
      Some(subst.toTactic(form))
    }

  }

  /**
   * useAt(fact)(pos) uses the given fact at the given position in the sequent.
   * Unifies fact the left or right part of fact with what's found at sequent(pos) and use corresponding
   * instance to make progress by reducing to the other side.
   *
   * Backward Tableaux-style proof analogue of [[useFor()]].

   * Tactic specification:
   * {{{
   * useAt(fact)(p)(F) = let (C,f)=F(p) in
   *   case f of {
   *     s=unify(fact.left,_) => CutRight(C(s(fact.right))(p) & <(
   *       "use cut": skip
   *       "show cut": EquivifyRight(p.top) & CoHide(p.top) & CE(C(_)) & factTactic
   *     )
   *     s=unify(fact.right,_) => accordingly with an extra commuteEquivRightT
   *   }
   * }}}
   * @author Andre Platzer
   * @param fact the Formula to use to simplify at the indicated position of the sequent
   * @param key the part of the Formula fact to unify the indicated position of the sequent with
   * @param factTactic the tactic to use to prove the instance of the fact obtained after unification
   * @param inst Transformation for instantiating additional unmatched symbols that do not occur in fact(key).
   *   Defaults to identity transformation, i.e., no change in substitution found by unification.
   *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
   * @example useAt("[a;++b;]p(??)<->[a;]p(??)&[b;]p(??)", PosInExpr(0::Nil), byUS("[;] compose"))
   * applied to the indicated 1::1::Nil of
   * [x:=1;][{x'=22}] [x:=2*x;++x:=0;]x>=0
   * turns it into
   * [x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)
   * @see [[useFor()]]
   * @todo could directly use prop rules instead of CE if key close to HereP if more efficient.
   */
  def useAt(fact: Formula, key: PosInExpr, factTactic: Tactic, inst: Subst=>Subst = (us=>us)): PositionTactic = new PositionTactic("useAt") {
    import TactixLibrary.assertT
    import TactixLibrary.debug
    import TacticLibrary.debugC
    import TacticLibrary.instantiateQuanT
    import SearchTacticsImpl.lastSucc
    import Augmentors._
    private val (keyCtx:Context[_],keyPart) = fact.at(key)

    override def applies(s: Sequent, p: Position): Boolean = try {
      val sub = s.sub(p)
      if (!sub.isDefined) {
        if (DEBUG) println("ill-positioned " + p + " in " + s + "\nin " + "useAt(" + fact + ")(" + p + ")\n(" + s + ")")
        return false
      }
      UnificationMatch(keyPart,sub.get)
      true
    } catch {case e: ProverException =>
      if (DEBUG) println(e.inContext("useAt(" + fact + ")(" + p + ")\n(" + s + ")" + "\nat " + s.sub(p)))
      false
    }

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val (ctx,expr) = node.sequent.at(p)
        val subst = inst(UnificationMatch(keyPart, expr))
        if (DEBUG) println("useAt(" + fact.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
        assert(expr == subst(keyPart), "unification matched left successfully: " + expr + " is " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)
        //val keyCtxMatched = Context(subst(keyCtx.ctx))
        Some(useAt(subst, keyCtx, keyPart, p, ctx, expr, factTactic, node.sequent))
      }

      /**
       * useAt(K{k})(C{c}) uses, already under the given substitution subst, the key k from context K{k}
       * in place of c at position p in context C{_}.
       * @param subst the substitution subst=unify(k,c)
       * @param K the context of fact in which key k occurs
       * @param k the key from context K{_} to use in place of c
       * @param p the position at which this useAt is applied to
       * @param C the context C{_} around the position p at which K{k} will be used
       * @param c the formula c at position p in context C{_} to be replaced by subst(k)
       * @param sequent the sequent in which this useAt happens.
       * @tparam T
       * @return
       * @author Andre Platzer
       */
      private def useAt[T <: Expression](subst: RenUSubst, K: Context[T], k: T, p: Position, C:Context[Formula], c:Expression, factTactic: Tactic, sequent: Sequent): Tactic = {
        require(subst(k) == c, "correctly matched input")
        require(C(c).at(p.inExpr) == (C,c), "correctly split at position p")
        require(List((C,DotFormula),(C,DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

        /** Equivalence rewriting step */
        def equivStep(other: Expression, factTactic: Tactic): Tactic = {
          val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
          //@note ctx(fml) is meant to put fml in for DotTerm in ctx, i.e apply the corresponding USubst.
        //@todo simplify substantially if subst=id
          debug("start useAt") & cutLR(C(subst(other)))(p.top) & debugC("  cutted right") & onBranch(
            //(BranchLabels.cutUseLbl, debugT("  useAt result")),
            //@todo would already know that ctx is the right context to use and subst(left)<->subst(right) is what we need to prove next, which results by US from left<->right
            //@todo could optimize equivalenceCongruenceT by a direct CE call using context ctx
            (BranchLabels.cutShowLbl, debugC("    show use") & cohide(cutPos) & assertT(0,1) & debugC("    cohidden") &
              equivifyR(SuccPosition(0)) & debugC("    equivified") &
              debugC("    CE coming up") & (
              if (other.kind==FormulaKind) CE(p.inExpr)
              else if (other.kind==TermKind) CQ(p.inExpr)
              else throw new IllegalArgumentException("Don't know how to handle kind " + other.kind + " of " + other)) &
              debugC("    using fact tactic") & factTactic & debugC("  done fact tactic"))
            //@todo error if factTactic is not applicable (factTactic | errorT)
          ) & debug("end   useAt")
        }

        K.ctx match {
          case DotFormula =>
            //@note this should be similar to byUS(fact) using factTactic to prove fact after instantiation
            US(Sequent(Nil, IndexedSeq(), IndexedSeq(k.asInstanceOf[Formula]))) & factTactic

          case Equiv(DotFormula, other) =>
            equivStep(other, PropositionalTacticsImpl.commuteEquivRightT(SuccPosition(0)) & factTactic)

          case Equiv(other, DotFormula) =>
            equivStep(other, factTactic)

          case Equal(DotTerm, other) =>
            equivStep(other, ArithmeticTacticsImpl.commuteEqualsT(SuccPosition(0)) & factTactic)

          case Equal(other, DotTerm) =>
            equivStep(other, factTactic)

          //@todo not sure if the following two cases really work as intended, but they seem to
          case Imply(other, DotFormula) if p.isSucc && p.isTopLevel =>
            cutR(subst(other))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, cohide(p.top) & factTactic)
            )

          case Imply(DotFormula, other) if p.isAnte && p.isTopLevel =>
            cutL(subst(other))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, lastSucc(cohide) & factTactic)
            )

          case Imply(other, DotFormula) if !(p.isSucc && p.isTopLevel) =>
            val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
            cutLR(C(subst(other)))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, cohide(cutPos) & implyR(SuccPos(0)) &
                AxiomaticRuleTactics.propositionalCongruenceT(p.inExpr) //@note simple approximation would be: ((Monb | Mond | allMon ...)*)
                // gather back to a single implication for axiom-based factTactic to succeed
                & PropositionalTacticsImpl.InverseImplyRightT
                & factTactic)
            )

          case Imply(DotFormula, other) if !(p.isAnte && p.isTopLevel) =>
            println("Check this useAt case")
            // same as "case Imply(other, DotFormula) if !(p.isSucc && p.isTopLevel)"
            val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
            cutLR(C(subst(other)))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, cohide(cutPos) & implyR(SuccPos(0)) &
                AxiomaticRuleTactics.propositionalCongruenceT(p.inExpr) //@note simple approximation would be: ((Monb | Mond | allMon ...)*)
                // gather back to a single implication for axiom-based factTactic to succeed
                & PropositionalTacticsImpl.InverseImplyRightT
                & factTactic)
            )


          case Imply(prereq, remainder) if StaticSemantics.signature(prereq).intersect(Set(DotFormula,DotTerm)).isEmpty =>
            //@todo could do: if prereq provable by master then use remainder directly. Otherwise use CMon to show C{prereq} implies ....
            //@todo only prove remainder absolutely by proving prereq if that proof works out. Otherwise preserve context to prove prereq by master.
            //@todo check positioning etc.
            useAt(subst, new Context(remainder), k, p, C, c, cutR(subst(prereq))(SuccPos(0)) & onBranch(
              //@note the roles of cutUseLbl and cutShowLbl are really swapped here, since the implication on cutShowLbl will be handled by factTactic
              //@todo don't work on prereq? Or make it customizable?
              (BranchLabels.cutUseLbl, /* prove prereq: */ TactixLibrary.master),
              (BranchLabels.cutShowLbl, /*PropositionalTacticsImpl.InverseImplyRightT &*/ factTactic)
            ), sequent)

          case Forall(vars, remainder) if vars.length==1 =>
            useAt(subst, new Context(remainder), k, p, C, c, instantiateQuanT(vars.head, subst(vars.head))(SuccPos(0)), sequent)

          //@todo unfold box by step*
          case Box(a, remainder) => ???
        }
      }
    }

  }

  /**
   * CQ(pos) at the indicated position within an equivalence reduces contextual equivalence to argument equality.
   * This tactic will use [[CE()]] under the hood as needed.
   * @param inEqPos the position *within* the two sides of the equivalence at which the context DotTerm happens.
   * @see [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
   */
  def CQ(inEqPos: PosInExpr): Tactic = new ConstructionTactic("CQ congruence") {outer =>
    import StaticSemantics._
    import StaticSemanticsTools._
    import Augmentors._
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length==1 &&
      (node.sequent.succ.head match {
        case Equiv(p, q) => p.at(inEqPos)._1 == q.at(inEqPos)._1
        case _ => false
      })

    private val f_ = FuncOf(Function("f_", None, Real, Real), Anything)
    private val g_ = FuncOf(Function("g_", None, Real, Real), Anything)
    private val c_ = PredOf(Function("ctx_", None, Real, Bool), DotTerm)
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Equiv(l, r) =>
        val (ctxF, f) = l.at(inEqPos)
        val (ctxG, g) = r.at(inEqPos)
        //@note Could skip the construction of ctxQ but it's part of the .at construction anyways.
        assert(!DEBUG || ctxF == ctxG, "same context if applicable (implied by AxiomaticRule applying successfully)")
        assert(!DEBUG || ctxF.ctx == ctxG.ctx, "same context formula if applicable (implied by AxiomaticRule applying successfully)")
        require(ctxF.isTermContext, "Formula context expected for CQ")
        if (DEBUG) println("CQ: boundAt(" + ctxF.ctx + "," + inEqPos + ")=" + boundAt(ctxF.ctx, inEqPos) + " intersecting FV(" + f + ")=" + freeVars(f) + "\\/FV(" + g + ")=" + freeVars(g) + " i.e. " + (freeVars(f)++freeVars(g)) + "\nIntersect: " + boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f)++freeVars(g)))
        if (boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f)++freeVars(g)).isEmpty)
          Some(new ApplyRule(AxiomaticRule("CQ equation congruence",
            USubst(SubstitutionPair(c_, ctxF.ctx) :: SubstitutionPair(f_, f) :: SubstitutionPair(g_, g) :: Nil)
          )) {
            override def applicable(node: ProofNode): Boolean = outer.applicable(node)
          })
        else {
          if (DEBUG) println("CQ: Split " + l + " around " + inEqPos)
          val (fmlPos,termPos) : (PosInExpr,PosInExpr) = Context.splitPos(l, inEqPos)
          if (DEBUG) println("CQ: Split " + l + " around " + inEqPos + "\ninto " + fmlPos + " and " + termPos + "\n  as " + l.at(fmlPos)._1 + " and " + Context.at(l.at(fmlPos)._2,termPos)._1)
          if (l.at(fmlPos)._2.isInstanceOf[Modal]) println(">>CE TACTIC MAY PRODUCE INFINITE LOOP<<")
          if (fmlPos==HereP) throw new IllegalStateException("CQ split void, would cause infinite loop unless stopped")
          //@todo could optimize to build directly since ctx already known
          Some(CE(fmlPos) & CQ(termPos))
        }
    }
  }

  /**
   * CE(pos) at the indicated position within an equivalence reduces contextual equivalence to argument equivalence.
   * @param inEqPos the position *within* the two sides of the equivalence at which the context DotFormula happens.
   * @see [[UnifyUSCalculus.CE(Context)]]
   * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
   * @see [[UnifyUSCalculus.CE(Provable)]]
   */
  def CE(inEqPos: PosInExpr): Tactic = new ConstructionTactic("CE congruence") {outer =>
    import Augmentors._
    override def applicable(node : ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length==1 &&
      (node.sequent.succ.head match {
        case Equiv(p, q) => p.at(inEqPos)._1 == q.at(inEqPos)._1
        case _ => false
      })

    private val p_ = PredOf(Function("p_", None, Real, Bool), Anything)
    private val q_ = PredOf(Function("q_", None, Real, Bool), Anything)
    private val c_ = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)
    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Equiv(l, r) if inEqPos==HereP =>
        //@note optimization: skip CE step if context already begins at HereP
        Some(TactixLibrary.skip)

      case Equiv(l, r) =>
        val (ctxP, p) = l.at(inEqPos)
        val (ctxQ, q) = r.at(inEqPos)
        //@note Could skip the construction of ctxQ but it's part of the .at construction anyways.
        assert(!DEBUG || ctxP == ctxQ, "same context if applicable (implied by AxiomaticRule applying successfully)")
        assert(!DEBUG || ctxP.ctx == ctxQ.ctx, "same context formula if applicable (implied by AxiomaticRule applying successfully)")
        require(ctxP.isFormulaContext, "Formula context expected for CE")
        Some(new ApplyRule(AxiomaticRule("CE congruence",
          USubst(SubstitutionPair(c_, ctxP.ctx) :: SubstitutionPair(p_, p) :: SubstitutionPair(q_, q) :: Nil)
        )) {
          override def applicable(node: ProofNode): Boolean = outer.applicable(node)
        })
    }
  }

  /**
   * CMon(pos) at the indicated position within an implication reduces contextual implication to argument implication.
   * @param inEqPos the position *within* the two sides of the implication at which the context DotFormula happens.
   * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see [[UnifyUSCalculus.CMon(Provable)]]
   */
  def CMon(inEqPos: PosInExpr): Tactic = new ConstructionTactic("CMon congruence") {
    import Augmentors._

    override def applicable(node: ProofNode): Boolean = node.sequent.ante.isEmpty && node.sequent.succ.length == 1 &&
      (node.sequent.succ.head match {
        case Imply(p, q) => p.at(inEqPos)._1 == q.at(inEqPos)._1
        case _ => false
      })

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = node.sequent.succ.head match {
      case Imply(l, r) if inEqPos == HereP =>
        //@note optimization: skip CMon step if context already begins at HereP
        Some(TactixLibrary.skip)
      case Imply(l, r) =>
        val (ctxP, p: Formula) = l.at(inEqPos)
        val (ctxQ, q: Formula) = r.at(inEqPos)
        assert(ctxP == ctxQ, "Contexts must be equal, but " + ctxP + " != " + ctxQ)
        Some(implyR(1) &
          by(CMon(ctxP)(Provable.startProof(Sequent(Nil, IndexedSeq(p), IndexedSeq(q))))) &
          by(inverseImplyR(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Imply(p, q)))))))
    }
  }

  /** CE(fact) uses the equivalence left<->right or equality left=right or implication left->right fact for congruence
    * reasoning at the indicated position to replace right by left at indicated position (literally, no substitution).
    * Efficient unification-free version of [[UnifyUSCalculus#useAt(Provable, PosInExpr):PositionTactic]]
    * @see [[UnifyUSCalculus.CE(Provable,Context)]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @example CE(fact) == CE(fact, Context("⎵".asFormula))
    */
  def CE(fact: Provable): PositionTactic = new PositionTactic("CE(Provable)") {
    import Augmentors._
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + fact)

    def splitFact: (Expression, Expression, Tactic, (PosInExpr=>Tactic)) = fact.conclusion.succ.head match {
      case Equal(l,r) => (l, r, equivifyR(SuccPosition(0)), CQ)
      case Equiv(l,r) => (l, r, equivifyR(SuccPosition(0)), CE)
      case Imply(l,r) => (l, r, skip, CMon)
      case _ => throw new IllegalArgumentException("CE expects equivalence or equality or implication fact " + fact)
    }
    val (other, key, equivify, tactic) = splitFact

    override def applies(s: Sequent, p: Position): Boolean =
      if (s.sub(p) == Some(key)) true
      else {if (DEBUG) println("In-applicable CE(" + fact + ") at " + p + " which is " + s.sub(p) + " at " + s); false}

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode): Boolean = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val (ctx,c) = node.sequent.at(p)
        val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(node.sequent.succ.length + 1)}
        Some(cutLR(ctx(other))(p.top) &
          onBranch(
            (BranchLabels.cutShowLbl, cohide(cutPos) & //assertT(0,1) &
              equivify & /*commuteEquivR(SuccPosition(0)) &*/
              tactic(p.inExpr) &
              by(fact)
              )
          )
        )
      }
    }
  }

  /** CE(fact) uses the equivalence left<->right or equality left=right or implication left->right fact for congruence
    * reasoning in the given context at the indicated position to replace right by left in that context (literally, no substitution).
    * @see [[UnifyUSCalculus.CE(Provable)]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    */
  def CE(fact: Provable, C: Context[Formula]): PositionTactic = new PositionTactic("CE(Provable,Context)") {
    import Augmentors._
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + fact)

    def splitFact: (Expression, Expression, Tactic, (Context[Formula]=>ForwardTactic)) = fact.conclusion.succ.head match {
      //@todo case Equal(l,r) => (l, r, equivifyR(SuccPosition(0)), CQ)
      case Equiv(l,r) => (l, r, equivifyR(SuccPosition(0)), CE)
      //@todo case Imply(l,r) => (l, r, skip, CMon)
      case _ => throw new IllegalArgumentException("CE expects equivalence or equality or implication fact " + fact)
    }
    val (other, key, equivify, tactic) = splitFact

    override def applies(s: Sequent, p: Position): Boolean =
      if (s.sub(p) == Some(C(key))) true
      else {if (DEBUG) println("In-applicable CE(" + fact + "," + C + ") at " + p + " which is " + s.sub(p) + " at " + s); false}

    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode): Boolean = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val (posctx,c) = node.sequent.at(p)
        val ctx = posctx(C)
        val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(node.sequent.succ.length + 1)}
        Some(cutLR(ctx(other))(p.top) &
          onBranch(
            (BranchLabels.cutShowLbl, cohide(cutPos) & //assertT(0,1) &
              equivify & /*commuteEquivR(SuccPosition(0)) &*/
              by(tactic(C)(fact))
              )
          )
        )
      }
    }
  }

  /*******************************************************************
    * unification and matching based auto-tactics (forward Hilbert)
    *******************************************************************/

  type ForwardTactic = (Provable => Provable)
  type ForwardPositionTactic = (Position => ForwardTactic)
  //@todo add the following def &() for composition and def | as implicit definitions to ForwardTactic
  def seqCompose(first: ForwardTactic, second: ForwardTactic): ForwardTactic = first andThen second
  def either(left: ForwardTactic, right: ForwardTactic): ForwardTactic =
    pr => try {left(pr)} catch { case _: ProverException => right(pr) }
  def ifThenElse(cond: Provable=>Boolean, thenT: ForwardTactic, elseT: ForwardTactic): ForwardTactic =
    pr => if (cond(pr)) thenT(pr) else elseT(pr)
  def seqComposeP(first: ForwardPositionTactic, second: ForwardPositionTactic): ForwardPositionTactic = pos => seqCompose(first(pos), second(pos))
  def eitherP(left: ForwardPositionTactic, right: ForwardPositionTactic): ForwardPositionTactic = pos => either(left(pos), right(pos))
  def ifThenElseP(cond: Position=>(Provable=>Boolean), thenT: ForwardPositionTactic, elseT: ForwardPositionTactic): ForwardPositionTactic = pos => ifThenElse(cond(pos), thenT(pos), elseT(pos))


  /** useFor(axiom) use the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String): ForwardPositionTactic = useFor(axiom, AxiomIndex.axiomIndex(axiom)._1)

  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr): ForwardPositionTactic =
    if (Axiom.axioms.contains(axiom)) useFor(Axiom.axiom(axiom), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(DerivedAxioms.derivedAxiom(axiom), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr, inst: RenUSubst=>RenUSubst): ForwardPositionTactic =
    if (Axiom.axioms.contains(axiom)) useFor(Axiom.axiom(axiom), key, inst)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(DerivedAxioms.derivedAxiom(axiom), key, inst)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

  /** CE(C) will wrap any equivalence left<->right or equality left=right fact it gets within context C.
    * Uses CE or CQ as needed.
    * @see [[CE(PosInExpr]]
    * @see [[CE(Provable)]]
    * @see [[CMon(Context)]]
    * @todo likewise for Context[Term] using CT instead.
    */
  def CE(C: Context[Formula]): ForwardTactic = equiv => {
    require(equiv.conclusion.ante.length==0 && equiv.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + equiv)
    equiv.conclusion.succ.head match {
      case Equiv(left,right) =>
        require(C.isFormulaContext, "Formula context expected to make use of equivalences with CE " + C)
        equiv(
          Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(C(left), C(right)))),
          AxiomaticRule("CE congruence",
            USubst(SubstitutionPair(PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula), C.ctx) ::
              SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), left) ::
              SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), right) ::
              Nil))
        )
      case Equal(left,right) =>
        require(C.isTermContext, "Term context expected to make use of equalities with CE " + C)
        equiv(
          Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(C(left), C(right)))),
          AxiomaticRule("CQ equation congruence",
            USubst(SubstitutionPair(PredOf(Function("ctx_", None, Real, Bool), DotTerm), C.ctx) ::
              SubstitutionPair(FuncOf(Function("f_", None, Real, Real), Anything), left) ::
              SubstitutionPair(FuncOf(Function("g_", None, Real, Real), Anything), right) ::
              Nil))
        )
      case _ => throw new IllegalArgumentException("expected equivalence or equality fact " + equiv.conclusion)
    }
  }

  /** CMon(C) will wrap any implication left->right fact it gets within a positive context C by monotonicity.
    * {{{
    *      k |- o
    *   ------------ CMon if C{⎵} of positive polarity
    *   C{k} |- C{o}
    * }}}
    * @note The direction in the conclusion switches for negative polarity C{⎵}
    * @see [[CE(Context)]]
    * @see [[AxiomaticRuleTactics.propositionalCongruenceT()]]
    */
  def CMon(C: Context[Formula]): ForwardTactic = impl => {
    import StaticSemantics.symbols
    require(impl.conclusion.ante.length == 1 && impl.conclusion.succ.length == 1, "expected equivalence shape without antecedent and exactly one succedent " + impl)
    //@todo require(DotFormula only occurs with positive polarity in C)
    val left = impl.conclusion.ante.head
    val right = impl.conclusion.succ.head
    require(C.isFormulaContext, "Formula context expected to make use of equivalences with CE " + C)
    if (DEBUG) println("CMon(" + C + ")" + "(" + impl + ")")
    /** Monotonicity rewriting step to replace occurrence of instance of k by instance of o in context */
    def monStep(C: Context[Formula], mon: Provable): Provable = {
      if (DEBUG) println("in monStep(" + C + ", " + mon + ")") //\nin CMon(" + C + ")" + "(" + impl + ")")
      var polarity = 1 // default is positive polarity
      var weakened = false  //@todo this is a hack that doesn't even quite work.
      (
        // which context to use it in
      C.ctx match {
        case DotFormula => mon

        case And(e, c) if !symbols(e).contains(DotFormula) =>
          (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(0), SuccPos(0)), 0)
            // right branch
            (CoHide2(AntePos(1), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

        case And(c, e) if !symbols(e).contains(DotFormula) =>
          (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(1), SuccPos(0)), 1)
            // left branch
            (CoHide2(AntePos(0), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

        case Or(e, c) if !symbols(e).contains(DotFormula) =>
          (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (OrRight(SuccPos(0)), 0)
            (OrLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(0)), 0)
            // right branch
            (CoHide2(AntePos(0), SuccPos(1)), 0)
            ) (monStep(Context(c), mon), 0)

        case Or(c, e) if !symbols(e).contains(DotFormula) =>
          (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (OrRight(SuccPos(0)), 0)
            (OrLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(1)), 1)
            // right branch
            (CoHide2(AntePos(0), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

        case Imply(e, c) if !symbols(e).contains(DotFormula) =>
          polarity = FormulaTools.polarityAt(C.ctx, FormulaTools.posOf(C.ctx, DotFormula).getOrElse(
            throw new IllegalArgumentException("Context should contain DotFormula")))
          val (ante, succ) =
            if (polarity < 0) (IndexedSeq(C(right)), IndexedSeq(C(left))) // polarity switch so switch left/right sides
            else (IndexedSeq(C(left)), IndexedSeq(C(right)))
          (Provable.startProof(Sequent(Nil, ante, succ))
            (ImplyRight(SuccPos(0)), 0)
            (ImplyLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(1)), 0)
            // right branch
            (CoHide2(AntePos(1), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

        case Imply(c, e) if !symbols(e).contains(DotFormula) =>
          polarity = FormulaTools.polarityAt(C.ctx, FormulaTools.posOf(C.ctx, DotFormula).getOrElse(
            throw new IllegalArgumentException("Context should contain DotFormula")))
          val (ante, succ) =
            if (polarity < 0) (IndexedSeq(C(right)), IndexedSeq(C(left))) // polarity switch so switch left/right sides
            else (IndexedSeq(C(left)), IndexedSeq(C(right)))
          println("CMon check case: " + C + " to prove " + Sequent(Nil, ante, succ) + "\nfrom " + mon)
          (Provable.startProof(Sequent(Nil, ante, succ))
            (ImplyRight(SuccPos(0)), 0)
            (ImplyLeft(AntePos(0)), 0)
            // right branch
            (Close(AntePos(1), SuccPos(0)), 1)
            // left branch
            (CoHide2(AntePos(0), SuccPos(1)), 0)
            ) (monStep(Context(c), mon), 0)

        case Equiv(e, c) if !symbols(e).contains(DotFormula) =>
          //@note fallback to implication
          // polarity(k)=-1, polarity(o)=+1
          weakened = true
          // orient equivalence Equiv(c,e) such that polarity of k in that will be +1
          // and polarity of o in that will be -1
          val newPol = FormulaTools.polarityAt(Imply(c,e), FormulaTools.posOf(Imply(c,e), DotFormula).getOrElse(
            throw new IllegalArgumentException("Context should contain DotFormula")))
          if (newPol<0) {
            // polarity of k in (Context(Imply(c,e))(k) will be +1
            // polarity of o in (Context(Imply(c,e))(o) will be -1
            monStep(Context(Imply(c, e)), mon)
          } else if (newPol>0) {
            assert(FormulaTools.polarityAt(Imply(e,c), FormulaTools.posOf(Imply(e,c), DotFormula).getOrElse(
              throw new IllegalArgumentException("Context should contain DotFormula")))>0)
            // polarity of k in (Context(Imply(e,c))(k) will be +1
            // polarity of o in (Context(Imply(e,c))(o) will be -1
            monStep(Context(Imply(e, c)), mon)
          } else {
            assert(false, "polarity rotations should ultimately be nonzero except with too many nested equivalences " + C); ???
          }

        case Equiv(c, e) if !symbols(e).contains(DotFormula) =>
          //@note fallback to implication
          // polarity(k)=-1, polarity(o)=+1
          weakened = true
          // orient equivalence Equiv(c,e) such that polarity of k in that will be +1
          // and polarity of o in that will be -1
          val newPol = FormulaTools.polarityAt(Imply(c,e), FormulaTools.posOf(Imply(c,e), DotFormula).getOrElse(
            throw new IllegalArgumentException("Context should contain DotFormula")))
          if (newPol<0) {
            // polarity of k in (Context(Imply(c,e))(k) will be +1
            // polarity of o in (Context(Imply(c,e))(o) will be -1
            monStep(Context(Imply(c, e)), mon)
          } else if (newPol>0) {
            assert(FormulaTools.polarityAt(Imply(e,c), FormulaTools.posOf(Imply(e,c), DotFormula).getOrElse(
              throw new IllegalArgumentException("Context should contain DotFormula")))>0)
            // polarity of k in (Context(Imply(e,c))(k) will be +1
            // polarity of o in (Context(Imply(e,c))(o) will be -1
            monStep(Context(Imply(e, c)), mon)
          } else {
            assert(false, "polarity rotations should ultimately be nonzero except with too many nested equivalences " + C); ???
          }

        case Equiv(e, c) => assert(symbols(e).contains(DotFormula) || symbols(c).contains(DotFormula), "proper contexts have dots somewhere " + C)
          throw new ProverException("No monotone context for equivalences " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")

        case Box(a, c) if !symbols(a).contains(DotFormula) =>
          (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (AxiomaticRule("[] monotone", USubst(
              SubstitutionPair(ProgramConst("a_"), a)
                :: SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Context(c)(left))
                :: SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Context(c)(right))
                :: Nil
            )
            ), 0)
            ) (monStep(Context(c), mon), 0)

        case Diamond(a, c) if !symbols(a).contains(DotFormula) =>
          (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (AxiomaticRule("<> monotone", USubst(
              SubstitutionPair(ProgramConst("a_"), a)
                :: SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Context(c)(left))
                :: SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Context(c)(right))
                :: Nil
            )
            ), 0)
            ) (monStep(Context(c), mon), 0)

        case m:Modal if symbols(m.program).contains(DotFormula) =>
          throw new ProverException("No monotone context within programs " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")

        case Forall(vars, c) => //if !StaticSemantics.freeVars(subst(c)).toSymbolSet.intersect(vars.toSet).isEmpty =>
          //@note would also work with all distribute and all generalization instead
          //@note would also work with Skolemize and all instantiate but disjointness is more painful
          useFor("all eliminate", PosInExpr(1::Nil))(AntePosition(0))(monStep(Context(c), mon)) (
            Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))),
            Skolemize(SuccPos(0))
          )

        /*case Forall(vars, c) if StaticSemantics.freeVars(subst(c)).toSymbolSet.intersect(vars.toSet).isEmpty =>
          useFor("vacuous all quantifier")(SuccPosition(0))(
            useFor("vacuous all quantifier")(AntePosition(0))(monStep(Context(c), mon))
          )*/

        case Exists(vars, c) =>
          //@note would also work with exists distribute and exists generalization instead
          //@note would also work with Skolemize and all instantiate but disjointness is more painful
          useFor("exists eliminate", PosInExpr(0::Nil))(SuccPosition(0))(monStep(Context(c), mon)) (
            Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))),
            Skolemize(AntePos(0))
          )

        //@todo flip polarity
        case Not(_) => throw new ProverException("No monotone context without polarity flipping for not " + K + "\nin CMon.monStep(" + C + ",\non " + mon + ")")

        case _ => throw new ProverException("Not implemented for other cases yet " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")
      }
        ) ensuring(r => weakened || r.conclusion == (if (polarity < 0)
        Sequent(Nil, IndexedSeq(C(right)), IndexedSeq(C(left)))
      else Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right)))), "Expected conclusion " + "\nin CMon.monStep(" + C + ",\non " + mon + ")"
        ) ensuring(r => !impl.isProved || r.isProved, "Proved if input fact proved" + "\nin CMon.monStep(" + C + ",\non " + mon + ")")
    }
    monStep(C, impl)
  }

  /** useFor(fact,key,inst) use the key part of the given fact forward for the selected position in the given Provable to conclude a new Provable
    * Forward Hilbert-style proof analogue of [[useAt()]].
    * @author Andre Platzer
    * @param fact the Provable whose conclusion  to use to simplify at the indicated position of the sequent
    * @param key the part of the fact's conclusion to unify the indicated position of the sequent with
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur in `fact.conclusion(key)`.
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @example useFor(Axiom.axiom("[;] compose"), PosInExpr(0::Nil))
    * applied to the indicated 1::1::Nil of
    * [x:=1;][{x'=22}] [x:=2*x;++x:=0;]x>=0
    * turns it into
    * [x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)
    * @see [[useAt()]]
    */
  def useFor(fact: Provable, key: PosInExpr, inst: RenUSubst=>RenUSubst = (us => us)): ForwardPositionTactic = {
    import Augmentors._
    val (keyCtx: Context[_], keyPart) = fact.conclusion(SuccPos(0)).at(key)
    if (DEBUG) println("useFor(" + fact.conclusion + ") key: " + keyPart + " in key context: " + keyCtx)

    pos => proof => {

      val (ctx, expr) = proof.conclusion.at(pos)
      val subst = inst(UnificationMatch(keyPart, expr))
      if (DEBUG) println("useFor(" + fact.conclusion.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
      if (DEBUG) println("useFor(" + fact.conclusion + ") on " + proof)
      assert(expr == subst(keyPart), "unification matched left successfully: " + expr + " is " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)

      /** useFor(subst, K,k, p, C,c)
        *
        * @param subst the substitution that unifies key k with occurrence c==subst(k).
        * @param K the context within which k occurs in fact.conclusion==K{k}
        * @param k the key
        * @param p the position at which occurrence c occurs in proof.conclusion
        * @param C the context within which occurrence c occurs in proof.conclusion(p.top)==C{c}
        * @param c the occurrence c at position p in proof.conclusion
        * @tparam T
        * @return The Provable following from proof by using key k of fact at p in proof.conclusion
        */
      def useFor[T <: Expression](subst: RenUSubst, K: Context[T], k: T, p: Position, C: Context[Formula], c: Expression): Provable = {
        assert(subst(k) == c, "correctly matched input")
        assert(fact.conclusion.succ.head==K(k), "correctly matched key in fact")
        assert(proof.conclusion(p.top)==C(c), "correctly matched occurrence in input proof")
        assert(C(c).at(p.inExpr) ==(C, c), "correctly split at position p")
        assert(List((C, DotFormula), (C, DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

        /** Equivalence rewriting step to replace occurrence of instance of key k by instance of other o in context */
        def equivStep(o: Expression, factTactic: Tactic): Provable = {
          //@todo delete factTactic argument since unused or use factTactic turned argument into Provable=>Provable
          require(fact.isProved, "currently want proved facts as input only")
          require(proof.conclusion.updated(p.top, C(subst(k)))==proof.conclusion, "expected context split")
          // |- fact: k=o or k<->o, respectively
          val sideUS: Provable = subst.toForward(fact)
          // |- subst(fact): subst(k)=subst(o) or subst(k)<->subst(o) by US
          val sideCE: Provable = CE(C)(sideUS)
          //@todo could shortcut proof by using "CO one-sided congruence" instead of CE
          // |- C{subst(k)} <-> C{subst(o)} by CQ or CE, respectively
          val sideImply: Provable = sideCE(Sequent(Nil, IndexedSeq(), IndexedSeq(Imply(C(subst(k)), C(subst(o))))),
            EquivifyRight(SuccPos(0)))
          // |- C{subst(k)}  -> C{subst(other)} by EquivifyRight
          //assert(C(subst(k)) == expr, "matched expression expected")
          val coside: Provable = sideImply(
            proof.conclusion.updated(p.top, Imply(C(subst(k)), C(subst(o)))),
            CoHideRight(p.top.asInstanceOf[SuccPos])
          )
          // G |- C{subst(k)}  -> C{subst(o)}, D by CoHideRight
          val proved = {Provable.startProof(proof.conclusion.updated(p.top, C(subst(o))))(
            CutRight(C(subst(k)), p.top.asInstanceOf[SuccPos]), 0
          ) (coside, 1)
          } ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
            ) ensuring(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")
          //                           *
          //                        ------
          // G |- C{subst(k)}, D    coside
          // ------------------------------ CutRight
          // G |- C{subst(o)}, D
          proved(proof, 0)
        } ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
          ) ensuring(r=>r.subgoals==proof.subgoals, "expected original premises")

        // in which context of the fact does the key occur
        K.ctx match {
          case Equal(DotTerm, o) =>
            equivStep(o, byUS(fact))

          case Equal(o, DotTerm) =>
            equivStep(o, ArithmeticTacticsImpl.commuteEqualsT(SuccPosition(0)) & byUS(fact))

          case Equiv(DotFormula, o) =>
            equivStep(o, byUS(fact))

          case Equiv(o, DotFormula) =>
            equivStep(o, PropositionalTacticsImpl.commuteEquivRightT(SuccPosition(0)) & byUS(fact))

          //@todo implies cases
          case Imply(o, DotFormula) =>
            // |- o->k
            val deduct = inverseImplyR(fact)
            // o |- k
            val sideUS: Provable = subst.toForward(deduct)
            // subst(o) |- subst(k) by US
            val Cmon = CMon(C)(sideUS)

            // C{subst(k)} |- C{subst(o)} for polarity < 0
            // C{subst(o)} |- C{subst(k)} for polarity > 0
            // C{subst(k)} |- Ci{subst(o)} for polarity = 0, where <-> in C are turned into -> in Ci
            val polarity = FormulaTools.polarityAt(C.ctx, pos.inExpr)  //@todo * (if (pos.isAnte) -1 else 1)
            val (kk, oo) =
              if (polarity < 0) (C(subst(k)), C(subst(o)))
              else if (polarity > 0) (C(subst(o)), C(subst(k)))
              else {
                assert(polarity ==0)
                val Ci = Context(FormulaTools.makePolarityAt(C.ctx, pos.inExpr, -1))
                (Ci(subst(k)), Ci(subst(o)))
              }

            val sideImply = Cmon(Sequent(Nil, IndexedSeq(), IndexedSeq(Imply(kk, oo))), ImplyRight(SuccPos(0)))

            // |- C{subst(o)} -> C{subst(k)}
            val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(proof.conclusion.succ.length)}
            val coside: Provable = sideImply(
              if (pos.isSucc) proof.conclusion.updated(p.top, Imply(kk, oo))
              //@note drop p.top too and glue
              else Sequent(Nil, proof.conclusion.ante.patch(p.top.getIndex,Nil,1), proof.conclusion.succ).
                glue(Sequent(Nil, IndexedSeq(), IndexedSeq(Imply(kk, oo)))),
              CoHideRight(cutPos)
            )
            // G |- C{subst(o)}  -> C{subst(k)}, D by CoHideRight
            val proved = {
              if (pos.isSucc)
                Provable.startProof(proof.conclusion.updated(pos.top, oo))(
                  CutRight(kk, pos.top.asInstanceOf[SuccPos]), 0
                ) (coside, 1)
                // G |- C{subst(o)}, D by CutRight with coside
              else
                //@todo flip o,k sides?
                Provable.startProof(proof.conclusion.updated(pos.top, oo))(
                  CutLeft(kk, pos.top.asInstanceOf[AntePos]), 0
                ) (coside, 1)
                // C{subst(o)}, G |- D by CutLeft with coside
              } /*ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
                ) ensuring(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")*/

            if (polarity == 0 && pos.isSucc) {
              val equivified = proved(Provable.startProof(proved.subgoals.head)(EquivifyRight(pos.top.asInstanceOf[SuccPos]), 0), 0)
              //@todo is equiv always top-level, so looking at inExpr.head determines direction?
              val commuted =
                if (pos.inExpr.head == 1) equivified(CommuteEquivRight(pos.top.asInstanceOf[SuccPos]), 0)
                else equivified
              commuted(proof, 0)
            } else if (polarity == 0 && pos.isAnte) {
              ???
            } else proved(proof, 0)

          //@todo check this case!
          case Imply(DotFormula, o) =>
            // |- k->o
            val deduct = inverseImplyR(fact)
            // k |- o
            val sideUS: Provable = subst.toForward(deduct)
            // subst(k) |- subst(o) by US
            val Cmon = CMon(C)(sideUS)

            // C{subst(o)} |- C{subst(k)} for polarity > 0
            // C{subst(k)} |- C{subst(o)} for polarity < 0
            val polarity = FormulaTools.polarityAt(C.ctx, pos.inExpr)
            //@todo relax the context C if CMon met an equivalence here, see case above.
            assert(polarity != 0, "Polarity should be either positive or negative. Polarity 0 of equivalences not supported: " + C) // polarity 0: met an <->
            val impl = if (polarity < 0) Imply(C(subst(o)), C(subst(k))) else Imply(C(subst(k)), C(subst(o)))

            val sideImply = Cmon(Sequent(Nil, IndexedSeq(), IndexedSeq(impl)),
              ImplyRight(SuccPos(0))
            )
            // |- C{subst(k)} -> C{subst(o)}
            val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(proof.conclusion.succ.length)}
            val coside: Provable = sideImply(
              if (pos.isSucc) proof.conclusion.updated(p.top, impl)
              //@note drop p.top too and glue
              else Sequent(Nil, proof.conclusion.ante.patch(p.top.getIndex,Nil,1), proof.conclusion.succ).
                glue(Sequent(Nil, IndexedSeq(), IndexedSeq(impl))),
              CoHideRight(cutPos)
            )
            // G |- C{subst(k)}  -> C{subst(o)}, D by CoHideRight
            val proved = {Provable.startProof(proof.conclusion.updated(pos.top, C(subst(o))))(
              //@todo CutLeft if pos is AntePos
              CutRight(C(subst(k)), pos.top.asInstanceOf[SuccPos]), 0
            ) (coside, 1)
              // G |- C{subst(k)}  -> C{subst(o)}, D by CoHideRight
            } /*ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
              ) ensuring(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")*/
            proved(proof, 0)

          case Imply(prereq, remainder) if StaticSemantics.signature(prereq).intersect(Set(DotFormula,DotTerm)).isEmpty =>
            throw new ProverException("Not implemented for other cases yet, see useAt: " + K)

          case _ => throw new ProverException("Not implemented for other cases yet, see useAt: " + K)
        }
      }
      val r = useFor(subst, keyCtx, keyPart, pos, ctx, expr)
      if (DEBUG) println("useFor(" + fact.conclusion + ") on " + proof + "\n ~~> " + r)
      r
    }
  }

  /**
   * {{{
   *   G |- a -> b, D
   * ----------------
   *   G, a |- b, D
   * }}}
   * @see [[PropositionalTacticsImpl.InverseImplyRightT]]
   */
  private def inverseImplyR: ForwardTactic = pr => {
    val pos = SuccPos(0)
    val last = AntePos(pr.conclusion.ante.length)
    val Imply(a,b) = pr.conclusion.succ.head
    (Provable.startProof(pr.conclusion.updated(pos, b).glue(Sequent(Nil, IndexedSeq(a), IndexedSeq())))
      (CutRight(a, pos), 0)
      // left branch
      (Close(last, pos), 0)
      // right branch
      (HideLeft(last), 0)
      ) (pr, 0)
    /*(Provable.startProof(pr.conclusion.updated(pos, b).glue(Sequent(Nil, IndexedSeq(a), IndexedSeq())))
      (Cut(Imply(a,b), pos), 0)
      // right branch
      (HideLeft(last), 1)
      // left branch
      (ImplyLeft(last), 0)
      // left.right branch
      (Close(last, pos), 2)
      // left.left branch
      (Close(last, pos), 0)
      // right branch
      ) (pr, 0)*/
  }

  /*******************************************************************
    * Computation-based auto-tactics
    *******************************************************************/

  /** Chases the expression at the indicated position forward until it is chased away or can't be chased further without critical choices. */
  lazy val chase: PositionTactic = chase(3,3)

  /** Chase with bounded breadth and giveUp to stop.
    * @param breadth how many alternative axioms to pursue locally, using the first applicable one.
    *                Equivalent to pruning keys so that all lists longer than giveUp are replaced by Nil,
    *                and then all lists are truncated beyond breadth.
    * @param giveUp  how many alternatives are too much so that the chase stops without trying any for applicability.
    *                Equivalent to pruning keys so that all lists longer than giveUp are replaced by Nil.
    */
  def chase(breadth: Int, giveUp: Int): PositionTactic = chase(breadth, giveUp, AxiomIndex.axiomsFor _)
  def chase(breadth: Int, giveUp: Int, keys: Expression=>List[String]): PositionTactic = chase(breadth, giveUp, keys, (ax,pos) => pr=>pr)
  def chase(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic): PositionTactic =
    chaseI(breadth, giveUp,keys, modifier, ax=>us=>us)
  def chaseI(breadth: Int, giveUp: Int, keys: Expression=>List[String], inst: String=>(RenUSubst=>RenUSubst)): PositionTactic =
    chaseI(breadth, giveUp, keys, (ax,pos)=>pr=>pr, inst)
  def chaseI(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic, inst: String=>(RenUSubst=>RenUSubst)): PositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chase(e => keys(e) match {
      case l:List[String] if l.size > giveUp => Nil
      case l:List[String] => l.take(breadth)
    }, modifier, inst)
  }

  def chaseFor(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic): ForwardPositionTactic =
    chaseFor(breadth, giveUp,keys, modifier, ax=>us=>us)
  def chaseFor(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic, inst: String=>(RenUSubst=>RenUSubst)): ForwardPositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chaseFor(e => keys(e) match {
      case l:List[String] if l.size > giveUp => Nil
      case l:List[String] => l.take(breadth)
    }, modifier, inst)
  }

  /** chase: Chases the expression at the indicated position forward until it is chased away or can't be chased further without critical choices.
    *
    * Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
    * Follows canonical axioms toward all their recursors while there is an applicable simplifier axiom according to `keys`.
    * @param keys maps expressions to a list of axiom names to be used for those expressions.
    *             First returned axioms will be favored (if applicable) over further axioms.
    * @param modifier will be notified after successful uses of axiom at a position with the result of the use.
    *                 The result of modifier(ax,pos)(step) will be used instead of step for each step of the chase.
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur when using the given axiom _1.
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @note Chase is search-free and, thus, quite efficient. It directly follows the
    *       [[AxiomIndex.axiomIndex() axiom index]] information to compute follow-up positions for the chase.
    * @example When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+(x'*y+x*y')>=0
    * @example When applied at Nil, turns [?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into ((x>0->x+1>=1) & (x=0->1>=1))
    * @example When applied at 1::Nil, turns [{x'=22}][?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into [{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))
    * @see [[HilbertCalculus.derive]]
    * @see [[chaseFor()]]
    * @todo also implement a backwards chase in tableaux/sequent style based on useAt instead of useFor
    */
  def chase(keys: Expression=>List[String],
            modifier: (String,Position)=>ForwardTactic,
            inst: String=>(RenUSubst=>RenUSubst) = ax=>us=>us): PositionTactic = new PositionTactic("chase") {
    import Augmentors._

    //@note True has no applicable keys. This applicability is still an overapproximation since it does not check for clashes.
    override def applies(s: Sequent, p: Position): Boolean = {
      val sub = s.sub(p)
      if (!sub.isDefined) {
        if (DEBUG) println("ill-positioned " + p + " in " + s + "\nin " + "chase\n(" + s + ")")
        return false
      }
      !(keys(sub.get).isEmpty)
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        //Some(useAt(chaseProof(node.sequent.at(p).get), PosInExpr(0::Nil))(p))
        Some(CE(chaseProof(node.sequent.sub(p).get))(p))

      /** Construct a proof proving the answer of the chase of e, so either of e=chased(e) or e<->chased(e) */
      private def chaseProof(e: Expression): Provable = {
        // reflexive setup corresponds to no-progress chase
        val initial: Provable = e match {
          case t: Term =>      // t=t
            DerivedAxioms.equalReflex.fact(
              Sequent(Nil, IndexedSeq(), IndexedSeq(Equal(t,t))),
              UniformSubstitutionRule(USubst(SubstitutionPair(FuncOf(Function("s",None,Unit,Real),Nothing), t)::Nil),
                DerivedAxioms.equalReflex.fact.conclusion))
          case f: Formula =>   // f<->f
            DerivedAxioms.equivReflexiveAxiom.fact(
              Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(f,f))),
              UniformSubstitutionRule(USubst(SubstitutionPair(PredOf(Function("p",None,Unit,Bool),Nothing), f)::Nil),
                DerivedAxioms.equivReflexiveAxiom.fact.conclusion))
        }
        assert(initial.isProved && initial.conclusion.ante.isEmpty && initial.conclusion.succ.length==1, "Proved reflexive start " + initial + " for " + e)
        if (DEBUG) println("chase starts at " + initial)
        //@note start the chase on the left-hand side
        val r = chaseFor(keys, modifier, inst) (SuccPosition(0, PosInExpr(0::Nil)))(initial)
        if (DEBUG) println("chase(" + e.prettyString + ") = ~~> " + r + " done")
        r
      } ensuring(r => r.isProved, "chase remains proved: " + " final chase(" + e + ")")
    }
  }

  /** chaseFor: Chases the expression of Provables at given positions forward until it is chased away or can't be chased further without critical choices.
    *
    * Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
    * Follows canonical axioms toward all their recursors while there is an applicable simplifier axiom according to `keys`.
    * @param keys maps expressions to a list of axiom names to be used for those expressions.
    *             First returned axioms will be favored (if applicable) over further axioms.
    * @param modifier will be notified after successful uses of axiom at a position with the result of the use.
    *                 The result of modifier(ax,pos)(step) will be used instead of step for each step of the chase.
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur when using the given axiom _1.
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @note Chase is search-free and, thus, quite efficient. It directly follows the
    *       [[AxiomIndex.axiomIndex() axiom index]] information to compute follow-up positions for the chase.
    * @example When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+(x'*y+x*y')>=0
    * @example When applied at Nil, turns [?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into ((x>0->x+1>=1) & (x=0->1>=1))
    * @example When applied at 1::Nil, turns [{x'=22}][?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into [{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))
    * @see [[chase()]]
    * @see [[HilbertCalculus.derive]]
    * @see [[UnifyUSCalculus.useFor()]]
    */
  def chaseFor(keys: Expression=>List[String],
               modifier: (String,Position)=>ForwardTactic,
               inst: String=>(RenUSubst=>RenUSubst) = ax=>us=>us): ForwardPositionTactic = pos => de => {
    import AxiomIndex.axiomIndex
    import Augmentors._
    /** Recursive chase implementation */
    def doChase(de: Provable, pos: Position): Provable = {
      if (DEBUG) println("chase(" + de.conclusion.sub(pos).get.prettyString + ")")
      // generic recursor
      keys(de.conclusion.sub(pos).get) match {
        case Nil =>
          if (DEBUG) println("no chase(" + de.conclusion.sub(pos).get.prettyString + ")")
          de
        /*throw new IllegalArgumentException("No axiomFor for: " + expr)*/
        case List(ax) =>
          val (key, recursor) = axiomIndex(ax)
          try {
            val axUse = modifier(ax,pos) (useFor(ax, key, inst(ax))(pos)(de))
            recursor.foldLeft(axUse)(
              (pf, cursor) => doChase(pf, pos.append(cursor))
            )
          } catch {case e: ProverException => throw e.inContext("useFor(" + ax + ", " + key.prettyString + ")\nin " + "chase(" + de.conclusion.sub(pos).get.prettyString + ")")}
        // take the first axiom among breadth that works for one useFor step
        case l: List[String] =>
          // useFor the first applicable axiom if any, or None
          def firstAxUse: Option[(Provable,List[PosInExpr])] = {
            for (ax <- l) try {
              val (key, recursor) = axiomIndex(ax)
              return Some((modifier(ax,pos) (useFor(ax, key, inst(ax))(pos)(de)), recursor))
            } catch {case _: ProverException => /* ignore and try next */}
            None
          }
          firstAxUse match {
            case None =>
              if (DEBUG) println("no chase(" + de.conclusion.sub(pos).get.prettyString + ")")
              de
            case Some((axUse, recursor)) =>
              recursor.foldLeft(axUse)(
                (pf, cursor) => doChase(pf, pos.append(cursor))
              )
          }
      }
    } ensuring(r => r.subgoals==de.subgoals, "chase keeps subgoals unchanged: " + " final chase(" + de.conclusion.sub(pos).get.prettyString + ")\nhad subgoals: " + de.subgoals)
    doChase(de,pos)
  }


  /** An update-based calculus launched at a position */
  def updateCalculus: PositionTactic = chase(3,3, (e:Expression) => e match {
      // no equational assignments
      case Box(Assign(_,_),_)    => "[:=] assign" :: "[:=] assign update" :: Nil
      case Diamond(Assign(_,_),_) => "<:=> assign" :: "<:=> assign update" :: Nil
      case _ => AxiomIndex.axiomsFor(e)
    }
  )

  /** Debug output s (for forward tactics) */
  def debugF(s: => Any): ForwardTactic=>ForwardTactic = tac => proof => {val pr = tac(proof); if (DEBUG) println("=== " + s + " === " + pr); pr}
  /** Debug output s (for forward positional tactics) */
  def debugPF(s: => Any): ForwardPositionTactic=>ForwardPositionTactic = tac => pos => proof => {val pr = tac(pos)(proof); if (DEBUG) println("=== " + s + " === " + pr); pr}

}
