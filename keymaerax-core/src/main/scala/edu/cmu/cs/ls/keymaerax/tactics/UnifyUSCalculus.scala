/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ByProvable, ConstructionTactic, PositionTactic, Tactic}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.UnificationMatch
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable._

/**
 * Automatic unification-based Uniform Substitution Calculus with indexing.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see [[AxiomIndex.axiomIndex()]]
 */
trait UnifyUSCalculus {
  import Tactic.DEBUG

  type Subst = UnificationMatch.Subst

  /*******************************************************************
    * unification and matching based auto-tactics
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
  private[tactics] def useDirectAt(fact: Provable, key: PosInExpr): PositionTactic = {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
    require(fact.isProved, "(no strict requirement, but) the best usable facts are proved " + fact)
    useAt(fact.conclusion.succ.head, key, by(fact))
  }
  /** useAt(lem)(pos) uses the given lemma at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(lem: Lemma, key:PosInExpr, inst: Subst=>Subst): PositionTactic = useAt(lem.fact, key, inst)
  def useAt(lem: Lemma, key:PosInExpr): PositionTactic = useAt(lem.fact, key)
  def useAt(lem: Lemma, inst: Subst=>Subst) : PositionTactic = useAt(lem.fact, PosInExpr(0::Nil), inst)
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
  //@todo once complete, AxiomIndex.axiomIndex(axiom)._1 can be used as default key
  def useAt(axiom: String, inst: Subst=>Subst): PositionTactic = useAt(axiom, PosInExpr(0::Nil), inst)
  def useAt(axiom: String): PositionTactic = useAt(axiom, PosInExpr(0::Nil))

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
    * unification and matching based auto-tactics
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
    } catch {case e: ProverException => println(e.inContext("US(" + form + ")\n(" + node.sequent + ") inapplicable since un-unifiable")); false}

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
   * @see [[useFor()]]
   * @todo could directly use prop rules instead of CE if key close to HereP if more efficient.
   */
  def useAt(fact: Formula, key: PosInExpr, factTactic: Tactic, inst: Subst=>Subst = (us=>us)): PositionTactic = new PositionTactic("useAt") {
    import PropositionalTacticsImpl._
    import FormulaConverter._
    import SequentConverter._
    import TactixLibrary.assertT
    import TactixLibrary.debug
    import TacticLibrary.debugC
    import TacticLibrary.instantiateQuanT
    import SearchTacticsImpl.lastSucc
    private val (keyCtx:Context[_],keyPart) = fact.extractContext(key)
    //private val keyPart = new FormulaConverter(fact).subFormulaAt(key).get

    override def applies(s: Sequent, p: Position): Boolean = try {
      val part = s.at(p)
      if (!part.isDefined) {println("ill-positioned " + p + " in " + s + "\nin " + "useAt(" + fact + ")(" + p + ")\n(" + s + ")"); false}
      else {
        UnificationMatch(keyPart,part.get)
        true
      }
    } catch {case e: ProverException => println(e.inContext("useAt(" + fact + ")(" + p + ")\n(" + s + ")" + "\nat " + s.at(p))); false}

    def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode) = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val (ctx,expr) = node.sequent.splitContext(p)
        val subst = inst(UnificationMatch(keyPart, expr))
        if (DEBUG) println("useAt(" + fact.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
        assert(expr == subst(keyPart), "unification matched left successfully: " + expr + " is " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)
        //val keyCtxMatched = Context(subst(keyCtx.ctx))
        Some(useAt(subst, keyCtx, keyPart, p, ctx, expr, factTactic))
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
       * @tparam T
       * @return
       * @author Andre Platzer
       */
      private def useAt[T <: Expression](subst: RenUSubst, K: Context[T], k: T, p: Position, C:Context[Formula], c:Expression, factTactic: Tactic): Tactic = {
        require(subst(k) == c, "correctly matched input")
        require(C(c).extractContext(p.inExpr) == (C,c), "correctly split at position p")
        require(List((C,DotFormula),(C,DotTerm)).contains(C.ctx.extractContext(p.inExpr)), "correctly split at position p")

        /** Equivalence rewriting step */
        def equivStep(other: Expression, factTactic: Tactic): Tactic =
        //@note ctx(fml) is meant to put fml in for DotTerm in ctx, i.e apply the corresponding USubst.
        //@todo simplify substantially if subst=id
          debug("start useAt") & cutRightT(C(subst(other)))(p.top) & debugC("  cutted right") & onBranch(
            //(BranchLabels.cutUseLbl, debugT("  useAt result")),
            //@todo would already know that ctx is the right context to use and subst(left)<->subst(right) is what we need to prove next, which results by US from left<->right
            //@todo could optimize equivalenceCongruenceT by a direct CE call using context ctx
            (BranchLabels.cutShowLbl, debugC("    show use") & cohideT(p.top) & assertT(0,1) & debugC("    cohidden") &
              equivifyRightT(SuccPosition(0)) & debugC("    equivified") &
              debugC("    CE coming up") & (
              if (other.kind==FormulaKind) AxiomaticRuleTactics.equivalenceCongruenceT(p.inExpr)
              else if (other.kind==TermKind) AxiomaticRuleTactics.equationCongruenceT(p.inExpr)
              else throw new IllegalArgumentException("Don't know how to handle kind " + other.kind + " of " + other)) &
              debugC("    using fact tactic") & factTactic & debugC("  done fact tactic"))
            //@todo error if factTactic is not applicable (factTactic | errorT)
          ) & debug("end   useAt")

        K.ctx match {
          case DotFormula =>
            //@note this should be similar to byUS(fact) using factTactic to prove fact after instantiation
            US(Sequent(Nil, IndexedSeq(), IndexedSeq(k.asInstanceOf[Formula]))) & factTactic

          case Equiv(DotFormula, other) =>
            equivStep(other, commuteEquivRightT(SuccPosition(0)) & factTactic)

          case Equiv(other, DotFormula) =>
            equivStep(other, factTactic)

          case Equal(DotTerm, other) =>
            equivStep(other, ArithmeticTacticsImpl.commuteEqualsT(SuccPosition(0)) & factTactic)

          case Equal(other, DotTerm) =>
            equivStep(other, factTactic)

          //@todo not sure if the following two cases really work as intended, but they seem to
          case Imply(other, DotFormula) if p.isSucc && p.isTopLevel =>
            cutRightT(subst(other))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, cohideT(p.top) & factTactic)
            )

          case Imply(DotFormula, other) if p.isAnte && p.isTopLevel =>
            cutLeftT(subst(other))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, lastSucc(cohideT) & factTactic)
            )

          case Imply(other, DotFormula) if !(p.isSucc && p.isTopLevel) =>
            cutRightT(C(subst(other)))(p.top) & onBranch(
              (BranchLabels.cutShowLbl, cohideT(p.top) & implyR(SuccPos(0)) &
                AxiomaticRuleTactics.propositionalCongruenceT(p.inExpr) //@todo simple approximation would be: ((Monb | Mond | allMon ...)*)
                & factTactic)
            )

          case Imply(DotFormula, other) if !(p.isAnte && p.isTopLevel) => ???

          case Imply(prereq, remainder) if StaticSemantics.signature(prereq).intersect(Set(DotFormula,DotTerm)).isEmpty =>
            //@todo only prove remainder absolutely by proving prereq if that proof works out. Otherwise preserve context to prove prereq by master.
            //@todo check positioning etc.
            useAt(subst, new Context(remainder), k, p, C, c, cutRightT(subst(prereq))(SuccPos(0)) & onBranch(
              //@note the roles of cutUseLbl and cutShowLbl are really swapped here, since the implication on cutShowLbl will be handled by factTactic
              (BranchLabels.cutUseLbl, /* prove prereq: */ TactixLibrary.master),
              (BranchLabels.cutShowLbl, /*PropositionalTacticsImpl.InverseImplyRightT &*/ factTactic)
            ))

          case Forall(vars, remainder) if vars.length==1 =>
            useAt(subst, new Context(remainder), k, p, C, c, instantiateQuanT(vars.head, subst(vars.head))(SuccPos(0)))

          //@todo unfold box by step*
          case Box(a, remainder) => ???
        }
      }
    }

  }

  /** useFor(axiom) use the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String): (Position => (Provable => Provable)) = useFor(axiom, PosInExpr(0::Nil))

  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr): (Position => (Provable => Provable)) =
    if (Axiom.axioms.contains(axiom)) useFor(Axiom.axiom(axiom), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(DerivedAxioms.derivedAxiom(axiom), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

  /** useFor(fact,key,inst) use the key part of the given fact forward for the selected position in the given Provable to conclude a new Provable
    * Forward Hilbert-style proof analogue of [[useAt()]].
    * @author Andre Platzer
    * @param fact the Provable whose conclusion  to use to simplify at the indicated position of the sequent
    * @param key the part of the fact's conclusion to unify the indicated position of the sequent with
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur in `fact.conclusion(key)`.
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @see [[useAt()]]
    */
  def useFor(fact: Provable, key: PosInExpr, inst: RenUSubst=>RenUSubst = (us => us)): (Position => (Provable => Provable)) = {
    import FormulaConverter._
    import SequentConverter._
    //import TactixLibrary._
    val (keyCtx: Context[_], keyPart) = fact.conclusion(SuccPos(0)).extractContext(key)
    if (DEBUG) println("useFor(" + fact.conclusion + ") key: " + keyPart + " in key context: " + keyCtx)

    val HISTORY=false

    pos => proof => {

      val (ctx, expr) = proof.conclusion.splitContext(pos)
      val subst = inst(UnificationMatch(keyPart, expr))
      if (DEBUG) println("useFor(" + fact.conclusion.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
      if (DEBUG) println("useFor(" + fact.conclusion + ") on " + proof)
      assert(expr == subst(keyPart), "unification matched left successfully: " + expr + " is " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)

      def useFor[T <: Expression](subst: RenUSubst, K: Context[T], k: T, p: Position, C: Context[Formula], c: Expression): Provable =
      {
        require(subst(k) == c, "correctly matched input")
        require(C(c).extractContext(p.inExpr) ==(C, c), "correctly split at position p")
        require(List((C, DotFormula), (C, DotTerm)).contains(C.ctx.extractContext(p.inExpr)), "correctly split at position p")

        /** Equivalence rewriting step */
        def equivStep(other: Expression, factTactic: Tactic): Provable = {
          //@todo delete factTactic or use factTactic turned argument into Provable=>Provable
          require(fact.isProved, "currently want proved facts as input only")
          require(proof.conclusion.updated(p.top, C(subst(k)))==proof.conclusion, "expected context split")
          // |- fact: k=o
          val sideUS: Provable = subst.toForward(fact)
          // |- subst(fact): subst(k)=subst(o) by US
          /*(
            subst(fact.conclusion)
            ,
            AxiomaticRule("CT term congruence",
              USubst(SubstitutionPair(FuncOf(Function("ctx_", None, Real, Real), DotTerm), DotTerm) ::
                SubstitutionPair(FuncOf(Function("f_", None, Real, Real), Anything), subst(k)) ::
                SubstitutionPair(FuncOf(Function("g_", None, Real, Real), Anything), subst(other)) ::
                Nil))
//            AxiomaticRule("CQ equation congruence",
//            USubst(SubstitutionPair(PredOf(Function("ctx_", None, Real, Bool), Anything), C.ctx) :: Nil))
          )*/
          val sideCE = sideUS(
            Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(C(subst(k)), C(subst(other)))))
            ,
            k.kind match {
              case TermKind => AxiomaticRule("CQ equation congruence",
                USubst(SubstitutionPair(PredOf(Function("ctx_", None, Real, Bool), DotTerm), C.ctx) ::
                  SubstitutionPair(FuncOf(Function("f_", None, Real, Real), Anything), subst(k)) ::
                  SubstitutionPair(FuncOf(Function("g_", None, Real, Real), Anything), subst(other)) ::
                  Nil))
              case FormulaKind => AxiomaticRule("CE congruence",
                USubst(SubstitutionPair(PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula), C.ctx) ::
                  SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), subst(k)) ::
                  SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), subst(other)) ::
                  Nil))
            }
          )
          // |- C{subst(k)} <-> C{subst(o)} by CQ
          //          val sideSwap = sideCE(
          //            Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(C(subst(other)), C(subst(k))))),
          //            CommuteEquivRight(SuccPos(0))
          //          )
          //          // |- C{subst(o)} <-> C{subst(k)} by CommuteEquivRight
          val side2: Provable = sideCE(Sequent(Nil, IndexedSeq(), IndexedSeq(Imply(C(subst(k)), C(subst(other))))),
            EquivifyRight(SuccPos(0)))
          // |- C{subst(k)}  -> C{subst(other)} by EquivifyRight
          //assert(C(subst(k)) == expr, "matched expression expected")
          val coside: Provable = side2(
            proof.conclusion.updated(p.top, Imply(C(subst(k)), C(subst(other)))),
            CoHideRight(p.top.asInstanceOf[SuccPos])
          )
          // G |- C{subst(k)}  -> C{subst(other)}, D by CoHideRight
          val proved = {Provable.startProof(proof.conclusion.updated(p.top, C(subst(other))))(
            CutRight(C(subst(k)), p.top.asInstanceOf[SuccPos]), 0
          ) (coside, 1)
          } ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(other))), "prolonged conclusion"
            ) ensuring(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")
          //                           *
          //                        ------
          // G |- C{subst(k)}, D    coside
          // ------------------------------ CutRight
          // G |- C{subst(o)}, D
          proved(proof, 0)

          //
          //          //fact(Sequent(Nil,IndexedSeq(),IndexedSeq(Equal(subst(k), subst(c)))),
          //          proof(proof.conclusion.updated(pos.top, C(subst(other))), CutRight(C(subst(other)), pos.top.asInstanceOf[SuccPos]))
          //          //@note ctx(fml) is meant to put fml in for DotTerm in ctx, i.e apply the corresponding USubst.
          //          cutRightT(C(subst(other)))(p.top) & onBranch(
          //            //(BranchLabels.cutUseLbl, debugT("  useAt result")),
          //            //@todo would already know that ctx is the right context to use and subst(left)<->subst(right) is what we need to prove next, which results by US from left<->right
          //            //@todo could optimize equivalenceCongruenceT by a direct CE call using context ctx
          //            (BranchLabels.cutShowLbl, cohideT(p.top) /*& assertT(0,1)*/ &
          //              equivifyRightT(SuccPosition(0)) & (
          //              if (other.kind == FormulaKind) AxiomaticRuleTactics.equivalenceCongruenceT(p.inExpr)
          //              else if (other.kind == TermKind) AxiomaticRuleTactics.equationCongruenceT(p.inExpr)
          //              else throw new IllegalArgumentException("Don't know how to handle kind " + other.kind + " of " + other)) &
          //              factTactic)
          //            //@todo error if factTactic is not applicable (factTactic | errorT)
          //          )
        } ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(other))), "prolonged conclusion"
          ) ensuring(r=>r.subgoals==proof.subgoals, "expected original premises")

        K.ctx match {
          case Equal(DotTerm, other) =>
            //@todo this is convoluted and inefficient compared to a direct forward proof
            //@todo commute
            if (HISTORY) TactixLibrary.proveBy(fact.conclusion.updated(pos.top, C(subst(other))),
              useAt(fact.conclusion.succ.head, key.sibling, byUS(fact), inst)(p))
            else
              equivStep(other, byUS(fact))

          case Equal(other, DotTerm) =>
            //@todo this is convoluted and inefficient compared to a direct forward proof
            if (HISTORY) TactixLibrary.proveBy(fact.conclusion.updated(pos.top, C(subst(other))),
              useAt(fact.conclusion.succ.head, key.sibling, ArithmeticTacticsImpl.commuteEqualsT(SuccPosition(0)) & byUS(fact), inst)(p))
            else
              equivStep(other, ArithmeticTacticsImpl.commuteEqualsT(SuccPosition(0)) & byUS(fact))

          case Equiv(DotFormula, other) =>
            //@todo this is convoluted and inefficient compared to a direct forward proof
            //@todo commute
            if (HISTORY) TactixLibrary.proveBy(fact.conclusion.updated(pos.top, C(subst(other))),
              useAt(fact.conclusion.succ.head, key.sibling, byUS(fact), inst)(p))
            else
              equivStep(other, byUS(fact))

          case Equiv(other, DotFormula) =>
            //@todo this is convoluted and inefficient compared to a direct forward proof
            if (HISTORY) TactixLibrary.proveBy(fact.conclusion.updated(pos.top, C(subst(other))),
              useAt(fact.conclusion.succ.head, key.sibling, PropositionalTacticsImpl.commuteEquivRightT(SuccPosition(0)) & byUS(fact), inst)(p))
            else
              equivStep(other, PropositionalTacticsImpl.commuteEquivRightT(SuccPosition(0)) & byUS(fact))
        }
      }
      val r = useFor(subst, keyCtx, keyPart, pos, ctx, expr)
      if (DEBUG) println("useFor(" + fact.conclusion + ") on " + proof + "\n ~~> " + r)
      r
    }
  }

  /*******************************************************************
    * Computation-based auto-tactics
    *******************************************************************/

  lazy val chase: PositionTactic = chaseWide(1,3)

  def chaseWide(breadth: Int): PositionTactic = chaseWide(breadth, 2*breadth)

  private def unprog: PositionTactic = chaseWide(1,2, e => e match {
    case Box(Assign(_,_))    => "[:=] assign" :: "[:=] assign update" :: Nil
    case _ => AxiomIndex.axiomsFor(e)
  })

  /** Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
    * Follows canonical axioms toward all their recursors while there is a unique canonical simplifier axiom.
    * @see [[HilbertCalculus.derive]]
    * @todo also implement a backwards chase in tableaux/sequent style
    */
  def chaseWide(breadth: Int, giveUp: Int, keys: Expression=>List[String] = AxiomIndex.axiomsFor): PositionTactic = new PositionTactic("chase") {
    require(breadth<=giveUp)
    import AxiomIndex.axiomIndex
    import FormulaConverter._
    import TermConverter._
    import SequentConverter._
    import Tactic.DEBUG

    override def applies(s: Sequent, p: Position): Boolean = keys(s.at(p).getOrElse(True)).size==1

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        Some(useDirectAt(chaseProof(node.sequent.at(p).get), PosInExpr(0::Nil))(p))

      /** Construct a proof proving the answer of the chose of e */
      private def chaseProof(e: Expression): Provable = {
        val initial: Provable = e match {
          case t: Term =>
            DerivedAxioms.equalReflex.fact(
              Sequent(Nil, IndexedSeq(), IndexedSeq(Equal(t,t))),
              UniformSubstitutionRule(USubst(SubstitutionPair(FuncOf(Function("s",None,Unit,Real),Nothing), t)::Nil),
                DerivedAxioms.equalReflex.fact.conclusion))
          case f: Formula =>
            DerivedAxioms.equivReflexiveAxiom.fact(
              Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(f,f))),
              UniformSubstitutionRule(USubst(SubstitutionPair(PredOf(Function("p",None,Unit,Bool),Nothing), f)::Nil),
                DerivedAxioms.equivReflexiveAxiom.fact.conclusion))
        }
        assert(initial.isProved, "Proved reflexive start " + initial + " for " + e)
        if (DEBUG) println("chase starts at " + initial)
        val r = chase(initial, PosInExpr(1::Nil))
        if (DEBUG) println("chase(" + e.prettyString + ") = ~~> " + r + " done")
        r
      } ensuring(r => r.isProved, "chase remains proved: " + " final chase(" + e + ")")

      private def chase(de: Provable, pos: PosInExpr): Provable = {
        if (DEBUG) println("chase(" + de.conclusion.succ.head.subAt(pos).prettyString + ")")
        // generic recursor
        keys(de.conclusion.succ.head.subAt(pos)) match {
          case Nil => println("no chase(" + de.conclusion.succ.head.subAt(pos).prettyString + ")"); de
          /*throw new IllegalArgumentException("No axiomFor for: " + expr)*/
          case List(ax) =>
            val (key, recursor) = axiomIndex(ax)
            val axUse = debugPF(ax)(useFor(ax, key))(SuccPosition(0, pos))(de)
            recursor.foldLeft(axUse)(
              (pf, cursor) => chase(pf, pos.append(cursor))
            )
          // take the first axiom among breadth that works for one useFor step
          case l: List[String] if l.size<=giveUp =>
            def firstAxUse(l: List[String]): Option[(Provable,List[PosInExpr])] = {
              for (ax <- l) try {
                val (key, recursor) = axiomIndex(ax)
                return Some((debugPF(ax)(useFor(ax, key))(SuccPosition(0, pos))(de), recursor))
              } catch {case _: ProverException => /* ignore and try next */}
              None
            }
            firstAxUse(l.take(Math.min(breadth, l.length))) match {
              case None => println("no chase(" + de.conclusion.succ.head.subAt(pos).prettyString + ")"); de
              case Some((axUse, recursor)) =>
                recursor.foldLeft(axUse)(
                  (pf, cursor) => chase(pf, pos.append(cursor))
                )
            }
          case l: List[String] if l.size>giveUp => println("stop chase(" + de.conclusion.succ.head.subAt(pos).prettyString + ")"); de
        }
      } ensuring(r => r.isProved, "chase remains proved: " + "chase(" + de.conclusion.succ.head(pos).prettyString + ")")
    }
  }

  def debugF(s: => Any): (Provable=>Provable)=>(Provable=>Provable) = tac => proof => {val pr = tac(proof); if (DEBUG) println("=== " + s + " === " + pr); pr}
  def debugPF(s: => Any): (Position=>Provable=>Provable)=>(Position=>Provable=>Provable) = tac => pos => proof => {val pr = tac(pos)(proof); if (DEBUG) println("=== " + s + " === " + pr); pr}

}
