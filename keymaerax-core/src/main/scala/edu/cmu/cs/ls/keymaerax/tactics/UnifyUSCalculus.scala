/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{ByProvable, ConstructionTactic, PositionTactic, Tactic}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
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
      if (!sub.isDefined) {println("ill-positioned " + p + " in " + s + "\nin " + "useAt(" + fact + ")(" + p + ")\n(" + s + ")"); return false}
      UnificationMatch(keyPart,sub.get)
      true
    } catch {case e: ProverException => println(e.inContext("useAt(" + fact + ")(" + p + ")\n(" + s + ")" + "\nat " + s.sub(p))); false}

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
              if (other.kind==FormulaKind) AxiomaticRuleTactics.equivalenceCongruenceT(p.inExpr)
              else if (other.kind==TermKind) AxiomaticRuleTactics.equationCongruenceT(p.inExpr)
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
            //@todo only prove remainder absolutely by proving prereq if that proof works out. Otherwise preserve context to prove prereq by master.
            //@todo check positioning etc.
            useAt(subst, new Context(remainder), k, p, C, c, cutR(subst(prereq))(SuccPos(0)) & onBranch(
              //@note the roles of cutUseLbl and cutShowLbl are really swapped here, since the implication on cutShowLbl will be handled by factTactic
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

  /** CE(equiv) uses the equivalence left<->right or equality left=right fact equiv for congruence reasoning
    * at the indicated position to replace left by right (literally, no substitution)
    * Efficient unification-free version of [[useAt()]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    */
  def CE(equiv: Provable): PositionTactic = new PositionTactic("CE(Provable)") {
    import Augmentors._
    require(equiv.conclusion.ante.length==0 && equiv.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + equiv)
    private val equi = equiv.conclusion.succ.head
    val (key,other) = equi match {
      case Equal(l,r) => (l,r)
      case Equiv(l,r) => (l,r)
      case _ => throw new IllegalArgumentException("expected equivalence or equality fact " + equiv)
    }
    override def applies(s: Sequent, p: Position): Boolean = s.sub(p) == Some(key)
    override def apply(p: Position): Tactic = new ConstructionTactic(name) {
      override def applicable(node : ProofNode): Boolean = applies(node.sequent, p)

      def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        val (ctx,c) = node.sequent.at(p)
        val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(node.sequent.succ.length + 1)}
        Some(cutLR(ctx(other))(p.top) &
          onBranch(
            (BranchLabels.cutShowLbl, cohide(cutPos) & //assertT(0,1) &
              equivifyR(SuccPosition(0)) & PropositionalTacticsImpl.commuteEquivRightT(SuccPosition(0)) &
              (if (other.kind==FormulaKind) AxiomaticRuleTactics.equivalenceCongruenceT(p.inExpr)
              else if (other.kind==TermKind) AxiomaticRuleTactics.equationCongruenceT(p.inExpr)
              else throw new IllegalArgumentException("Don't know how to handle kind " + other.kind + " of " + other)) &
              by(equiv)
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
  def useFor(axiom: String): ForwardPositionTactic = useFor(axiom, PosInExpr(0::Nil))

  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr): ForwardPositionTactic =
    if (Axiom.axioms.contains(axiom)) useFor(Axiom.axiom(axiom), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(DerivedAxioms.derivedAxiom(axiom), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

  /** CE(C) will wrap any equivalence left<->right or equality left=right fact it gets within context C.
    * Uses CE or CQ as needed.
    * @see [[CE(Provable)]]
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

      def useFor[T <: Expression](subst: RenUSubst, K: Context[T], k: T, p: Position, C: Context[Formula], c: Expression): Provable =
      {
        require(subst(k) == c, "correctly matched input")
        require(C(c).at(p.inExpr) ==(C, c), "correctly split at position p")
        require(List((C, DotFormula), (C, DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

        /** Equivalence rewriting step to replace occurrence of instance of k by instance of o in context */
        def equivStep(o: Expression, factTactic: Tactic): Provable = {
          //@todo delete factTactic argument since unused or use factTactic turned argument into Provable=>Provable
          require(fact.isProved, "currently want proved facts as input only")
          require(proof.conclusion.updated(p.top, C(subst(k)))==proof.conclusion, "expected context split")
          // |- fact: k=o or k<->o, respectively
          val sideUS: Provable = subst.toForward(fact)
          // |- subst(fact): subst(k)=subst(o) or subst(k)<->subst(o) by US
          val sideCE: Provable = CE(C)(sideUS)
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

          case _ => throw new ProverException("Not implemented for other cases yet, see useAt")
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

  /** Chases the expression at the indicated position forward until it is chased away or can't be chased further without critical choices. */
  lazy val chase: PositionTactic = chase(3,3)

  /** Chase with bounded breadth and giveUp to stop.
    * @param breadth how many alternative axioms to pursue locally, using the first applicable one.
    *                Equivalent to pruning keys so that all lists longer than giveUp are replaced by Nil,
    *                and then all lists are truncated beyond breadth.
    * @param giveUp  how many alternatives are too much so that the chase stops without trying any for applicability.
    *                Equivalent to pruning keys so that all lists longer than giveUp are replaced by Nil.
    */
  def chase(breadth: Int, giveUp: Int): PositionTactic = chase(breadth, giveUp, AxiomIndex.axiomsFor)
  def chase(breadth: Int, giveUp: Int, keys: Expression=>List[String]): PositionTactic = chase(breadth, giveUp, keys, (ax,pos) => pr=>pr)
  def chase(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic): PositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chase(e => keys(e) match {
      case l:List[String] if l.size > giveUp => Nil
      case l:List[String] => l.take(breadth)
    }, modifier)
  }
  def chaseFor(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic): ForwardPositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chaseFor(e => keys(e) match {
      case l:List[String] if l.size > giveUp => Nil
      case l:List[String] => l.take(breadth)
    }, modifier)
  }

  /** chase: Chases the expression at the indicated position forward until it is chased away or can't be chased further without critical choices.
    *
    * Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
    * Follows canonical axioms toward all their recursors while there is an applicable simplifier axiom according to `keys`.
    * @param keys maps expressions to a list of axiom names to be used for those expressions.
    *             First returned axioms will be favored (if applicable) over further axioms.
    * @param modifier will be notified after successful uses of axiom at a position with the result of the use.
    *                 The result of modifier(ax,pos)(step) will be used instead of step for each step of the chase.
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
            modifier: (String,Position)=>ForwardTactic = (ax,pos) => pr=>pr): PositionTactic = new PositionTactic("chase") {
    import Augmentors._

    //@note True has no applicable keys. This applicability is still an overapproximation since it does not check for clashes.
    override def applies(s: Sequent, p: Position): Boolean = {
      val sub = s.sub(p)
      if (!sub.isDefined) {println("ill-positioned " + p + " in " + s + "\nin " + "chase\n(" + s + ")"); return false}
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
        val r = chaseFor(keys, modifier) (SuccPosition(0, PosInExpr(1::Nil)))(initial)
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
    * @note Chase is search-free and, thus, quite efficient. It directly follows the
    *       [[AxiomIndex.axiomIndex() axiom index]] information to compute follow-up positions for the chase.
    * @example When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+(x'*y+x*y')>=0
    * @example When applied at Nil, turns [?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into ((x>0->x+1>=1) & (x=0->1>=1))
    * @example When applied at 1::Nil, turns [{x'=22}][?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into [{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))
    * @see [[chase()derive]]
    * @see [[HilbertCalculus.derive]]
    */
  def chaseFor(keys: Expression=>List[String],
                    modifier: (String,Position)=>ForwardTactic): ForwardPositionTactic = pos => de => {
    def doChase(de: Provable, pos: Position): Provable = {
      import AxiomIndex.axiomIndex
      import Augmentors._
      if (DEBUG) println("chase(" + de.conclusion.sub(pos).get.prettyString + ")")
      // generic recursor
      keys(de.conclusion.sub(pos).get) match {
        case Nil => println("no chase(" + de.conclusion.sub(pos).get.prettyString + ")"); de
        /*throw new IllegalArgumentException("No axiomFor for: " + expr)*/
        case List(ax) =>
          val (key, recursor) = axiomIndex(ax)
          try {
            val axUse = modifier(ax,pos) (useFor(ax, key)(pos)(de))
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
              return Some((modifier(ax,pos) (useFor(ax, key)(pos)(de)), recursor))
            } catch {case _: ProverException => /* ignore and try next */}
            None
          }
          firstAxUse match {
            case None => println("no chase(" + de.conclusion.sub(pos).get.prettyString + ")"); de
            case Some((axUse, recursor)) =>
              recursor.foldLeft(axUse)(
                (pf, cursor) => doChase(pf, pos.append(cursor))
              )
          }
      }
    }
    doChase(de,pos)
  }


  /** An update-based calculus for a position */
  def updateCalculus: PositionTactic = chase(3,3, e => e match {
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
