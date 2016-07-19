/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import SequentCalculus.{cohide2, cohideR, commuteEquivR, equivR, equivifyR, hideL, hideR, implyR}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.{closeTrue, cut, cutL, cutLR, cutR}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics._
import Augmentors._
import edu.cmu.cs.ls.keymaerax.tools.{CounterExampleTool, DiffSolutionTool}
import PosInExpr.HereP
import StaticSemanticsTools._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory

import scala.collection.immutable._
import scala.language.postfixOps

/**
  * Automatic unification-based Uniform Substitution Calculus with indexing.
  * Provides a tactic framework for automatically applying axioms and axiomatic rules by matching inputs against them by unification
  * according to their [[AxiomIndex]].
  *
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.bellerophon.UnificationMatch]]
  * @see [[AxiomIndex]]
  * @see Andre Platzer. [[http://arxiv.org/pdf/1601.06183.pdf A complete uniform substitution calculus for differential dynamic logic]]. arXiv 1601.06183, 2016.
  * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
  * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
  */
trait UnifyUSCalculus {
  import BelleExpr.DEBUG

  /** Liberal context via replaceAt instead of Context substitutions (true) */
  private val LIBERAL = Context.GUARDED

  /** @note must be initialized from outside; is var so that unit tests can setup/tear down.
    * @see [[DerivedAxioms]] */
  implicit var qeTool: QETool = null
  implicit var odeTool: DiffSolutionTool = null
  implicit var cexTool: CounterExampleTool = null

  /**
    * Throw exception if there is more than one open subgoal on the provable.
    */
  private def requireOneSubgoal(provable: Provable) =
    if(provable.subgoals.length != 1) throw new BelleError("Expected exactly one sequent in Provable")

  type Subst = UnificationMatch.Subst

  /*******************************************************************
    * Stepping auto-tactic
    *******************************************************************/

  /**
    * Make the canonical simplifying proof step based at the indicated position
    * except when an unknown decision needs to be made (e.g. invariants for loops or for differential equations).
    * Using the provided [[AxiomIndex]].
    *
    * @author Andre Platzer
    * @note Efficient source-level indexing implementation.
    * @see [[AxiomIndex]]
    */
  def stepAt(axiomIndex: Expression => Option[String]): DependentPositionTactic = new DependentPositionTactic("stepAt") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic("stepAt") {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        val sub = sequent.sub(pos)
        if (sub.isEmpty) throw new BelleUserGeneratedError("ill-positioned " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")")
        axiomIndex(sub.get) match {
          case Some(axiom) =>
            DerivationInfo(axiom).belleExpr match {
              case ap:AtPosition[_] => ap(pos)
              case expr:BelleExpr => expr
              case expr => throw new BelleUserGeneratedError("No axioms or rules applicable for " + sub.get + " which is at position " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")" + "\ngot " + expr)
            }
          case None => throw new BelleUserGeneratedError("No axioms or rules applicable for " + sub.get + " which is at position " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")")
        }
      }
    }
  }

  /*******************************************************************
    * close or proceed in proof by providing a Provable fact
    *******************************************************************/

  /** by(provable) uses the given Provable literally to continue or close the proof (if it fits to what has been proved) */
  //@todo auto-weaken as needed (maybe even exchangeleft)
  def by(fact: Provable)  : BuiltInTactic = new BuiltInTactic("by") {
    override def result(provable: Provable): Provable = {
      require(provable.subgoals.size == 1 && provable.subgoals.head == fact.conclusion, "Conclusion of fact\n" + fact + "\nmust match sole open goal in\n" + provable)
      if (provable.subgoals.size == 1 && provable.subgoals.head == fact.conclusion) provable.apply(fact, 0)
      else throw new BelleError("Conclusion of fact " + fact + " does not match sole open goal of " + provable)
    }
  }
  /** by(lemma) uses the given Lemma literally to continue or close the proof (if it fits to what has been proved) */
  def by(lemma: Lemma)        : BelleExpr = by(lemma.fact)
  /**
    * by(name,subst) uses the given axiom or axiomatic rule under the given substitution to prove the sequent.
    * {{{
    *    s(a) |- s(b)      a |- b
    *   ------------- rule(---------) if s(g)=G and s(d)=D
    *      G  |-  D        g |- d
    * }}}
    *
    * @author Andre Platzer
    * @param name the name of the fact to use to prove the sequent
    * @param subst what substitution `s` to use for instantiating the fact called `name`.
    * @see [[byUS()]]
    */
  def by(name: String, subst: USubst): BelleExpr = new NamedTactic(ProvableInfo(name).codeName, {
    by(subst(ProvableInfo(name).provable))
  })
  /** by(name,subst) uses the given axiom or axiomatic rule under the given substitution to prove the sequent. */
  def by(name: String, subst: Subst): BelleExpr = new NamedTactic(ProvableInfo(name).codeName, {
    by(subst.toForward(ProvableInfo(name).provable))
  })

  /** byUS(provable) proves by a uniform substitution instance of provable, obtained by unification with the current goal.
    *
    * @see [[UnifyUSCalculus.US()]] */
  def byUS(provable: Provable): BelleExpr = US(provable) //US(provable.conclusion) & by(provable)
  /** byUS(lemma) proves by a uniform substitution instance of lemma. */
  def byUS(lemma: Lemma)      : BelleExpr = byUS(lemma.fact)
  /** byUS(axiom) proves by a uniform substitution instance of a (derived) axiom or (derived) axiomatic rule.
    *
    * @see [[UnifyUSCalculus.byUS()]]
    */
  def byUS(name: String)     : BelleExpr = new NamedTactic(ProvableInfo(name).codeName, byUS(ProvableInfo(name).provable))

  /**
    * rule(name,inst) uses the given axiomatic rule to prove the sequent.
    * Unifies the fact's conclusion with the current sequent and proceed to the instantiated premise of `fact`.
    * {{{
    *    s(a) |- s(b)      a |- b
    *   ------------- rule(---------) if s(g)=G and s(d)=D
    *      G  |-  D        g |- d
    * }}}
    *
    * The behavior of rule(Provable) is essentially the same as that of by(Provable) except that
    * the former prefetches the uniform substitution instance during tactics applicability checking.
    *
    * @author Andre Platzer
    * @param name the name of the fact to use to prove the sequent
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur in the conclusion.
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @see [[byUS()]]
    * @see [[by()]]
    */
  def byUS(name: String, inst: Subst=>Subst = us=>us): BelleExpr = new NamedTactic(ProvableInfo(name).codeName, {
    val fact = Provable.rules.getOrElse(name, ProvableInfo(name).provable)
    //@todo could optimize to skip s.getRenamingTactic if fact's conclusion has no explicit variables in symbols
    USubstPatternTactic(
      (SequentType(fact.conclusion),
        (us: Subst) => {
          val s = inst(us);
          //@todo why not use s.toForward(fact) as in byUS(fact) instead of renaming the goal itself.
          //@todo unsure about use of renaming
          s.getRenamingTactic & by(fact(s.substitution.usubst))
        }) :: Nil
    )
  })

  /*******************************************************************
    * unification and matching based auto-tactics (backward tableaux/sequent)
    *******************************************************************/

  import TacticFactory._

  /** useAt(fact, tactic)(pos) uses the given fact (that'll be proved by tactic after unification) at the given position in the sequent (by unifying and equivalence rewriting). */
  //def useAt(fact: Formula, key: PosInExpr, tactic: Tactic, inst: Subst=>Subst): PositionTactic = useAt(fact, key, tactic, inst)
  //def useAt(fact: Formula, key: PosInExpr, tactic: Tactic): PositionTactic = useAt(fact, key, tactic)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  //  def useAt(fact: Formula, key: PosInExpr, inst: Subst=>Subst): DependentPositionTactic = useAt(fact, key, nil, inst)
  //  def useAt(fact: Formula, key: PosInExpr): DependentPositionTactic = useAt(fact, key, nil)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  //  def useAt(fact: Provable, key: PosInExpr, inst: Subst=>Subst): DependentPositionTactic = {
  //    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
  //    useAt(fact, key, inst)
  //  }
  //  def useAt(fact: Provable, key: PosInExpr): DependentPositionTactic = {
  //    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
  //    require(fact.isProved, "(no strict requirement, but) the best usable facts are proved " + fact)
  //    useAt(fact, key, inst=>inst)
  //  }
  // like useAt(fact,key) yet literally without uniform substitution of fact
  //  private[tactics] def useDirectAt(fact: Provable, key: PosInExpr): PositionTactic = {
  //    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
  //    require(fact.isProved, "(no strict requirement, but) the best usable facts are proved " + fact)
  //    useAt(fact.conclusion.succ.head, key, by(fact))
  //  }
  /** useAt(lem)(pos) uses the given lemma at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(lem: Lemma, key:PosInExpr, inst: Subst=>Subst): DependentPositionTactic = useAt(lem.fact, key, inst)
  def useAt(lem: Lemma, key:PosInExpr): DependentPositionTactic = useAt(lem.fact, key)
  def useAt(lem: Lemma)               : DependentPositionTactic = useAt(lem.fact, PosInExpr(0::Nil))

  /** Lazy use at of lemma by name. For use with ProveAs. */
  def lazyUseAt(lemmaName: String) : DependentPositionTactic =
    "lazyUseAt" by ((pos: Position, s:Sequent) => useAt(LemmaDBFactory.lemmaDB.get(lemmaName).get, PosInExpr(Nil))(pos))
  def lazyUseAt(lemmaName: String, key:PosInExpr) : DependentPositionTactic =
    "lazyUseAt" by ((pos: Position, s:Sequent) => useAt(LemmaDBFactory.lemmaDB.get(lemmaName).get, key)(pos))
  /** useAt(axiom)(pos) uses the given axiom at the given position in the sequent (by unifying and equivalence rewriting). */

  def useAt(axiom: String, key: PosInExpr, inst: Subst=>Subst): DependentPositionTactic = useAt(AxiomInfo(axiom).provable, key, inst)
  def useAt(axiom: String, key: PosInExpr): DependentPositionTactic = useAt(AxiomInfo(axiom).provable, key)
  def useAt(axiom: String, inst: Subst=>Subst): DependentPositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1, inst)
  def useAt(axiom: String): DependentPositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1)
  /** useExpansionAt(axiom)(pos) uses the given axiom at the given position in the sequent (by unifying and equivalence rewriting) in the direction that expands as opposed to simplifies operators. */
  def useExpansionAt(axiom: String): DependentPositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1.sibling)
  def useExpansionAt(axiom: String, inst: Subst=>Subst): DependentPositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1.sibling, inst)

  /*******************************************************************
    * unification and matching based auto-tactics (backward tableaux/sequent)
    *******************************************************************/

  /** US(subst, fact) reduces the proof to a proof of `fact`, whose uniform substitution instance under `subst` the current goal is.
    *
    * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(USubst)]]
    */
  def US(subst: USubst, fact: Provable): BuiltInTactic = by(fact(subst))
  def US(subst: USubst, axiom: String): BuiltInTactic = US(subst, AxiomInfo(axiom).provable)
  def US(subst: USubst): BuiltInTactic = new BuiltInTactic("US") {
    override def result(provable : Provable): Provable = provable(subst)
  }

  /**
    * US(fact) uses a suitable uniform substitution to reduce the proof to the proof of `fact`.
    * Unifies the current sequent with `fact.conclusion`.
    * Use that unifier as a uniform substitution to instantiate `fact` with.
    * {{{
    *      fact:
    *     g |- d
    *   --------- US where G=s(g) and D=s(d) where s=unify(fact.conclusion, G|-D)
    *     G |- D
    * }}}
    *
    * @author Andre Platzer
    * @param fact the proof to reduce this proof to by a suitable Uniform Substitution.
    * @see [[byUS()]]
    */
  def US(fact: Provable): DependentTactic = new SingleGoalDependentTactic("US") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      if (DEBUG) println("  US(" + fact.conclusion.prettyString + ")\n  unify: " + sequent + " matches against\n  form:  " + fact.conclusion + " ... checking")
      val subst = UnificationMatch(fact.conclusion, sequent)
      if (DEBUG) println("  US(" + fact.conclusion.prettyString + ")\n  unify: " + sequent + " matches against\n  form:  " + fact.conclusion + " by " + subst)
      Predef.assert(sequent == subst(fact.conclusion), "unification should match:\n  unify: " + sequent + "\n  gives: " + subst(fact.conclusion) + " when matching against\n  form:  " + fact.conclusion + "\n  by:    " + subst)
      by(subst.toForward(fact))
    }
  }

//  /**
//    * US(form) uses a suitable uniform substitution to reduce the proof to instead proving `form`.
//    * Unifies the current sequent with `form` and uses that unifier as a uniform substitution.
//    * {{{
//    *      form:
//    *     g |- d
//    *   --------- US where G=s(g) and D=s(d) where s=unify(form, G|-D)
//    *     G |- D
//    * }}}
//    *
//    * @author Andre Platzer
//    * @param form the sequent to reduce this proof to by a Uniform Substitution
//    * @see [[byUS()]]
//    */
  //  @deprecated("use US(Provable) instead")
  //  def US(form: Sequent): DependentTactic = new SingleGoalDependentTactic("US") {
  //    override def computeExpr(sequent: Sequent): BelleExpr = {
  //      if (DEBUG) println("  US(" + form.prettyString + ")\n  unify: " + sequent + " matches against\n  form:  " + form + " ... checking")
  //      val subst = UnificationMatch(form, sequent)
  //      if (DEBUG) println("  US(" + form.prettyString + ")\n  unify: " + sequent + " matches against\n  form:  " + form + " by " + subst)
  //      Predef.assert(sequent == subst(form), "unification should match:\n  unify: " + sequent + "\n  gives: " + subst(form) + " when matching against\n  form:  " + form + "\n  by:    " + subst)
  //      subst.toTactic(form)
  //    }
  //  }

  /**
    * useAt(fact)(pos) uses the given fact at the given position in the sequent.
    * Unifies fact the left or right part of fact with what's found at sequent(pos) and use corresponding
    * instance to make progress by reducing to the other side.
    * {{{
    *     G |- C{s(r)}, D
    *   ------------------ useAt(__l__<->r) if s=unify(c,l)
    *     G |- C{c}, D
    * }}}
    * and accordingly for facts that are `__l__->r` facts or conditional `p->(__l__<->r)` or `p->(__l__->r)` facts and so on,
    * where `__l__` indicates the key part of the fact.
    * useAt automatically tries proving the required assumptions/conditions of the fact it is using.
    *
    * Backward Tableaux-style proof analogue of [[useFor()]].
    *
    * Tactic specification:
    * {{{
    * useAt(fact)(p)(F) = let (C,c)=F(p) in
    *   case c of {
    *     s=unify(fact.left,_) => CutRight(C(s(fact.right))(p) & <(
    *       "use cut": skip
    *       "show cut": EquivifyRight(p.top) & CoHide(p.top) & CE(C(_)) & factTactic
    *     )
    *     s=unify(fact.right,_) => accordingly with an extra commuteEquivRightT
    *   }
    * }}}
    *
    * @author Andre Platzer
    * @param fact the fact to use to simplify at the indicated position of the sequent
    * @param key the part of the Formula fact to unify the indicated position of the sequent with
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur in fact(key).
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @example useAt("[a;++b;]p(??)<->[a;]p(??)&[b;]p(??)", PosInExpr(0::Nil), byUS("[;] compose"))
    * applied to the indicated 1::1::Nil of
    * [x:=1;][{x'=22}] [x:=2*x;++x:=0;]x>=0
    * turns it into
    * [x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)
    * @see [[useFor()]]
    * @see [[edu.cmu.cs.ls.keymaerax.btactics]]
    * @todo could directly use prop rules instead of CE if key close to HereP if more efficient.
    */
  def useAt(fact: Provable, key: PosInExpr, inst: Subst=>Subst = us=>us): DependentPositionTactic = new DependentPositionTactic("useAt") {
    private val (keyCtx:Context[_],keyPart) = fact.conclusion.succ.head.at(key)

    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        val (ctx,expr) = sequent.at(pos)
        val subst = inst(UnificationMatch(keyPart, expr))
        if (DEBUG) println("useAt(" + fact.prettyString + ")\n  unify:   " + expr + "\n  against: " + keyPart + "\n  by:      " + subst)
        Predef.assert(!RECHECK || expr == subst(keyPart), "unification matched left successfully\n  unify:   " + expr + "\n  against: " + keyPart + "\n  by:      " + subst + "\n  gave:    " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)
        //val keyCtxMatched = Context(subst(keyCtx.ctx))
        useAt(subst, keyCtx, keyPart, pos, ctx, expr, sequent)
      }
    }
    private[this] val RECHECK = true

    /**
      * useAt(K{k})(C{c}) uses, already under the given substitution subst, the key k from context K{k}
      * in place of c at position p in context C{_}.
      *
      * @param subst the substitution subst=unify(k,c)
      * @param K the context of fact in which key k occurs
      * @param k the key from context K{_} to use in place of c
      * @param p the position in the sequent at which this useAt is applied to
      * @param C the context C{_} around the position p at which K{k} will be used
      * @param c the formula c at position p in context C{_} to be replaced by subst(k)
      * @param sequent the sequent in which this useAt happens.
      * @tparam T
      * @return
      * @author Andre Platzer
      * @note The implementation could be generalized because it sometimes fires irrelevant substitution clashes coming merely from the context embedding contracts.
      */
    private def useAt[T <: Expression](subst: Subst, K: Context[T], k: T, p: Position, C:Context[Formula], c:Expression, sequent: Sequent): BelleExpr = {
      require(!RECHECK || subst(k) == c, "correctly matched input")
      //@note might cause some irrelevant clashes
      require(C(c).at(p.inExpr) == (C,c), "correctly split at position " + p.inExpr + "\ngiving context " + C + "\nsubexpression " + c + "\nreassembling to the same " + C(c))
      require(List((C,DotFormula),(C,DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

      /** Equivalence rewriting step */
      def equivStep(other: Expression, fact: Provable): BelleExpr = {
        val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length)}
        lazy val expect = if (p.isSucc) Imply(C(subst(other)), C(subst(keyPart))) else Imply(C(subst(keyPart)), C(subst(other)))
        lazy val expectEquiv = if (p.isSucc) Equiv(C(subst(other)), C(subst(keyPart))) else Equiv(C(subst(keyPart)), C(subst(other)))
        //@note ctx(fml) is meant to put fml in for DotTerm in ctx, i.e apply the corresponding USubst.
        //@todo simplify substantially if subst=id
        //@note cut instead of cutLR might be a quicker proof to avoid the equivify but changes positions which would be unfortunate.
        debug("start useAt " + p) & cutLR(C(subst(other)))(p.top) <(
          //@todo would already know that ctx is the right context to use and subst(left)<->subst(right) is what we need to prove next, which results by US from left<->right
          //@todo could optimize equivalenceCongruenceT by a direct CE call using context ctx
          /* use cut */ debug("    use cut") partial
          ,
          /* show cut */
          debug("    show cut") &
            cohideR/*(expect)*/(cutPos) & assert(0, 1) & debug("    cohidden") &
            //@todo SuccPosition(0) should be SuccPosition(previous length) if cutting left?
            assert(expect, "useAt show implication")(SuccPos(0)) &
            equivifyR(SuccPos(0)) & debug("    equivified") &
            assert(expectEquiv, "useAt show equivalence")(SuccPos(0)) &
            debug("    CE/CQ coming up") & (
            if (other.kind==FormulaKind) CE(p.inExpr) & debug("    ...CE done")
            else if (other.kind==TermKind) CQ(p.inExpr) & debug("     ...CQ done")
            else throw new IllegalArgumentException("Don't know how to handle kind " + other.kind + " of " + other)) &
            by(subst.toForward(fact))
          ) & debug("end   useAt " + p) partial
      }

      def implyStep(other: Expression): BelleExpr = {
        val cohide = p match {case p: SuccPosition => cohideR(p.top) case p: AntePosition => cohideR('Rlast)}
        cutLR(C(subst(other)))(p.topLevel) <(
          /* use */ ident partial,
          /* show */ cohide & CMon(p.inExpr) & by(subst.toForward(fact))
          )
      }

      /** Commute the fact l<->r or l=r */
      def commuteFact(fact: Provable): Provable = fact.conclusion match {
        case Sequent(IndexedSeq(), IndexedSeq(Equiv(l, r))) =>
          Provable.startProof(Equiv(r, l))(CommuteEquivRight(SuccPos(0)), 0)(fact, 0)
        case Sequent(IndexedSeq(), IndexedSeq(Equal(l, r))) => useFor("= commute")(SuccPos(0))(fact)
      }

      K.ctx match {
        case DotFormula if p.isTopLevel => by(subst.toForward(fact))

        case DotFormula if !p.isTopLevel =>
          val provedFact = TactixLibrary.proveBy(Equiv(fact.conclusion.succ.head,True),
            equivR(1) <(closeTrue(1) , cohideR(1) & by(fact)))
          equivStep(True, if (p.isSucc) commuteFact(provedFact) else provedFact)

        case Equiv(DotFormula, other) => equivStep(other, if (p.isSucc) commuteFact(fact) else fact)

        case Equiv(other, DotFormula) => equivStep(other, if (p.isAnte) commuteFact(fact) else fact)

        case Equal(DotTerm(_), other) =>
          equivStep(other, if (p.isSucc) commuteFact(fact) else fact)

        case Equal(other, DotTerm(_)) =>
          equivStep(other, if (p.isAnte) commuteFact(fact) else fact)

        case Imply(other, DotFormula) => implyStep(other)

        case Imply(DotFormula, other) => implyStep(other)

        //@note all DotTerms are equal
        case Imply(prereq, remainder) if StaticSemantics.signature(prereq).intersect(Set(DotFormula,DotTerm)).isEmpty =>
          // try to prove prereq globally
          /* {{{
           *                                         fact
           *                                   prereq -> remainder
           * ----------------master   ----------------------------- US
           * |- subst(prereq)         |- subst(prereq -> remainder)
           * ------------------------------------------------------ CutRight
           *         |- subst(remainder)
           * }}}
           * The resulting new fact subst(remainder) is then used via useFor
           */

          try {
            // |- subst(prereq)
            //@note don't call master to avoid infinite proof search for ODEs
            val prereqFact = TactixLibrary.proveBy(subst(prereq), TactixLibrary.QE)
            require(prereqFact.isProved, "only globally provable requirements currently supported. Ese useAt instead " + prereqFact)

            // |- subst(remainder{k})
            val remFact: Provable = (Provable.startProof(subst(Context(remainder)(k)))
              // |- subst(prereq)      |- subst(prereq -> remainder)
              (CutRight(subst(prereq), SuccPos(0)), 0)
              // prove right branch   |- subst(prereq -> remainder)
              // right branch  |- subst(prereq -> remainder)  byUS(fact)
              (subst.toForward(fact), 1)
              // left branch   |- subst(prereq)
              (prereqFact, 0)
              )
            remFact ensuring(r => r.subgoals == fact.subgoals, "Proved / no new subgoals expected " + remFact)

            val remKey: PosInExpr = key.child
            require(remFact.conclusion(SuccPos(0)).at(remKey)._2 == subst(keyPart), "position guess within fact are usually expected to succeed " + remKey + " in\n" + remFact + "\nis remaining from " + key + " in\n" + fact)
            UnifyUSCalculus.this.useAt(remFact, remKey, inst)(p)
          } catch {
            case err: Throwable =>
              // global proof of prereq unsuccessful, local proof needed
              /* {{{
               *                                                                                              fact
               *                                                                                        prereq -> remainder
               *                                                                            --------------------------------------------- CMon
               *                                               G |- C(subst(remL)),D          C(subst(prereq)) |- C(subst(remainder))
               *                              -------------------------------------- Hide   --------------------------------------------- ->2<->
               *                              G,C(subst(prereq)) |- C(subst(remL)),D        G,C(subst(prereq)) |- C(subst(remL->remR)),D
               *                              ------------------------------------------------------------------------------------------- CutRight
               * G |- C(subst(prereq)),D                              G,C(subst(prereq)) |- C(subst(remR)),D
               * ------------------------------------------------------------------------------------------------------------------------ Cut
               *                      G |- C(subst(remR)),D
               * }}}
               *
               */

              //@todo assumes no more context around remainder (no other examples so far)
              val (conclusion, commute) = remainder match {
                case Equiv(DotFormula, other) => (other, if (p.isSucc) commuteEquivR(1) else ident)
                case Equiv(other, DotFormula) => (other, if (p.isAnte) commuteEquivR(1) else ident)
                //              case Equal(DotTerm, other) => (other, if (p.isSucc) TactixLibrary.useAt("= commute")(1) else ident)
                //              case Equal(other, DotTerm) => (other, if (p.isAnte) TactixLibrary.useAt("= commute")(1) else ident)
              }

              cut(C(subst(prereq))) <(
                /* use: result remains open */ cutR(C(subst(conclusion)))(p.checkSucc.top) <(
                hideL('Llast) partial,
                cohide2(AntePos(sequent.ante.size), p.top) & equivifyR(1) & commute & implyRi & CMon(p.inExpr) &
                  by(Provable.startProof(Imply(subst(prereq), subst(Context(remainder)(k))))(subst.toForward(fact), 0))
                ) partial,
                /* show: prereq remains open */ hideR(p.top) partial
                )
          }
        case Forall(vars, remainder) if vars.length==1 => ???
        //useAt(subst, new Context(remainder), k, p, C, c, /*@todo instantiateQuanT(vars.head, subst(vars.head))(SuccPos(0))*/ ident, sequent)

        //@todo unfold box by step*
        case Box(a, remainder) => ???
      }
    }

  }



  // Let auto-tactics

  /** Let(abbr, value, inner) alias `let abbr=value in inner` abbreviates `value` by `abbr` in the
    * provable and proceeds with an internal proof by tactic `inner`, resuming to the outer proof by a
    * uniform substitution of `value` for `abbr` of the resulting provable.
    */
  def let(abbr: Expression, value: Expression, inner: BelleExpr): BelleExpr = Let(abbr, value, inner)


  //////////////
  // Congruence Reasoning

  /**
    * CQ(pos) at the indicated position within an equivalence reduces contextual equivalence `p(left)<->p(right)` to argument equality `left=right`.
    * This tactic will use [[CEat()]] under the hood as needed.
    * {{{
    *        f(x) = g(x)
    *   --------------------- CQ
    *    c(f(x)) <-> c(g(x))
    * }}}
    *
    * @param inEqPos the position *within* the two sides of the equivalence at which the context DotTerm happens.
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    */
  def CQ(inEqPos: PosInExpr): DependentTactic = new SingleGoalDependentTactic("CQ congruence") {
    private val f_ = FuncOf(Function("f_", None, Real, Real), Anything)
    private val g_ = FuncOf(Function("g_", None, Real, Real), Anything)
    private val c_ = PredOf(Function("ctx_", None, Real, Bool), DotTerm)

    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.isEmpty && sequent.succ.length == 1, "Expected empty antecedent and single succedent, but got " + sequent)
      sequent.succ.head match {
        case Equiv(p, q) =>
          val (ctxF, f) = p.at(inEqPos)
          val (ctxG, g) = q.at(inEqPos)
          require(ctxF == ctxG, "Same context expected, but got contexts " + ctxF + " and " + ctxG)
          require(ctxF.ctx == ctxG.ctx, "Same context formulas expected, but got " + ctxF.ctx + " and " + ctxG.ctx)
          require(ctxF.isTermContext, "Formula context expected for CQ")
          if (DEBUG) println("CQ: boundAt(" + ctxF.ctx + "," + inEqPos + ")=" + boundAt(ctxF.ctx, inEqPos) + " intersecting FV(" + f + ")=" + freeVars(f) + "\\/FV(" + g + ")=" + freeVars(g) + " i.e. " + (freeVars(f)++freeVars(g)) + "\nIntersect: " + boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f)++freeVars(g)))
          if (boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f)++freeVars(g)).isEmpty) {
            by("CQ equation congruence", USubst(SubstitutionPair(c_, ctxF.ctx) :: SubstitutionPair(f_, f) :: SubstitutionPair(g_, g) :: Nil))
          } else {
            if (DEBUG) println("CQ: Split " + p + " around " + inEqPos)
            val (fmlPos,termPos) : (PosInExpr,PosInExpr) = Context.splitPos(p, inEqPos)
            if (DEBUG) println("CQ: Split " + p + " around " + inEqPos + "\ninto " + fmlPos + " and " + termPos + "\n  as " + p.at(fmlPos)._1 + " and " + Context.at(p.at(fmlPos)._2,termPos)._1)
            if (p.at(fmlPos)._2.isInstanceOf[Modal]) println(">>CE TACTIC MAY PRODUCE INFINITE LOOP<<")
            if (fmlPos == HereP) throw new IllegalStateException("CQ split void, would cause infinite loop unless stopped")
            //@todo could optimize to build directly since ctx already known
            CE(fmlPos) & CQ(termPos)
          }
        case fml => throw new BelleError("Expected equivalence, but got " + fml)
      }
    }
  }

  /**
    * CE(pos) at the indicated position within an equivalence reduces contextual equivalence `C{left}<->C{right}`to argument equivalence `left<->right`.
    * {{{
    *       p(x) <-> q(x)
    *   --------------------- CE
    *    C{p(x)} <-> C{q(x)}
    * }}}
    * Part of the differential dynamic logic Hilbert calculus.
    *
    * @param inEqPos the position *within* the two sides of the equivalence at which the context DotFormula occurs.
    * @see [[UnifyUSCalculus.CE(Context)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @see [[UnifyUSCalculus.CEat(Provable)]]
    * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
    * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
    */
  def CE(inEqPos: PosInExpr): DependentTactic = new SingleGoalDependentTactic("CE congruence") {
    private val p_ = PredOf(Function("p_", None, Real, Bool), Anything)
    private val q_ = PredOf(Function("q_", None, Real, Bool), Anything)
    private val c_ = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)

    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.isEmpty && sequent.succ.length==1, "Expected empty antecedent and single succedent formula, but got " + sequent)
      sequent.succ.head match {
        case Equiv(l, r) =>
          if (inEqPos == HereP) ident
          else {
            val (ctxP, p) = l.at(inEqPos)
            val (ctxQ, q) = r.at(inEqPos)
            //@note Could skip the construction of ctxQ but it's part of the .at construction anyways.
            require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
            require(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
            require(ctxP.isFormulaContext, "Formula context expected for CE")
            by("CE congruence", USubst(SubstitutionPair(c_, ctxP.ctx) :: SubstitutionPair(p_, p) :: SubstitutionPair(q_, q) :: Nil))
          }
        case fml => throw new BelleError("Expected equivalence, but got " + fml)
      }
    }
  }

  /**
    * CMon(pos) at the indicated position within an implication reduces contextual implication `C{o}->C{k}` to argument implication `o->k` for positive C.
    * {{{
    *   |- o -> k
    *   ------------------------- for positive C{.}
    *   |- C{o} -> C{k}
    * }}}
    *
    * @param inEqPos the position *within* the two sides of the implication at which the context DotFormula happens.
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(Context)]]
    * @see [[UnifyUSCalculus.CEat())]]
    */
  def CMon(inEqPos: PosInExpr): DependentTactic = new SingleGoalDependentTactic("CMon congruence") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.isEmpty && sequent.succ.length==1, "Expected empty antecedent and single succedent formula, but got " + sequent)
      sequent.succ.head match {
        case Imply(l, r) =>
          val (ctxP, p: Formula) = l.at(inEqPos)
          val (ctxQ, q: Formula) = r.at(inEqPos)
          require(ctxP == ctxQ, "Contexts must be equal, but " + ctxP + " != " + ctxQ)
          if (FormulaTools.polarityAt(l, inEqPos) < 0) implyR(SuccPos(0)) &
            by(CMon(ctxP)(Provable.startProof(Sequent(IndexedSeq(q), IndexedSeq(p))))) &
            by(inverseImplyR(Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(Imply(q, p))))))
          else implyR(SuccPos(0)) &
            by(CMon(ctxP)(Provable.startProof(Sequent(IndexedSeq(p), IndexedSeq(q))))) &
            by(inverseImplyR(Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(Imply(p, q))))))
      }
    }
  }

  /** CEat(fact) uses the equivalence `left<->right` or equality `left=right` or implication `left->right` fact for congruence
    * reasoning at the indicated position to replace `right` by `left` at indicated position (literally, no substitution).
    * Efficient unification-free version of [[UnifyUSCalculus#useAt(Provable, PosInExpr):PositionTactic]]
    * {{{
    *                          fact
    *   G |- C{q(x)}, D    q(x) <-> p(x)
    *   -------------------------------- CER(fact)
    *   G |- C{p(x)}, D
    * }}}
    * Similarly for antecedents or equality facts or implication facts, e.g.:
    * {{{
    *                          fact
    *   C{q(x)}, G |- D    q(x) <-> p(x)
    *   -------------------------------- CEL(fact)
    *   C{p(x)}, G |- D
    * }}}
    *
    * @see [[UnifyUSCalculus.CEat(Provable,Context)]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @example `CEat(fact)` is equivalent to `CEat(fact, Context("⎵".asFormula))``
    * @todo Optimization: Would direct propositional rules make CEat faster at pos.isTopLevel?
    */
  def CEat(fact: Provable): DependentPositionTactic = new DependentPositionTactic("CE(Provable)") {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + fact)

    def splitFact: (Expression, Expression, BelleExpr, (PosInExpr=>BelleExpr)) = fact.conclusion.succ.head match {
      case Equal(l,r) => (l, r, equivifyR(SuccPos(0)), CQ)
      case Equiv(l,r) => (l, r, equivifyR(SuccPos(0)), CE)
      case Imply(l,r) => (l, r, ident, CMon)
      case _ => throw new IllegalArgumentException("CE expects equivalence or equality or implication fact " + fact)
    }
    val (other, key, equivify, tactic) = splitFact

    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(sequent.sub(pos).contains(key), "In-applicable CE(" + fact + ")\nat " + pos + " which is " + sequent.sub(pos).getOrElse("<ill-positioned>") + "\nat " + sequent)
        val (ctx, _) = sequent.at(pos)
        val (cutPos: SuccPos, commute: BelleExpr) = pos match {case p: SuccPosition => (p.top, ident) case p: AntePosition => (SuccPos(sequent.succ.length), commuteEquivR(1))}
        val ctxOther = if (!LIBERAL) ctx(other) else sequent.replaceAt(pos, other).asInstanceOf[Formula]
        cutLR(ctxOther)(pos.top) <(
          /* use */ ident,
          /* show */ cohideR(cutPos) & equivify & tactic(pos.inExpr) & commute &  by(fact)
          )
      }
    }
  }

  /** CEat(fact,C) uses the equivalence `left<->right` or equality `left=right` or implication `left->right` fact for congruence
    * reasoning in the given context C at the indicated position to replace `right` by `left` in that context (literally, no substitution).
    *
    * @see [[UnifyUSCalculus.CEat(Provable)]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @example `CE(fact, Context("⎵".asFormula))` is equivalent to `CE(fact)`.
    * @example `CE(fact, Context("x>0&⎵".asFormula))(p)` is equivalent to `CE(fact)(p+PosInExpr(1::Nil))`.
    *          Except that the former has the shape `x>0&⎵` for the context starting from position `p`.
    */
  def CEat(fact: Provable, C: Context[Formula]): DependentPositionTactic = new DependentPositionTactic("CE(Provable,Context)") {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + fact)

    def splitFact: (Expression, Expression, BelleExpr, (Context[Formula]=>ForwardTactic)) = fact.conclusion.succ.head match {
      case Equal(l,r) => (l, r, equivifyR(SuccPos(0)), CE) //@note this CE can also use CQ
      case Equiv(l,r) => (l, r, equivifyR(SuccPos(0)), CE)
      case Imply(l,r) => (l, r, ident, CMon)
      case _ => throw new IllegalArgumentException("CE expects equivalence or equality or implication fact " + fact)
    }
    val (other, key, equivify, tactic) = splitFact


    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(sequent.sub(pos).contains(C(key)), "In-applicable CE(" + fact + ",\n" + C + ")\nat " + pos + "\nwhich is " + sequent.sub(pos).getOrElse("none") + "\nat " + sequent)
        val (posctx,c) = sequent.at(pos)
        val ctx = posctx(C)
        val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
        cutLR(ctx(other))(pos.top) <(
          /* use */ ident partial,
          /* show */ cohideR(cutPos) & //assertT(0,1) &
          equivify & /*commuteEquivR(SuccPosition(0)) &*/
          by(tactic(C)(fact))
          )
      }
    }
  }


  /** cutAt(repl) cuts left/right to replace the expression at the indicated position in its context C{.} by `repl`.
    * {{{
    *   G |- C{repl}, D   G |- C{repl}->C{c}, D
    *   --------------------------------------- cutAt(repl)
    *   G |- C{c}, D
    * }}}
    * {{{
    *   C{repl}, G |- D   G |- D, C{c}->C{repl}
    *   --------------------------------------- cutAt(repl)
    *   C{c}, G |- D
    * }}}
    *
    * @see [[UnifyUSCalculus.CEat(Provable)]]
    */
  def cutAt(repl: Expression): DependentPositionTactic = new DependentPositionTactic("cutAt") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        require(sequent.sub(pos).isDefined, "Position " + pos + " not defined in sequent " + sequent)
        val (ctx, _) = sequent.at(pos)
        cutLR(ctx(repl))(pos.top)
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
  def iden: ForwardTactic = pr => pr
  def uniformRenameF(what: Variable, repl: Variable): ForwardTactic = pr => pr(
    UniformRenaming(what, repl)(pr.conclusion).head,
    UniformRenaming(what, repl)
  )
  def commuteEquivFR: ForwardPositionTactic = pos => pr => pr(
    CommuteEquivRight(pos.checkSucc.checkTop.asInstanceOf[SuccPos])(pr.conclusion).head,
    CommuteEquivRight(pos.checkSucc.checkTop.asInstanceOf[SuccPos])
  )


  /** useFor(axiom) use the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String): ForwardPositionTactic = useFor(axiom, AxiomIndex.axiomIndex(axiom)._1)

  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr): ForwardPositionTactic = useFor(AxiomInfo(axiom).provable, key)
  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr, inst: Subst=>Subst): ForwardPositionTactic = useFor(AxiomInfo(axiom).provable, key, inst)

  /** useExpansionFor(axiom) uses the given axiom forward for the given position in the sequent (by unifying and equivalence rewriting) in the direction that expands as opposed to simplifies operators. */
  def useExpansionFor(axiom: String): ForwardPositionTactic = useFor(axiom, AxiomIndex.axiomIndex(axiom)._1.sibling)

  /** CE(C) will wrap any equivalence `left<->right` or equality `left=right` fact it gets within context C.
    * Uses CE or CQ as needed.
    * {{{
    *       p(x) <-> q(x)
    *   --------------------- CE
    *    C{p(x)} <-> C{q(x)}
    * }}}
    * {{{
    *       f(x) = g(x)
    *   --------------------- CQ+CE
    *    c(f(x)) <-> c(g(x))
    * }}}
    *
    * @see [[CE(PosInExpr]]
    * @see [[CEat(Provable)]]
    * @see [[CMon(Context)]]
    * @todo likewise for Context[Term] using CT instead.
    */
  def CE(C: Context[Formula]): ForwardTactic = equiv => {
    require(equiv.conclusion.ante.isEmpty && equiv.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + equiv)
    equiv.conclusion.succ.head match {
      case Equiv(left,right) =>
        require(C.isFormulaContext, "Formula context expected to make use of equivalences with CE " + C)
        equiv(
          Provable.rules("CE congruence")(
            USubst(SubstitutionPair(PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula), C.ctx) ::
              SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), left) ::
              SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), right) ::
              Nil))
        )
      case Equal(left,right) =>
        require(C.isTermContext, "Term context expected to make use of equalities with CE " + C)
        equiv(
          Provable.rules("CQ equation congruence")(
            USubst(SubstitutionPair(PredOf(Function("ctx_", None, Real, Bool), DotTerm), C.ctx) ::
              SubstitutionPair(FuncOf(Function("f_", None, Real, Real), Anything), left) ::
              SubstitutionPair(FuncOf(Function("g_", None, Real, Real), Anything), right) ::
              Nil))
        )
      case _ => throw new IllegalArgumentException("expected equivalence or equality fact " + equiv.conclusion)
    }
  }

  /** CMon(C) will wrap any implication `left->right` fact it gets within a (positive or negative) context C by monotonicity.
    * {{{
    *      k |- o
    *   ------------ CMon if C{⎵} of positive polarity
    *   C{k} |- C{o}
    * }}}
    *
    * @note The direction in the conclusion switches for negative polarity C{⎵}
    * @author Andre Platzer
    * @author Stefan Mitsch
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @see [[CE(Context)]]
    */
  def CMon(C: Context[Formula]): ForwardTactic = impl => {
    import StaticSemantics.symbols
    require(impl.conclusion.ante.length == 1 && impl.conclusion.succ.length == 1, "expected equivalence shape without antecedent and exactly one succedent " + impl)

    // global polarity switch for all cases, except Modal and Equiv, which modify this switch if necessary
    val polarity = FormulaTools.polarityAt(C.ctx, FormulaTools.posOf(C.ctx, DotFormula).getOrElse(
      throw new IllegalArgumentException(s"Context should contain DotFormula, but is ${C.ctx}")))
    val (left, right) =
      if (polarity < 0) (impl.conclusion.succ.head, impl.conclusion.ante.head)
      else (impl.conclusion.ante.head, impl.conclusion.succ.head)

    require(C.isFormulaContext, "Formula context expected to make use of equivalences with CE " + C)
    if (DEBUG) println("CMon(" + C + ")" + "(" + impl + ")")
    /** Monotonicity rewriting step to replace occurrence of instance of k by instance of o in context */
    def monStep(C: Context[Formula], mon: Provable): Provable = {
      //@todo assert(mon.ante.head == C{left or right} && mon.succ.head == C{right or left})
      if (DEBUG) println("in monStep(" + C + ", " + mon + ")") //\nin CMon(" + C + ")" + "(" + impl + ")")

      val localPolarity = FormulaTools.polarityAt(C.ctx, FormulaTools.posOf(C.ctx, DotFormula).getOrElse(
        throw new IllegalArgumentException("Context should contain DotFormula")))
      val (ante, succ) =
        if (polarity*localPolarity < 0 || (polarity == 0 && localPolarity < 0)) (IndexedSeq(C(right)), IndexedSeq(C(left)))
        else (IndexedSeq(C(left)), IndexedSeq(C(right)))

      (
        // which context to use it in
        C.ctx match {
          case DotFormula => mon

          case And(e, c) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(ante, succ))
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(0), SuccPos(0)), 0)
              // right branch
              (CoHide2(AntePos(1), SuccPos(0)), 0)
              ) (monStep(Context(c), mon), 0)

          case And(c, e) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(ante, succ))
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(1), SuccPos(0)), 1)
              // left branch
              (CoHide2(AntePos(0), SuccPos(0)), 0)
              ) (monStep(Context(c), mon), 0)

          case Or(e, c) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(ante, succ))
            (OrRight(SuccPos(0)), 0)
            (OrLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(0)), 0)
              // right branch
              (CoHide2(AntePos(0), SuccPos(1)), 0)
              ) (monStep(Context(c), mon), 0)

          case Or(c, e) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(ante, succ))
            (OrRight(SuccPos(0)), 0)
            (OrLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(1)), 1)
              // right branch
              (CoHide2(AntePos(0), SuccPos(0)), 0)
              ) (monStep(Context(c), mon), 0)

          case Imply(e, c) if !symbols(e).contains(DotFormula) =>
            if (DEBUG) println("CMon check case: " + C + " to prove " + Sequent(ante, succ) + "\nfrom " + mon +
              "\nnext step in context " + Context(c) + "\n having current polarity " + polarity + " and new polarity " + localPolarity)
            (Provable.startProof(Sequent(ante, succ))
              // e->c{a} |- e->c{s}
              (ImplyRight(SuccPos(0)), 0)
              // e->c{a}, e |- c{s}
              (ImplyLeft(AntePos(0)), 0)
              // e |- c{s}, e    c{a}, e |- c{s}
              // left branch     e |- c{s}, e closes
              (Close(AntePos(0), SuccPos(1)), 0)
              // right branch    c{a}, e |- c{s}
              (HideLeft(AntePos(1)),0 )    //@note was: (CoHide2(AntePos(1), SuccPos(0)), 0)
              // right branch  c{a} |- c{s}
              ) (monStep(Context(c), mon), 0)

          case Imply(c, e) if !symbols(e).contains(DotFormula) =>
            if (DEBUG) println("CMon check case: " + C + " to prove " + Sequent(ante, succ) + "\nfrom " + mon +
              "\nnext step in context " + Context(c) + "\n having current polarity " + polarity + " and new polarity " + localPolarity)
            (Provable.startProof(Sequent(ante, succ))
              // c{a}->e |- c{s}->e
              (ImplyRight(SuccPos(0)), 0)
              // c{a}->e, c{s} |- e
              (ImplyLeft(AntePos(0)), 0)
              // c{s} |- e, c{a}    e, c{s} |- e
              // right branch       e, c{s} |- e
              (Close(AntePos(0), SuccPos(0)), 1)   //@note was: AntePos(1) for ImplyLeftOld for some reason
              // left branch        c{s} |- e, c{a}
              (HideRight(SuccPos(0)), 0)   //@note was: (CoHide2(AntePos(0), SuccPos(1)), 0)
              ) (monStep(Context(c), mon), 0)

          case Equiv(e, c) if !symbols(e).contains(DotFormula) =>
            //@note fallback to implication
            // polarity(k)=-1, polarity(o)=+1
            // orient equivalence Equiv(c,e) such that polarity of k in that will be +1
            // and polarity of o in that will be -1
            val newPol = FormulaTools.polarityAt(Imply(c,e), FormulaTools.posOf(Imply(c,e), DotFormula).getOrElse(
              throw new IllegalArgumentException("Context should contain DotFormula")))
            if (newPol<0) {
              // polarity of k in (Context(Imply(c,e))(k) will be +1
              // polarity of o in (Context(Imply(c,e))(o) will be -1
              monStep(Context(Imply(c, e)), mon)
            } else if (newPol>0) {
              Predef.assert(FormulaTools.polarityAt(Imply(e,c), FormulaTools.posOf(Imply(e,c), DotFormula).getOrElse(
                throw new IllegalArgumentException("Context should contain DotFormula")))<0)
              // polarity of k in (Context(Imply(e,c))(k) will be +1
              // polarity of o in (Context(Imply(e,c))(o) will be -1
              monStep(Context(Imply(e, c)), mon)
            } else {
              Predef.assert(false, "polarity rotations should ultimately be nonzero except with too many nested equivalences " + C); ???
            }

          case Equiv(c, e) if !symbols(e).contains(DotFormula) =>
            //@note fallback to implication
            // polarity(k)=-1, polarity(o)=+1
            // orient equivalence Equiv(c,e) such that polarity of k in that will be +1
            // and polarity of o in that will be -1
            val newPol = FormulaTools.polarityAt(Imply(c,e), FormulaTools.posOf(Imply(c,e), DotFormula).getOrElse(
              throw new IllegalArgumentException("Context should contain DotFormula")))
            if (newPol>0) {
              // polarity of k in (Context(Imply(c,e))(k) will be +1
              // polarity of o in (Context(Imply(c,e))(o) will be -1
              monStep(Context(Imply(c, e)), mon)
            } else if (newPol<0) {
              Predef.assert(FormulaTools.polarityAt(Imply(e,c), FormulaTools.posOf(Imply(e,c), DotFormula).getOrElse(
                throw new IllegalArgumentException("Context should contain DotFormula")))>0)
              // polarity of k in (Context(Imply(e,c))(k) will be +1
              // polarity of o in (Context(Imply(e,c))(o) will be -1
              monStep(Context(Imply(e, c)), mon)
            } else {
              Predef.assert(false, "polarity rotations should ultimately be nonzero except with too many nested equivalences " + C); ???
            }

          case Equiv(e, c) => Predef.assert(symbols(e).contains(DotFormula) || symbols(c).contains(DotFormula), "proper contexts have dots somewhere " + C)
            throw new ProverException("No monotone context for equivalences " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")

          case Box(a, c) if !symbols(a).contains(DotFormula) =>
            //@note rotate substitution into same order as current ante/succ
            val (bleft, bright) =
              if (polarity*localPolarity < 0 || (polarity == 0 && localPolarity < 0)) (right, left)
              else (left, right)
            (Provable.startProof(Sequent(ante, succ))
            (DerivedRuleInfo("[] monotone").provable(USubst(
              SubstitutionPair(ProgramConst("a_"), a)
                :: SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Context(c)(bleft))
                :: SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Context(c)(bright))
                :: Nil
            )
            ), 0)
              ) (monStep(Context(c), mon), 0)

          case Diamond(a, c) if !symbols(a).contains(DotFormula) =>
            //@note rotate substitution into same order as current ante/succ
            val (dleft, dright) =
              if (polarity*localPolarity < 0 || (polarity == 0 && localPolarity < 0)) (right, left)
              else (left, right)
            (Provable.startProof(Sequent(ante, succ))
            (Provable.rules("<> monotone")(USubst(
              SubstitutionPair(ProgramConst("a_"), a)
                :: SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Context(c)(dleft))
                :: SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Context(c)(dright))
                :: Nil
            )
            ), 0)
              ) (monStep(Context(c), mon), 0)

          case m:Modal if symbols(m.program).contains(DotFormula) =>
            //@todo implement good cases. For example nibble of assign on both sides. Or random. Or ....
            throw new ProverException("No monotone context within programs " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")

          case Forall(vars, c) => //if !StaticSemantics.freeVars(subst(c)).symbols.intersect(vars.toSet).isEmpty =>
            require(vars.size == 1, "Universal quantifier must not be block quantifier")
            //@note would also work with all distribute and all generalization instead
            //@note would also work with Skolemize and all instantiate but disjointness is more painful
            val rename = (us: RenUSubst) => us ++ RenUSubst(Seq((Variable("x_"), vars.head)))
            useFor("all eliminate", PosInExpr(1::Nil), rename)(AntePosition.base0(1-1))(monStep(Context(c), mon)) (
              Sequent(ante, succ),
              Skolemize(SuccPos(0))
            )

          /*case Forall(vars, c) if StaticSemantics.freeVars(subst(c)).symbols.intersect(vars.toSet).isEmpty =>
            useFor("vacuous all quantifier")(SuccPosition(0))(
              useFor("vacuous all quantifier")(AntePosition(0))(monStep(Context(c), mon))
            )*/

          case Exists(vars, c) =>
            require(vars.size == 1, "Existential quantifier must not be block quantifier")
            //@note would also work with exists distribute and exists generalization instead
            //@note would also work with Skolemize and all instantiate but disjointness is more painful
            val rename = (us: RenUSubst) => us ++ RenUSubst(Seq((Variable("x_"), vars.head)))
            useFor("exists eliminate", PosInExpr(0::Nil), rename)(SuccPosition(1))(monStep(Context(c), mon)) (
              Sequent(ante, succ),
              Skolemize(AntePos(0))
            )

          case Not(c) =>
            //@note no polarity switch necessary here, since global polarity switch at beginning of CMon
            (Provable.startProof(Sequent(ante, succ))
            (NotLeft(AntePos(0)), 0)
            (NotRight(SuccPos(0)), 0)
              ) (monStep(Context(c), mon), 0)

          case _ => throw new ProverException("Not implemented for other cases yet " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")
        }
        ) ensuring(r => {true || r.conclusion ==
        //@todo ensuring is not correct yet (needs to keep track of when to switch polarity)
        (if (C.ctx == DotFormula && polarity < 0) Sequent(IndexedSeq(right), IndexedSeq(left))
        else if (C.ctx == DotFormula && polarity >= 0) Sequent(IndexedSeq(left), IndexedSeq(right))
        else if (polarity >= 0) Sequent(IndexedSeq(C(right)), IndexedSeq(C(left)))
        else Sequent(IndexedSeq(C(left)), IndexedSeq(C(right))))}, "Expected conclusion " + "\nin CMon.monStep(" + C + ",\nwhich is " + (if (polarity < 0) C(right) + "/" + C(left) else C(left) + "/" + C(right)) + ",\non " + mon + ")"
        ) ensuring(r => !impl.isProved || r.isProved, "Proved if input fact proved" + "\nin CMon.monStep(" + C + ",\non " + mon + ")")
    }
    monStep(C, impl)
  }

  /** useFor(fact,key,inst) use the key part of the given fact forward for the selected position in the given Provable to conclude a new Provable
    * Forward Hilbert-style proof analogue of [[useAt()]].
    * {{{
    *     G |- C{c}, D
    *   ------------------ useFor(__l__<->r) if s=unify(c,l)
    *     G |- C{s(r)}, D
    * }}}
    * and accordingly for facts that are `__l__->r` facts or conditional `p->(__l__<->r)` or `p->(__l__->r)` facts and so on,
    * where `__l__` indicates the key part of the fact.
    * useAt automatically tries proving the required assumptions/conditions of the fact it is using.
    *
    * @author Andre Platzer
    * @param fact the Provable fact whose conclusion to use to simplify at the indicated position of the sequent
    * @param key the part of the fact's conclusion to unify the indicated position of the sequent with
    * @param inst Transformation for instantiating additional unmatched symbols that do not occur in `fact.conclusion(key)`.
    *   Defaults to identity transformation, i.e., no change in substitution found by unification.
    *   This transformation could also change the substitution if other cases than the most-general unifier are preferred.
    * @example useFor(Axiom.axiom("[;] compose"), PosInExpr(0::Nil))
    * applied to the indicated 1::1::Nil of
    * ``[x:=1;][{x'=22}]__[x:=2*x;++x:=0;]x>=0__``
    * turns it into
    * ``[x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)``
    * @see [[useAt()]]
    * @see [[edu.cmu.cs.ls.keymaerax.btactics]]
    */
  def useFor(fact: Provable, key: PosInExpr, inst: Subst=>Subst = (us => us)): ForwardPositionTactic = {
    // split key into keyCtx{keyPart} = fact
    val (keyCtx: Context[_], keyPart) = fact.conclusion(SuccPos(0)).at(key)
    if (DEBUG) println("useFor(" + fact.conclusion + ") key: " + keyPart + " in key context: " + keyCtx)

    pos => proof => {
      // split proof into ctx{expr} at pos
      val (ctx, expr) = proof.conclusion.at(pos)
      // instantiated unification of expr against keyPart
      val subst = inst(UnificationMatch(keyPart, expr))
      if (DEBUG) println("useFor(" + fact.conclusion.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
      if (DEBUG) println("useFor(" + fact.conclusion + ") on " + proof)
      Predef.assert(expr == subst(keyPart), "unification matched key successfully:\nexpr     " + expr + "\nequals   " + subst(keyPart) + "\nwhich is " + keyPart + "\ninstantiated by " + subst)

      /** useFor(subst, K,k, p, C,c)
        *
        * @param subst the substitution that unifies key k with occurrence c==subst(k).
        * @param K the context within which k occurs in fact.conclusion==K{k}
        * @param k the key
        * @param p the position at which occurrence c occurs in proof.conclusion
        * @param C the context within which occurrence c occurs in proof.conclusion(p.top)==C{c}
        * @param c the occurrence c at position p in proof.conclusion
        * @tparam T the type of the key
        * @return The Provable following from proof by using key k of fact at p in proof.conclusion
        * @see [[useFor()]]
        */
      def useFor[T <: Expression](subst: Subst, K: Context[T], k: T, p: Position, C: Context[Formula], c: Expression): Provable = {
        Predef.assert(subst(k) == c, "correctly matched input")
        Predef.assert(fact.conclusion.succ.head==K(k), "correctly matched key in fact")
        Predef.assert(proof.conclusion(p.top)==C(c), "correctly matched occurrence in input proof")
        Predef.assert(C(c).at(p.inExpr) ==(C, c), "correctly split at position p")
        Predef.assert(List((C, DotFormula), (C, DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

        /** Forward equivalence rewriting step to replace occurrence of instance of key k by instance of other o in context
          * {{{
          * G |- C{subst(k)}, D
          * ---------------------
          * G |- C{subst(o)}, D
          * }}}
          * or
          * {{{
          * G, C{subst(k)} |- D
          * ---------------------
          * G, C{subst(o)} |- D
          * }}}
          *
          * @param o
          */
        def equivStep(o: Expression): Provable = {
          require(fact.isProved, "currently want proved facts as input only\n" + fact)
          require(proof.conclusion.updated(p.top, C(subst(k)))==proof.conclusion, "expected context split")
          // |- fact: k=o or k<->o, respectively
          val sideUS: Provable = subst.toForward(fact)
          // |- subst(fact): subst(k)=subst(o) or subst(k)<->subst(o) by US
          val sideCE: Provable = CE(C)(sideUS)
          //@todo could shortcut proof by using "CO one-sided congruence" instead of CE
          // |- C{subst(k)} <-> C{subst(o)} by CQ or CE, respectively
          val sideImply: Provable = sideCE(Sequent(IndexedSeq(), IndexedSeq(Imply(C(subst(k)), C(subst(o))))),
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
            equivStep(o)

          case Equal(o, DotTerm) =>
            equivStep(o)

          case Equiv(DotFormula, o) =>
            equivStep(o)

          case Equiv(o, DotFormula) =>
            equivStep(o)


          case Imply(o, DotFormula) =>
            // |- o->k
            val deduct = inverseImplyR(fact)
            // o |- k
            val sideUS: Provable = subst.toForward(deduct)
            // subst(o) |- subst(k) by US

            //@note align context with implication o -> _ to get correct case (_ -> o or o -> _ depending on polarity)
            val Cmon = C.ctx match {
              case Equiv(ctxL, ctxR) if symbols(ctxL).contains(DotFormula) => CMon(Context(Equiv(ctxR, ctxL)))(sideUS)
              case _ => CMon(C)(sideUS)
            }

            // C{subst(k)} |- C{subst(o)} for polarity < 0
            // C{subst(o)} |- C{subst(k)} for polarity > 0
            // Ci{subst(k)} |- Ci{subst(o)} for polarity = 0, where <-> in C are turned into -> in Ci
            //@note do not need to inverse polarity if pos.isAnte, because sideImply implicitly inverses polarity for
            // ante by using Imply(kk, oo) in succ
            val polarity = FormulaTools.polarityAt(C.ctx, pos.inExpr)
            val (kk, oo) =
              if (polarity < 0) (C(subst(k)), C(subst(o)))
              else if (polarity > 0) (C(subst(o)), C(subst(k)))
              else {
                Predef.assert(polarity == 0)
                val Ci = Context(FormulaTools.makePolarityAt(C.ctx, pos.inExpr, -1))
                (Ci(subst(k)), Ci(subst(o)))
              }

            val sideImply = Cmon(Sequent(IndexedSeq(), IndexedSeq(Imply(kk, oo))), ImplyRight(SuccPos(0)))

            // |- C{subst(o)} -> C{subst(k)}
            val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(proof.conclusion.succ.length)}
            val coside: Provable = sideImply(
              if (pos.isSucc) proof.conclusion.updated(p.top, Imply(kk, oo))
              //@note drop p.top too and glue
              else Sequent(proof.conclusion.ante.patch(p.top.getIndex,Nil,1), proof.conclusion.succ).
                glue(Sequent(IndexedSeq(), IndexedSeq(Imply(kk, oo)))),
              CoHideRight(cutPos)
            )
            // G |- C{subst(o)}  -> C{subst(k)}, D by CoHideRight
            val proved = {
              if (pos.isSucc)
              // G |- C{subst(o)}, D by CutRight with coside
                Provable.startProof(proof.conclusion.updated(pos.top, oo))(
                  CutRight(kk, pos.top.asInstanceOf[SuccPos]), 0) (coside, 1)
              else
              // C{subst(o)}, G |- D by CutLeft with coside
                Provable.startProof(proof.conclusion.updated(pos.top, kk))(
                  CutLeft(oo, pos.top.asInstanceOf[AntePos]), 0) (coside, 1)
            } /*ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
                ) ensuring(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")*/

            if (polarity == 0 && pos.isSucc) {
              val equivified = proved(Provable.startProof(proved.subgoals.head)(EquivifyRight(pos.top.asInstanceOf[SuccPos]), 0), 0)
              //@note equiv assumed to always be top-level, so looking at inExpr.head determines direction
              val commuted =
                if (pos.inExpr.head == 1) equivified(CommuteEquivRight(pos.top.asInstanceOf[SuccPos]), 0)
                else equivified
              commuted(proof, 0)
            } else if (polarity == 0 && pos.isAnte) {
              ???
            } else proved(proof, 0)


          case Imply(DotFormula, o) =>
            // |- k->o
            val deduct = inverseImplyR(fact)
            // k |- o
            val sideUS: Provable = subst.toForward(deduct)
            // subst(k) |- subst(o) by US

            //@note align context with implication _ -> o to get correct case (_ -> o or o -> _ depending on polarity)
            val Cmon = C.ctx match {
              case Equiv(ctxL, ctxR) if symbols(ctxR).contains(DotFormula)  => CMon(Context(Equiv(ctxR, ctxL)))(sideUS)
              case _ => CMon(C)(sideUS)
            }

            // C{subst(o)} |- C{subst(k)} for polarity < 0
            // C{subst(k)} |- C{subst(o)} for polarity > 0
            // Ci{subst(o)} |- Ci{subst(k)} for polarity = 0, where <-> in C are turned into -> in Ci
            //@note do not need to inverse polarity if pos.isAnte, because sideImply implicitly inverses polarity for
            // ante by using Imply(kk, oo) in succ
            val polarity = FormulaTools.polarityAt(C.ctx, pos.inExpr)
            val (kk, oo) =
              if (polarity < 0) (C(subst(o)), C(subst(k)))
              else if (polarity > 0) (C(subst(k)), C(subst(o)))
              else {
                Predef.assert(polarity == 0)
                val Ci = Context(FormulaTools.makePolarityAt(C.ctx, pos.inExpr, 1))
                (Ci(subst(k)), Ci(subst(o)))
              }

            val impl = Imply(kk, oo)
            val sideImply = Cmon(Sequent(IndexedSeq(), IndexedSeq(impl)), ImplyRight(SuccPos(0)))

            // |- C{subst(k)} -> C{subst(o)}
            val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(proof.conclusion.succ.length)}
            val coside: Provable = sideImply(
              if (pos.isSucc) proof.conclusion.updated(p.top, impl)
              //@note drop p.top too and glue
              else Sequent(proof.conclusion.ante.patch(p.top.getIndex,Nil,1), proof.conclusion.succ).
                glue(Sequent(IndexedSeq(), IndexedSeq(impl))),
              CoHideRight(cutPos)
            )

            val proved = {
              // G |- C{subst(k)}  -> C{subst(o)}, D by CoHideRight
              if (pos.isSucc)
              // C{subst(k)}, G |- D by CutLeft with coside
                Provable.startProof(proof.conclusion.updated(pos.top, oo))(
                  CutRight(kk, pos.top.asInstanceOf[SuccPos]), 0) (coside, 1)
              else
              // G |- C{subst(o)}, D by CutRight with coside
                Provable.startProof(proof.conclusion.updated(pos.top, kk))(
                  CutLeft(oo, pos.top.asInstanceOf[AntePos]), 0) (coside, 1)
            } /*ensuring(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
              ) ensuring(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")*/

            if (polarity == 0 && pos.isSucc) {
              val equivified = proved(Provable.startProof(proved.subgoals.head)(EquivifyRight(pos.top.asInstanceOf[SuccPos]), 0), 0)
              //@note equiv assumed to always be top-level, so looking at inExpr.head determines direction
              val commuted =
                if (pos.inExpr.head == 0) equivified(CommuteEquivRight(pos.top.asInstanceOf[SuccPos]), 0)
                else equivified
              commuted(proof, 0)
            } else if (polarity == 0 && pos.isAnte) {
              ???
            } else proved(proof, 0)


          case Imply(prereq, remainder) if StaticSemantics.signature(prereq).intersect(Set(DotFormula,DotTerm)).isEmpty =>
            // try to prove prereq globally
            //@todo if that fails preserve context and fall back to CMon and C{prereq} -> ...
            /* {{{
             *                                         fact
             *                                   prereq -> remainder
             * ----------------master   ----------------------------- US
             * |- subst(prereq)         |- subst(prereq -> remainder)
             * ------------------------------------------------------ CutRight
             *         |- subst(remainder)
             * }}}
             * The resulting new fact subst(remainder) is then used via useFor
             */

            // |- subst(prereq)
            val prereqFact = TactixLibrary.proveBy(subst(prereq), TactixLibrary.master())
            require(prereqFact.isProved, "only globally provable requirements currently supported. Ese useAt instead " + prereqFact)

            // |- subst(remainder{k})
            val remFact: Provable = (Provable.startProof(subst(Context(remainder)(k)))
              // |- subst(prereq)      |- subst(prereq -> remainder)
              (CutRight(subst(prereq), SuccPos(0)), 0)
              // prove right branch   |- subst(prereq -> remainder)
              // right branch  |- subst(prereq -> remainder)  byUS(fact)
              (subst.toForward(fact), 1)
              // left branch   |- subst(prereq)
              (prereqFact, 0)
              )
            remFact ensuring(r => r.subgoals == fact.subgoals, "Proved / no new subgoals expected " + remFact)

            val remKey: PosInExpr = key.child
            require(remFact.conclusion(SuccPos(0)).at(remKey)._2 == subst(keyPart), "position guess within fact are usually expected to succeed " + remKey + " in\n" + remFact + "\nis remaining from " + key + " in\n" + fact)
            UnifyUSCalculus.this.useFor(remFact, remKey, inst)(pos)(proof)


          case DotFormula =>
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
    * Inverse of imply-right rule, which is admissible since invertible.
    * {{{
    *   G |- a -> b, D
    * ----------------
    *   G, a |- b, D
    * }}}
    *
    * @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008. Lemma 7"
    */
  private def inverseImplyR: ForwardTactic = pr => {
    val pos = SuccPos(0)
    val last = AntePos(pr.conclusion.ante.length)
    val Imply(a,b) = pr.conclusion.succ.head
    (Provable.startProof(pr.conclusion.updated(pos, b).glue(Sequent(IndexedSeq(a), IndexedSeq())))
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
  lazy val chase: DependentPositionTactic = chase(3,3)

  /** Chase with bounded breadth and giveUp to stop.
    *
    * @param breadth how many alternative axioms to pursue locally, using the first applicable one.
    *                Equivalent to pruning keys so that all lists longer than giveUp are replaced by Nil,
    *                and then all lists are truncated beyond breadth.
    * @param giveUp  how many alternatives are too much so that the chase stops without trying any for applicability.
    *                Equivalent to pruning keys so that all lists longer than giveUp are replaced by Nil.
    */
  def chase(breadth: Int, giveUp: Int): DependentPositionTactic = chase(breadth, giveUp, AxiomIndex.axiomsFor (_:Expression))
  def chase(breadth: Int, giveUp: Int, keys: Expression=>List[String]): DependentPositionTactic = chase(breadth, giveUp, keys, (ax,pos) => pr=>pr)
  def chase(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic): DependentPositionTactic =
    chaseI(breadth, giveUp,keys, modifier, ax=>us=>us)
  def chaseI(breadth: Int, giveUp: Int, keys: Expression=>List[String], inst: String=>(Subst=>Subst)): DependentPositionTactic =
    chaseI(breadth, giveUp, keys, (ax,pos)=>pr=>pr, inst)
  def chaseI(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic, inst: String=>(Subst=>Subst)): DependentPositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chase(e => keys(e) match {
      case l:List[String] if l.size > giveUp => Nil
      case l:List[String] => l.take(breadth)
    }, modifier, inst)
  }

  def chaseFor(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic): ForwardPositionTactic =
    chaseFor(breadth, giveUp,keys, modifier, ax=>us=>us)
  def chaseFor(breadth: Int, giveUp: Int, keys: Expression=>List[String], modifier: (String,Position)=>ForwardTactic, inst: String=>(Subst=>Subst)): ForwardPositionTactic = {
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
    *
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
            inst: String=>(Subst=>Subst) = ax=>us=>us): DependentPositionTactic = new DependentPositionTactic("chase") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
        if (sequent.sub(pos).isEmpty) throw new BelleError("ill-positioned " + pos + " in " + sequent + "\nin " +
          "chase\n(" + sequent + ")")
        CEat(chaseProof(sequent.sub(pos).get))(pos)
      }

      /** Construct a proof proving the answer of the chase of e, so either of e=chased(e) or e<->chased(e) */
      private def chaseProof(e: Expression): Provable = {
        // reflexive setup corresponds to no-progress chase
        val initial: Provable = e match {
          case t: Term =>      // t=t
            DerivedAxioms.equalReflex.fact(USubst(SubstitutionPair(FuncOf(Function("s_",None,Unit,Real),Nothing), t)::Nil))
          case f: Formula =>   // f<->f
            DerivedAxioms.equivReflexiveAxiom.fact(USubst(SubstitutionPair(PredOf(Function("p_",None,Unit,Bool),Nothing), f)::Nil))
        }
        Predef.assert(initial.isProved && initial.conclusion.ante.isEmpty && initial.conclusion.succ.length==1,
          "Proved reflexive start " + initial + " for " + e)
        if (DEBUG) println("chase starts at " + initial)
        //@note start the chase on the left-hand side
        val r = chaseFor(keys, modifier, inst) (SuccPosition(1, 0::Nil))(initial)
        if (DEBUG) println("chase(" + e.prettyString + ") = ~~> " + r + " done")
        r
      } ensuring(r => r.isProved, "chase remains proved: " + " final chase(" + e + ")")
    }
  }

  /** chaseFor: Chases the expression of Provables at given positions forward until it is chased away or can't be chased further without critical choices.
    *
    * Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
    * Follows canonical axioms toward all their recursors while there is an applicable simplifier axiom according to `keys`.
    *
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
               inst: String=>(Subst=>Subst) = ax=>us=>us): ForwardPositionTactic = pos => de => {
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
          val (key, recursor) = AxiomIndex.axiomIndex(ax)
          try {
            val axUse = modifier(ax,pos) (useFor(ax, key, inst(ax))(pos)(de))
            recursor.foldLeft(axUse)(
              (pf, cursor) => doChase(pf, pos + cursor)
            )
          } catch {case e: ProverException => throw e.inContext("useFor(" + ax + ", " + key.prettyString + ")\nin " + "chase(" + de.conclusion.sub(pos).get.prettyString + ")")}
        // take the first axiom among breadth that works for one useFor step
        case l: List[String] =>
          // useFor the first applicable axiom if any, or None
          def firstAxUse: Option[(Provable,List[PosInExpr])] = {
            for (ax <- l) try {
              val (key, recursor) = AxiomIndex.axiomIndex(ax)
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
                (pf, cursor) => doChase(pf, pos + cursor)
              )
          }
      }
    } ensuring(r => r.subgoals==de.subgoals, "chase keeps subgoals unchanged: " + " final chase(" + de.conclusion.sub(pos).get.prettyString + ")\nhad subgoals: " + de.subgoals)
    doChase(de,pos)
  }
}