/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.{axiomatic, closeTrue, coHideR, commuteEquivR, cutLR, cutL,
  cutR, equivR, equivifyR, implyR}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.StaticSemanticsTools._
import edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, AxiomIndex, Context, DerivedAxioms, FormulaTools, HereP, Position, PosInExpr, SuccPosition}

import scala.collection.immutable._
import scala.language.postfixOps

/**
 * Automatic unification-based Uniform Substitution Calculus with indexing.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 */
trait UnifyUSCalculus {
  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  /**
   * Throw exception if there is more than one open subgoal on the provable.
   */
  private def requireOneSubgoal(provable: Provable) =
    if(provable.subgoals.length != 1) throw new BelleError("Expected exactly one sequent in Provable")

  type Subst = UnificationMatch.Subst

  /** G: Gödel generalization rule reduces a proof of `|- [a;]p(x)` to proving the postcondition `|- p(x)` in isolation.
    * {{{
    *       p(??)
    *   ----------- G
    *    [a;]p(??)
    * }}}
    * @see [[monb]] with p(x)=True
    */
  lazy val G                  : BelleExpr         = DLBySubst.G
  /** allG: all generalization rule reduces a proof of `|- \forall x p(x)` to proving `|- p(x)` in isolation */
  lazy val allG               : BelleExpr         = ??? //AxiomaticRuleTactics.forallGeneralizationT
  /** CT: Term Congruence: Contextual Equivalence of terms at the indicated position to reduce an equality `c(f(x))=c(g(x))` to an equality `f(x)=g(x)` */
  //def CT(inEqPos: PosInExpr)  : Tactic         = ???
  /** CQ: Equation Congruence: Contextual Equivalence of terms at the indicated position to reduce an equivalence to an equation */
  //def CQ(inEqPos: PosInExpr)  : Tactic
  /** CE: Congruence: Contextual Equivalence at the indicated position to reduce an equivalence to an equivalence */
  //def CE(inEqPos: PosInExpr)  : Tactic
  /** monb: Monotone `[a;]p(x) |- [a;]q(x)` reduces to proving `p(x) |- q(x)` */
  lazy val monb               : BelleExpr         = DLBySubst.monb
  /** mond: Monotone `<a;>p(x) |- <a;>q(x)` reduces to proving `p(x) |- q(x)` */
  lazy val mond               : BelleExpr         = DLBySubst.mond



  /*******************************************************************
    * unification and matching based auto-tactics (backward tableaux/sequent)
    *******************************************************************/

  /** US(form) reduce the proof to a proof of form by a suitable uniform substitution obtained by unification */
  //def US(form: Sequent): Tactic = US(form)

  /** useAt(fact, tactic)(pos) uses the given fact (that'll be proved by tactic after unification) at the given position in the sequent (by unifying and equivalence rewriting). */
  //def useAt(fact: Formula, key: PosInExpr, tactic: Tactic, inst: Subst=>Subst): PositionTactic = useAt(fact, key, tactic, inst)
  //def useAt(fact: Formula, key: PosInExpr, tactic: Tactic): PositionTactic = useAt(fact, key, tactic)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Formula, key: PosInExpr, inst: Subst=>Subst): DependentPositionTactic = useAt(fact, key, nil, inst)
  def useAt(fact: Formula, key: PosInExpr): DependentPositionTactic = useAt(fact, key, nil)
  /** useAt(fact)(pos) uses the given fact at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(fact: Provable, key: PosInExpr, inst: Subst=>Subst): DependentPositionTactic = {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1)
    useAt(fact.conclusion.succ.head, key, byUS(fact), inst)
  }
  def useAt(fact: Provable, key: PosInExpr): DependentPositionTactic = {
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
  def useAt(lem: Lemma, key:PosInExpr, inst: Subst=>Subst): DependentPositionTactic = useAt(lem.fact, key, inst)
  def useAt(lem: Lemma, key:PosInExpr): DependentPositionTactic = useAt(lem.fact, key)
  def useAt(lem: Lemma)               : DependentPositionTactic = useAt(lem.fact, PosInExpr(0::Nil))
  /** useAt(axiom)(pos) uses the given axiom at the given position in the sequent (by unifying and equivalence rewriting). */
  def useAt(axiom: String, key: PosInExpr, inst: Subst=>Subst): DependentPositionTactic =
    if (Axiom.axioms.contains(axiom)) useAt(Axiom.axiom(axiom), key, inst)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useAt(DerivedAxioms.derivedAxiom(axiom), key, inst)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  def useAt(axiom: String, key: PosInExpr): DependentPositionTactic =
    if (Axiom.axioms.contains(axiom)) useAt(Axiom.axiom(axiom), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useAt(DerivedAxioms.derivedAxiom(axiom), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  def useAt(axiom: String, inst: Subst=>Subst): DependentPositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1, inst)
  def useAt(axiom: String): DependentPositionTactic = useAt(axiom, AxiomIndex.axiomIndex(axiom)._1)

  /** by(provable) is a pseudo-tactic that uses the given Provable to continue or close the proof (if it fits to what has been proved) */
  //@todo auto-weaken as needed (maybe even exchangeleft)
  def by(fact: Provable)  : BuiltInTactic = new BuiltInTactic("by") {
    override def result(provable: Provable): Provable = {
      require(provable.subgoals.size == 1 && provable.subgoals.head == fact.conclusion, "Conclusion of fact " + fact + " must match sole open goal in " + provable)
      if (provable.subgoals.size == 1 && provable.subgoals.head == fact.conclusion) provable.apply(fact, 0)
      else throw new BelleError("Conclusion of fact " + fact + " does not match sole open goal of " + provable)
    }
  }//new ByProvable(provable)
  /** by(lemma) is a pseudo-tactic that uses the given Lemma to continue or close the proof (if it fits to what has been proved) */
  def by(lemma: Lemma)        : BelleExpr = by(lemma.fact)
  /** byUS(provable) proves by a uniform substitution instance of provable, obtained by unification */
  def byUS(provable: Provable): BelleExpr = US(provable.conclusion) & by(provable)
  /** byUS(lemma) proves by a uniform substitution instance of lemma */
  def byUS(lemma: Lemma)      : BelleExpr  = byUS(lemma.fact)
  /** byUS(axiom) proves by a uniform substitution instance of axiom */
  def byUS(axiom: String)     : BelleExpr =
    if (Axiom.axioms.contains(axiom)) byUS(Axiom.axiom(axiom))
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) byUS(DerivedAxioms.derivedAxiom(axiom))
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

  /*******************************************************************
    * unification and matching based auto-tactics (backward tableaux/sequent)
    *******************************************************************/

  /**
   * US(form) uses a suitable uniform substitution to reduce the proof to instead proving `form`.
   * Unifies the current sequent with `form` and uses that unifier as a uniform substitution.
   * {{{
   *      form:
   *     g |- d
   *   --------- US where G=s(g) and D=s(d) where s=unify(form, G|-d)
   *     G |- D
   * }}}
   *
   * @author Andre Platzer
   * @param form the sequent to reduce this proof node to by a Uniform Substitution
   */
  def US(form: Sequent): DependentTactic = new DependentTactic("US") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        requireOneSubgoal(provable)
        val subst = UnificationMatch(form, provable.subgoals.head)
        if (DEBUG) println("  US(" + form.prettyString + ") unify: " + provable.subgoals.head + " matches against form " + form + " by " + subst)
        Predef.assert(provable.subgoals.head == subst(form), "unification must match: " + provable.subgoals.head + " is " + subst(form) + " which is " + form + " instantiated by " + subst)
        subst.toTactic(form)
    }
  }

  /**
   * useAt(fact)(pos) uses the given fact at the given position in the sequent.
   * Unifies fact the left or right part of fact with what's found at sequent(pos) and use corresponding
   * instance to make progress by reducing to the other side.
   * {{{
   *     G |- C{s(r)}, D
   *   ------------------ useAt(__l__<->r) if s=unify(c,l)
   *     G |- C{c}, D
   * }}}
   * and accordingly for facts that are `__l__->r` facts or conditional `c->(__l__<->r)` or `c->(__l__->r)` facts and so on,
   * where `__l__` indicates the key part of the fact.
   * useAt automatically tries proving the required assumptions/conditions of the fact it is using.
   *
   * Backward Tableaux-style proof analogue of [[useFor()]].

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
   * @see [[edu.cmu.cs.ls.keymaerax.tactics]]
   * @todo could directly use prop rules instead of CE if key close to HereP if more efficient.
   */
  def useAt(fact: Formula, key: PosInExpr, factTactic: BelleExpr, inst: Subst=>Subst = us=>us): DependentPositionTactic = new DependentPositionTactic("useAt") {
    private val (keyCtx:Context[_],keyPart) = fact.at(key)

    override def apply(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable) =>
          requireOneSubgoal(provable)
          val (ctx,expr) = provable.subgoals.head.at(pos)
          val subst = inst(UnificationMatch(keyPart, expr))
          if (DEBUG) println("useAt(" + fact.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
          Predef.assert(expr == subst(keyPart), "unification matched left successfully: " + expr + " is " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)
          //val keyCtxMatched = Context(subst(keyCtx.ctx))
          useAt(subst, keyCtx, keyPart, pos, ctx, expr, factTactic, provable.subgoals.head)
      }
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
    private def useAt[T <: Expression](subst: Subst, K: Context[T], k: T, p: Position, C:Context[Formula], c:Expression, factTactic: BelleExpr, sequent: Sequent): BelleExpr = {
      require(subst(k) == c, "correctly matched input")
      require(C(c).at(p.inExpr) == (C,c), "correctly split at position p")
      require(List((C,DotFormula),(C,DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

      /** Equivalence rewriting step */
      def equivStep(other: Expression, factTactic: BelleExpr): BelleExpr = {
        val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length)}
        lazy val expect = if (p.isSucc) Imply(C(subst(other)), C(subst(keyPart))) else Imply(C(subst(keyPart)), C(subst(other)))
        lazy val expectEquiv = if (p.isSucc) Equiv(C(subst(other)), C(subst(keyPart))) else Equiv(C(subst(keyPart)), C(subst(other)))
        //@note ctx(fml) is meant to put fml in for DotTerm in ctx, i.e apply the corresponding USubst.
        //@todo simplify substantially if subst=id
        debug("start useAt " + p) & cutLR(C(subst(other)))(p.top) <(
          //@todo would already know that ctx is the right context to use and subst(left)<->subst(right) is what we need to prove next, which results by US from left<->right
          //@todo could optimize equivalenceCongruenceT by a direct CE call using context ctx
          /* use cut */ debug("    use cut") & ident partial,
          /* show cut */
            debug("    show cut") &
            coHideR/*(expect)*/(cutPos) & assert(0, 1) & debug("    cohidden") &
            //@todo SuccPosition(0) should be SuccPosition(previous length) if cutting left?
            assert(expect, "useAt show implication")(SuccPos(0)) &
            equivifyR(SuccPos(0)) & debug("    equivified") &
            assert(expectEquiv, "useAt show equivalence")(SuccPos(0)) &
            debug("    CE coming up") & (
            if (other.kind==FormulaKind) CE(p.inExpr)
            else if (other.kind==TermKind) CQ(p.inExpr)
            else throw new IllegalArgumentException("Don't know how to handle kind " + other.kind + " of " + other)) &
            debug("    using fact tactic") & factTactic & debug("  done fact tactic")

        ) & debug("end   useAt " + p)
      }

      K.ctx match {
        case DotFormula if p.isTopLevel =>
          //@note this should be similar to byUS(fact) using factTactic to prove fact after instantiation
          US(Sequent(Nil, IndexedSeq(), IndexedSeq(k.asInstanceOf[Formula]))) & factTactic

        case DotFormula if !p.isTopLevel =>
          equivStep(True, equivR(SuccPosition(0)) <(
              coHideR(SuccPosition(0)) & factTactic,
              closeTrue(SuccPosition(0))
            ))

        case Equiv(DotFormula, other) =>
          equivStep(other, (if (p.isSucc) commuteEquivR(SuccPosition(0)) else ident) & factTactic)

        case Equiv(other, DotFormula) =>
          equivStep(other, (if (p.isAnte) commuteEquivR(SuccPosition(0)) else ident) & factTactic)

        case Equal(DotTerm, other) => ???
          //@todo analogous swap of directions for p.isSucc/isAnte as above
//          equivStep(other, /*@todo useAt("= commute") &*/ factTactic)

        case Equal(other, DotTerm) =>
          //@todo analogous swap of directions for p.isSucc/isAnte as above
          equivStep(other, factTactic)

        //@todo not sure if the following two cases really work as intended, but they seem to
        case Imply(other, DotFormula) if p.isSucc && p.isTopLevel =>
          cutR(subst(other))(p) <(
            /* use */ ident partial,
            /* show */ coHideR(p) & factTactic
          )

        case Imply(DotFormula, other) if p.isAnte && p.isTopLevel =>
          cutL(subst(other))(p) <(
            /* use */ ident partial,
            /* show */ lastR(coHideR) & factTactic
          )

        case Imply(other, DotFormula) if !(p.isSucc && p.isTopLevel) =>
          val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
          cutLR(C(subst(other)))(p.top) <(
            /* use */ ident partial,
            /* show */ coHideR(cutPos) & implyR(SuccPos(0)) &
              propCMon(p.inExpr) //@note simple approximation would be: ((Monb | Mond | allMon ...)*)
              // gather back to a single implication for axiom-based factTactic to succeed
              & implyRi()
              & factTactic
          )

        case Imply(DotFormula, other) if !(p.isAnte && p.isTopLevel) =>
          println("Check this useAt case")
          // same as "case Imply(other, DotFormula) if !(p.isSucc && p.isTopLevel)"
          val cutPos: SuccPos = p match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
          cutLR(C(subst(other)))(p.top) <(
            /* use */ ident partial,
            /* show */ coHideR(cutPos) & implyR(SuccPos(0)) &
              propCMon(p.inExpr) //@note simple approximation would be: ((Monb | Mond | allMon ...)*)
              // gather back to a single implication for axiom-based factTactic to succeed
              & implyRi()
              & factTactic
          )


        case Imply(prereq, remainder) if StaticSemantics.signature(prereq).intersect(Set(DotFormula,DotTerm)).isEmpty =>
          //@todo could do: if prereq provable by master then use remainder directly. Otherwise use CMon to show C{prereq} implies ....
          //@todo only prove remainder absolutely by proving prereq if that proof works out. Otherwise preserve context to prove prereq by master.
          //@todo check positioning etc.
          useAt(subst, new Context(remainder), k, p, C, c, cutR(subst(prereq))(SuccPosition(0)) <(
            //@note the roles of cutUseLbl and cutShowLbl are really swapped here, since the implication on cutShowLbl will be handled by factTactic
            //@todo don't work on prereq? Or make it customizable?
            /* use */ /* prove prereq: */ /*@todo: TactixLibrary.master*/ ???,
            /* show */ factTactic
          ), sequent)

        case Forall(vars, remainder) if vars.length==1 => ???
          //useAt(subst, new Context(remainder), k, p, C, c, /*@todo instantiateQuanT(vars.head, subst(vars.head))(SuccPos(0))*/ ident, sequent)

        //@todo unfold box by step*
        case Box(a, remainder) => ???
      }
    }

  }

  //////////////
  // Congruence Reasoning

  /**
   * CQ(pos) at the indicated position within an equivalence reduces contextual equivalence `p(left)<->p(right)` to argument equality `left=right`.
   * This tactic will use [[CE()]] under the hood as needed.
   * {{{
   *        f(x) = g(x)
   *   --------------------- CQ
   *    c(f(x)) <-> c(g(x))
   * }}}
   * @param inEqPos the position *within* the two sides of the equivalence at which the context DotTerm happens.
   * @see [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
   */
  def CQ(inEqPos: PosInExpr): DependentTactic = new DependentTactic("CQ congruence") {
    private val f_ = FuncOf(Function("f_", None, Real, Real), Anything)
    private val g_ = FuncOf(Function("g_", None, Real, Real), Anything)
    private val c_ = PredOf(Function("ctx_", None, Real, Bool), DotTerm)

    override def computeExpr(v: BelleValue): BelleExpr = v match  {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Expected single subgoal, but got " + provable.subgoals.size)
        val sequent = provable.subgoals.head
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
              axiomatic("CQ equation congruence", USubst(SubstitutionPair(c_, ctxF.ctx) :: SubstitutionPair(f_, f) :: SubstitutionPair(g_, g) :: Nil))
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
   * @param inEqPos the position *within* the two sides of the equivalence at which the context DotFormula happens.
   * @see [[UnifyUSCalculus.CE(Context)]]
   * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
   * @see [[UnifyUSCalculus.CE(Provable)]]
   */
  def CE(inEqPos: PosInExpr): DependentTactic = new DependentTactic("CE congruence") {
    private val p_ = PredOf(Function("p_", None, Real, Bool), Anything)
    private val q_ = PredOf(Function("q_", None, Real, Bool), Anything)
    private val c_ = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)

    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Expected single open goal, but got " + provable.subgoals.size)
        val sequent = provable.subgoals.head
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
              axiomatic("CE congruence", USubst(SubstitutionPair(c_, ctxP.ctx) :: SubstitutionPair(p_, p) :: SubstitutionPair(q_, q) :: Nil))
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
   * @param inEqPos the position *within* the two sides of the implication at which the context DotFormula happens.
   * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see [[UnifyUSCalculus.CMon(Context)]]
   */
  def CMon(inEqPos: PosInExpr): DependentTactic = new DependentTactic("CMon congruence") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Expected single open goal, but got " + provable.subgoals.size)
        val sequent = provable.subgoals.head
        require(sequent.ante.isEmpty && sequent.succ.length==1, "Expected empty antecedent and single succedent formula, but got " + sequent)
        sequent.succ.head match {
          case Imply(l, r) =>
            val (ctxP, p: Formula) = l.at(inEqPos)
            val (ctxQ, q: Formula) = r.at(inEqPos)
            require(ctxP == ctxQ, "Contexts must be equal, but " + ctxP + " != " + ctxQ)
            implyR(SuccPos(0)) &
              by(CMon(ctxP)(Provable.startProof(Sequent(Nil, IndexedSeq(p), IndexedSeq(q))))) &
              by(inverseImplyR(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Imply(p, q))))))
        }
    }
  }

  /** CE(fact) uses the equivalence `left<->right` or equality `left=right` or implication `left->right` fact for congruence
    * reasoning at the indicated position to replace `right` by `left` at indicated position (literally, no substitution).
    * Efficient unification-free version of [[UnifyUSCalculus#useAt(Provable, PosInExpr):PositionTactic]]
    * {{{
    *                          fact
    *   G |- C{q(x)}, D    p(x) <-> q(x)
    *   -------------------------------- CE(fact)
    *   G |- C{p(x)}, D
    * }}}
    * Similarly for antecedents or equality facts or implication facts, e.g.:
    * {{{
    *                          fact
    *   C{q(x)}, G |- D    p(x) <-> q(x)
    *   -------------------------------- CE(fact)
    *   C{p(x)}, G |- D
    * }}}
    * @see [[UnifyUSCalculus.CE(Provable,Context)]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @example CE(fact) is equivalent to CE(fact, Context("⎵".asFormula))
    */
  def CE(fact: Provable): DependentPositionTactic = new DependentPositionTactic("CE(Provable)") {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + fact)

    def splitFact: (Expression, Expression, BelleExpr, (PosInExpr=>BelleExpr)) = fact.conclusion.succ.head match {
      case Equal(l,r) => (l, r, equivifyR(SuccPos(0)), CQ)
      case Equiv(l,r) => (l, r, equivifyR(SuccPos(0)), CE)
      case Imply(l,r) => (l, r, ident, CMon)
      case _ => throw new IllegalArgumentException("CE expects equivalence or equality or implication fact " + fact)
    }
    val (other, key, equivify, tactic) = splitFact

    override def apply(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable) =>
          require(provable.subgoals.size == 1, "Expected single open goal, but got " + provable.subgoals.size)
          val sequent = provable.subgoals.head
          require(sequent.sub(pos).contains(key), "In-applicable CE(" + fact + ")\nat " + pos + "\nwhich is " + sequent.sub(pos) + "\nat " + sequent)
          val (ctx, _) = sequent.at(pos)
          val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
          cutLR(ctx(other))(pos.top) <(
            /* use */ ident,
            /* show */ debug("Foo") & coHideR(cutPos) & debug("Bar") & equivify & debug("Zee") & tactic(pos.inExpr) & debug("WTF?") & by(fact) & debug("Done")
            )
      }
    }
  }

  /** CE(fact,C) uses the equivalence `left<->right` or equality `left=right` or implication `left->right` fact for congruence
    * reasoning in the given context C at the indicated position to replace `right` by `left` in that context (literally, no substitution).
    * @see [[UnifyUSCalculus.CE(Provable)]]
    * @see [[useAt()]]
    * @see [[CE(Context)]]
    * @see [[UnifyUSCalculus.CE(PosInExpr)]]
    * @see [[UnifyUSCalculus.CQ(PosInExpr)]]
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @example CE(fact, Context("⎵".asFormula)) is equivalent to CE(fact)
    * @example CE(fact, Context("x>0&⎵".asFormula))(p) is equivalent to CE(fact)(p+1)
    *          except that the former only accepts x>0&⎵ as the shape of the context at position p.
    */
  def CE(fact: Provable, C: Context[Formula]): DependentPositionTactic = new DependentPositionTactic("CE(Provable,Context)") {
    require(fact.conclusion.ante.isEmpty && fact.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + fact)

    def splitFact: (Expression, Expression, BelleExpr, (Context[Formula]=>ForwardTactic)) = fact.conclusion.succ.head match {
      case Equal(l,r) => (l, r, equivifyR(SuccPos(0)), CE) //@note this CE can also use CQ
      case Equiv(l,r) => (l, r, equivifyR(SuccPos(0)), CE)
      case Imply(l,r) => (l, r, ident, CMon)
      case _ => throw new IllegalArgumentException("CE expects equivalence or equality or implication fact " + fact)
    }
    val (other, key, equivify, tactic) = splitFact


    override def apply(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable) =>
          require(provable.subgoals.size == 1, "Expected single open goal, but got " + provable.subgoals.size)
          val sequent = provable.subgoals.head
          require(sequent.sub(pos).contains(C(key)), "In-applicable CE(" + fact + ",\n" + C + ")\nat " + pos + "\nwhich is " + sequent.sub(pos).getOrElse("none") + "\nat " + sequent)
          val (posctx,c) = sequent.at(pos)
          val ctx = posctx(C)
          val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(sequent.succ.length + 1)}
          cutLR(ctx(other))(pos.top) <(
            /* use */ ident partial,
            /* show */ coHideR(cutPos) & //assertT(0,1) &
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
    * @see [[UnifyUSCalculus.CE(Provable)]]
    */
  def cutAt(repl: Expression): DependentPositionTactic = new DependentPositionTactic("cutAt") {
    override def apply(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = v match {
        case BelleProvable(provable) =>
          requireOneSubgoal(provable)
          val sequent = provable.subgoals.head
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


  /** useFor(axiom) use the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String): ForwardPositionTactic = useFor(axiom, AxiomIndex.axiomIndex(axiom)._1)

  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr): ForwardPositionTactic =
    if (Axiom.axioms.contains(axiom)) useFor(Axiom.axiom(axiom), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(DerivedAxioms.derivedAxiom(axiom), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)
  /** useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to conclude a new Provable */
  def useFor(axiom: String, key: PosInExpr, inst: Subst=>Subst): ForwardPositionTactic =
    if (Axiom.axioms.contains(axiom)) useFor(Axiom.axiom(axiom), key, inst)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(DerivedAxioms.derivedAxiom(axiom), key, inst)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

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
    * @see [[CE(PosInExpr]]
    * @see [[CE(Provable)]]
    * @see [[CMon(Context)]]
    * @todo likewise for Context[Term] using CT instead.
    */
  def CE(C: Context[Formula]): ForwardTactic = equiv => {
    require(equiv.conclusion.ante.isEmpty && equiv.conclusion.succ.length==1, "expected equivalence shape without antecedent and exactly one succedent " + equiv)
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

  /** CMon(C) will wrap any implication `left->right` fact it gets within a (positive or negative) context C by monotonicity.
    * {{{
    *      k |- o
    *   ------------ CMon if C{⎵} of positive polarity
    *   C{k} |- C{o}
    * }}}
    * @note The direction in the conclusion switches for negative polarity C{⎵}
    * @see [[UnifyUSCalculus.CMon(PosInExpr)]]
    * @see [[CE(Context)]]
    * @see [[PropositionalTactics.propCMon()]]
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
            (Provable.startProof(Sequent(Nil, ante, succ))
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(0), SuccPos(0)), 0)
            // right branch
            (CoHide2(AntePos(1), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

          case And(c, e) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(Nil, ante, succ))
            (AndLeft(AntePos(0)), 0)
            (AndRight(SuccPos(0)), 0)
            (Close(AntePos(1), SuccPos(0)), 1)
            // left branch
            (CoHide2(AntePos(0), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

          case Or(e, c) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(Nil, ante, succ))
            (OrRight(SuccPos(0)), 0)
            (OrLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(0)), 0)
            // right branch
            (CoHide2(AntePos(0), SuccPos(1)), 0)
            ) (monStep(Context(c), mon), 0)

          case Or(c, e) if !symbols(e).contains(DotFormula) =>
            (Provable.startProof(Sequent(Nil, ante, succ))
            (OrRight(SuccPos(0)), 0)
            (OrLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(1)), 1)
            // right branch
            (CoHide2(AntePos(0), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

          case Imply(e, c) if !symbols(e).contains(DotFormula) =>
            if (DEBUG) println("CMon check case: " + C + " to prove " + Sequent(Nil, ante, succ) + "\nfrom " + mon +
              "\nnext step in context " + Context(c) + "\n having current polarity " + polarity + " and new polarity " + localPolarity)
            (Provable.startProof(Sequent(Nil, ante, succ))
            (ImplyRight(SuccPos(0)), 0)
            (ImplyLeft(AntePos(0)), 0)
            (Close(AntePos(0), SuccPos(1)), 0)
            // right branch
            (CoHide2(AntePos(1), SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

          case Imply(c, e) if !symbols(e).contains(DotFormula) =>
            if (DEBUG) println("CMon check case: " + C + " to prove " + Sequent(Nil, ante, succ) + "\nfrom " + mon +
              "\nnext step in context " + Context(c) + "\n having current polarity " + polarity + " and new polarity " + localPolarity)
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
            //@note undo polarity switch from beginning of CMon, need to nibble off modality first
            val (ante, succ) =
              if (polarity < 0) (right, left)
              else (left, right)
            (Provable.startProof(Sequent(Nil, IndexedSeq(C(ante)), IndexedSeq(C(succ))))
            (AxiomaticRule("[] monotone", USubst(
              SubstitutionPair(ProgramConst("a_"), a)
                :: SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Context(c)(ante))
                :: SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Context(c)(succ))
                :: Nil
            )
            ), 0)
            ) (monStep(Context(c), mon), 0)

          case Diamond(a, c) if !symbols(a).contains(DotFormula) =>
            //@note undo polarity switch from beginning of CMon, need to nibble off modality first
            val (ante, succ) =
              if (polarity < 0) (right, left)
              else (left, right)
            (Provable.startProof(Sequent(Nil, IndexedSeq(C(ante)), IndexedSeq(C(succ))))
            (AxiomaticRule("<> monotone", USubst(
              SubstitutionPair(ProgramConst("a_"), a)
                :: SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Context(c)(ante))
                :: SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Context(c)(succ))
                :: Nil
            )
            ), 0)
            ) (monStep(Context(c), mon), 0)

          case m:Modal if symbols(m.program).contains(DotFormula) =>
            //@todo implement good cases. For example nibble of assign on both sides. Or random. Or ....
            throw new ProverException("No monotone context within programs " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")

          case Forall(vars, c) => //if !StaticSemantics.freeVars(subst(c)).toSymbolSet.intersect(vars.toSet).isEmpty =>
            require(vars.size == 1, "Universal quantifier must not be block quantifier")
            //@note would also work with all distribute and all generalization instead
            //@note would also work with Skolemize and all instantiate but disjointness is more painful
            val rename = (us: RenUSubst) => us ++ RenUSubst(Seq((Variable("x"), vars.head)))
            useFor("all eliminate", PosInExpr(1::Nil), rename)(AntePosition(0))(monStep(Context(c), mon)) (
              Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))),
              Skolemize(SuccPos(0))
            )

          /*case Forall(vars, c) if StaticSemantics.freeVars(subst(c)).toSymbolSet.intersect(vars.toSet).isEmpty =>
            useFor("vacuous all quantifier")(SuccPosition(0))(
              useFor("vacuous all quantifier")(AntePosition(0))(monStep(Context(c), mon))
            )*/

          case Exists(vars, c) =>
            require(vars.size == 1, "Existential quantifier must not be block quantifier")
            //@note would also work with exists distribute and exists generalization instead
            //@note would also work with Skolemize and all instantiate but disjointness is more painful
            val rename = (us: RenUSubst) => us ++ RenUSubst(Seq((Variable("x"), vars.head)))
            useFor("exists eliminate", PosInExpr(0::Nil), rename)(SuccPosition(0))(monStep(Context(c), mon)) (
              Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))),
              Skolemize(AntePos(0))
            )

          case Not(c) =>
            //@note no polarity switch necessary here, since global polarity switch at beginning of CMon
            (Provable.startProof(Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))
            (NotLeft(AntePos(0)), 0)
            (NotRight(SuccPos(0)), 0)
            ) (monStep(Context(c), mon), 0)

          case _ => throw new ProverException("Not implemented for other cases yet " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")")
        }
        ) ensuring(r => {true || r.conclusion ==
        //@todo ensuring is not correct yet (needs to keep track of when to switch polarity)
        (if (C.ctx == DotFormula && polarity < 0) Sequent(Nil, IndexedSeq(right), IndexedSeq(left))
        else if (C.ctx == DotFormula && polarity >= 0) Sequent(Nil, IndexedSeq(left), IndexedSeq(right))
        else if (polarity >= 0) Sequent(Nil, IndexedSeq(C(right)), IndexedSeq(C(left)))
        else Sequent(Nil, IndexedSeq(C(left)), IndexedSeq(C(right))))}, "Expected conclusion " + "\nin CMon.monStep(" + C + ",\nwhich is " + (if (polarity < 0) C(right) + "/" + C(left) else C(left) + "/" + C(right)) + ",\non " + mon + ")"
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
    * and accordingly for facts that are `__l__->r` facts or conditional `c->(__l__<->r)` or `c->(__l__->r)` facts and so on,
    * where `__l__` indicates the key part of the fact.
    * useAt automatically tries proving the required assumptions/conditions of the fact it is using.
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
    * @see [[edu.cmu.cs.ls.keymaerax.tactics]]
    */
  def useFor(fact: Provable, key: PosInExpr, inst: Subst=>Subst = (us => us)): ForwardPositionTactic = {
    val (keyCtx: Context[_], keyPart) = fact.conclusion(SuccPos(0)).at(key)
    if (DEBUG) println("useFor(" + fact.conclusion + ") key: " + keyPart + " in key context: " + keyCtx)

    pos => proof => {

      val (ctx, expr) = proof.conclusion.at(pos)
      val subst = inst(UnificationMatch(keyPart, expr))
      if (DEBUG) println("useFor(" + fact.conclusion.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst)
      if (DEBUG) println("useFor(" + fact.conclusion + ") on " + proof)
      Predef.assert(expr == subst(keyPart), "unification matched left successfully: " + expr + " is " + subst(keyPart) + " which is " + keyPart + " instantiated by " + subst)

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
      def useFor[T <: Expression](subst: Subst, K: Context[T], k: T, p: Position, C: Context[Formula], c: Expression): Provable = {
        Predef.assert(subst(k) == c, "correctly matched input")
        Predef.assert(fact.conclusion.succ.head==K(k), "correctly matched key in fact")
        Predef.assert(proof.conclusion(p.top)==C(c), "correctly matched occurrence in input proof")
        Predef.assert(C(c).at(p.inExpr) ==(C, c), "correctly split at position p")
        Predef.assert(List((C, DotFormula), (C, DotTerm)).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

        /** Equivalence rewriting step to replace occurrence of instance of key k by instance of other o in context */
        def equivStep(o: Expression, factTactic: BelleExpr): Provable = {
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
            equivStep(o, useAt("= commute") & byUS(fact))

          case Equiv(DotFormula, o) =>
            equivStep(o, byUS(fact))

          case Equiv(o, DotFormula) =>
            equivStep(o, commuteEquivR(SuccPos(0)) & byUS(fact))

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
            val sideImply = Cmon(Sequent(Nil, IndexedSeq(), IndexedSeq(impl)), ImplyRight(SuccPos(0)))

            // |- C{subst(k)} -> C{subst(o)}
            val cutPos: SuccPos = pos match {case p: SuccPosition => p.top case p: AntePosition => SuccPos(proof.conclusion.succ.length)}
            val coside: Provable = sideImply(
              if (pos.isSucc) proof.conclusion.updated(p.top, impl)
              //@note drop p.top too and glue
              else Sequent(Nil, proof.conclusion.ante.patch(p.top.getIndex,Nil,1), proof.conclusion.succ).
                glue(Sequent(Nil, IndexedSeq(), IndexedSeq(impl))),
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
            throw new ProverException("Not implemented for other cases yet, see useAt: " + K)

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
   * {{{
   *   G |- a -> b, D
   * ----------------
   *   G, a |- b, D
   * }}}
    * @see "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages 143-189, 2008. Lemma 7"
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
}
