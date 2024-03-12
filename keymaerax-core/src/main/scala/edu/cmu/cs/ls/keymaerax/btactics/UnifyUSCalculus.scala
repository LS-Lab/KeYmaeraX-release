/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{InapplicableUnificationKeyFailure, _}
import edu.cmu.cs.ls.keymaerax.btactics.SequentCalculus.{andLi => _, implyRi => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.closeTrue
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.infrastruct.StaticSemanticsTools._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.btactics.macros.{AxiomInfo, DerivationInfo, ProvableInfo, Tactic, TacticInfo}
import edu.cmu.cs.ls.keymaerax.pt.{ElidingProvable, ProvableSig, TermProvable}
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position.seqPos2Position
import edu.cmu.cs.ls.keymaerax.parser.Declaration
import org.slf4j.LoggerFactory

import scala.collection.immutable._
import scala.reflect.runtime.universe
import scala.util.Try

/**
 * Automatic unification-based Uniform Substitution Calculus with indexing. Provides a tactic framework for
 * automatically applying axioms and axiomatic rules by matching inputs against them by unification according to the
 * axiom's [[AxIndex]].
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[UnifyUSCalculus]]
 */
object UnifyUSCalculus extends TacticProvider with UnifyUSCalculus {

  /** @inheritdoc */
  override def getInfo: (Class[_], universe.Type) = (UnifyUSCalculus.getClass, universe.typeOf[UnifyUSCalculus.type])
}

/**
 * Automatic unification-based Uniform Substitution Calculus with indexing. Provides a tactic framework for
 * automatically applying axioms and axiomatic rules by matching inputs against them by unification according to the
 * axiom's [[AxIndex]].
 *
 * This central collection of unification-based algorithms for focused proof strategies is the basis for using axioms
 * and axiomatic proof rules in flexible ways. It is also central for deciding upon their succession in proof
 * strategies, e.g., which steps to take next.
 *
 * The most important algorithms are:
 *   - [[UnifyUSCalculus.useAt()]] makes use of a (derived) axiom or axiomatic rule in any position and logically
 *     transforms the goal to prove what is required for the transformation.
 *   - [[UnifyUSCalculus.chase]] chains together a sequence of canonical useAt inferences to make a formula disappear
 *     (chase it away) as far as possible.
 *
 * Which part of a (derived) axiom to latch on to during a `useAt` is determined by the unification keys in the
 * [[AxiomInfo.theKey]]. Which resulting subexpressions to consider next during a `chase` is determined by the recursors
 * in the [[AxiomInfo.theRecursor]]. What unifier is used for the default key is, in turn, determined by
 * [[AxiomInfo.unifier]]. Which (derived) axiom is the canonical one to decompose a given expression is determined by
 * [[AxIndex.axiomsFor()]] Default keys and default recursors and default axiom indices can be overwritten by specifing
 * extra arguments. This can be useful for noncanonical useAts or chases.
 *
 * The combination of the UnifyUSCalculus algorithms make it possible to implement a tactic for using an axiom as
 * follows:
 * {{{
 *   useAt(Ax.composeb)
 * }}}
 * Such a tactic can then be applied in different positions of a sequent, e.g.:
 * {{{
 *   useAt(Ax.composeb)(1)
 *   useAt(Ax.composeb)(-2)
 *   useAt(Ax.composeb)(1, 1::0::Nil)
 * }}}
 *
 * The combination of the UnifyUSCalculus algorithms also make it possible to implement longer proof strategies. For
 * example, completely chasing away a formula by successively using the canonical axioms on the resulting formulas is:
 * {{{
 *   chase
 * }}}
 * Applying it at different positions of a sequent proceeds as follows, e.g.:
 * {{{
 *   chase(1)
 *   chase(-2)
 *   chase(1, 1::0::Nil)
 * }}}
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[AxiomInfo]]
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.infrastruct.UnificationMatch]]
 * @see
 *   [[AxIndex]]
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. arXiv:1601.06183
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015.
 * @Tactic
 *   completed
 */
trait UnifyUSCalculus {
  private val logger = LoggerFactory.getLogger(getClass) // @note instead of "with Logging" to avoid cyclic dependencies
  /** Whether to use a liberal context via replaceAt instead of proper Context substitutions */
  private val LIBERAL = Context.GUARDED

  /** The (generalized) substitutions used for unification */
  type Subst = UnificationMatch.Subst

  /** Which matcher this unification USubst calculus uses */
  private val defaultMatcher = UnificationMatch

  /** Whether to benefit from linearity info about axioms using [[LinearMatcher]] */
  private val OPTIMIZE = System.getProperty("SPEED", "true") == "true"

  /** The default position if no key has been specified, no key has been declared, and no key can be inferred. */
  private val defaultPosition = PosInExpr(0 :: Nil)

  // utility tactics

  /**
   * skip is a no-op tactic that has no effect Identical to [[nil]] but different name
   * @see
   *   [[TactixLibrary.done]]
   */
  @Tactic()
  val skip: BuiltInTactic = anonnoop { Idioms.ident.result }

  /** nil=skip is a no-op tactic that has no effect */
  @Tactic()
  val nil: BuiltInTactic = anonnoop { Idioms.nil.result }

  /**
   * A no-op tactic that as no effect but marks an open proof task.
   * @see
   *   [[skip]],[[nil]]
   */
  @Tactic()
  val todo: BuiltInTactic = anonnoop { Idioms.todo.result }

  /**
   * fail is a tactic that always fails as being inapplicable
   * @see
   *   [[skip]]
   */
  @Tactic()
  val fail: BuiltInTactic = anon { (_: ProvableSig) => throw new TacticInapplicableFailure("fail") }

  /* ******************************************************************
   * Stepping auto-tactic
    *******************************************************************/

  /**
   * Make the canonical simplifying proof step based at the indicated position except when an unknown decision needs to
   * be made (e.g. invariants for loops or for differential equations). Using the provided [[AxIndex]].
   *
   * @author
   *   Andre Platzer
   * @note
   *   Efficient source-level indexing implementation.
   * @see
   *   [[AxIndex]]
   * @see
   *   [[UnifyUSCalculus.chase]]
   * @see
   *   [[HilbertCalculus.stepAt]]
   */
  def stepAt(axiomIndex: Expression => Option[DerivationInfo]): DependentPositionTactic =
    anon { (pos: Position, sequent: Sequent) =>
      {
        // @e steps may create labels, which means stepAt has to be a dependent tactic at the moment
        val sub = sequent.sub(pos)
        if (sub.isEmpty) throw new IllFormedTacticApplicationException(
          "ill-positioned " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")"
        )
        axiomIndex(sub.get) match {
          case Some(axiom) =>
            logger.debug("stepAt {}", axiom)
            axiom.belleExpr match {
              case ap: AtPosition[_] => ap(pos)
              case expr: BelleExpr => expr
              case expr => throw new TacticInapplicableFailure(
                  "No axioms or rules applicable for " + sub
                    .get + " which is at position " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")" + "\ngot " + expr
                )
            }
          case None => throw new TacticInapplicableFailure(
              "No axioms or rules applicable for " + sub
                .get + " which is at position " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")"
            )
        }
      }
    }

  /* ******************************************************************
   * close or proceed in proof by providing a Provable fact
     *******************************************************************/

  /**
   * by(pi) uses the given provable with its information literally to continue or close the proof (if it fits to what
   * has been proved).
   *
   * @param pi
   *   the information for the Provable to use, e.g., from [[Ax]].
   */
  def by(pi: ProvableInfo): BelleExpr = by(pi.provable, pi.codeName)

  /**
   * by(provable) uses the given Provable literally to continue or close the proof (if it fits to what has been proved
   * so far)
   * @param fact
   *   the Provable to drop into the proof to proceed or close it if proved.
   * @param name
   *   the name to use/record for the tactic
   * @migration
   *   If possible use by(ProvableInfo) instead, which is faster and more robust.
   */
  // @todo auto-weaken as needed (maybe even exchangeleft)
  @deprecated("use by(ProvableInfo) instead if possible.")
  // If no name is given, just record as anonymous tactic because ProvableSig serialization is not supported
  def by(fact: => ProvableSig, name: String = TacticFactory.ANON): BuiltInTactic = new BuiltInTactic(name) {
    override def result(provable: ProvableSig): ProvableSig = {
      require(
        provable.subgoals.size == 1 && provable.subgoals.head == fact.conclusion,
        "Conclusion of fact\n" + fact + "\nmust match sole open goal in\n" + provable,
      )
      if (provable.subgoals.size == 1 && provable.subgoals.head == fact.conclusion) provable.apply(fact, 0)
      else throw new BelleUnexpectedProofStateError(
        "Conclusion of fact " + fact + " does not match sole open goal of " + provable,
        provable.underlyingProvable,
      )
    }
  }
  def by(lemma: Lemma): BelleExpr = if (lemma.name.isDefined) by(lemma.fact, lemma.name.get) else by(lemma.fact)

  // by with given substitutions

  /**
   * by(pi,subst) uses the given axiom or axiomatic rule under the given substitution to prove the sequent.
   * {{{
   *    s(a) |- s(b)      a |- b
   *   ------------- rule(---------) if s(g)=G and s(d)=D
   *      G  |-  D        g |- d
   * }}}
   *
   * @author
   *   Andre Platzer
   * @param pi
   *   the provable to use to prove the sequent
   * @param subst
   *   what substitution `s` to use for instantiating the fact `pi`.
   * @see
   *   [[byUS()]]
   */
  def by(pi: ProvableInfo, subst: USubst): BelleExpr = by(pi.provable(subst), pi.codeName)
  def by(pi: ProvableInfo, subst: Subst): BelleExpr = by(subst.toForward(pi.provable), pi.codeName)

  def by(lemma: Lemma, subst: USubst): BelleExpr = by(lemma.fact(subst))

  /** by(name,subst) uses the given axiom or axiomatic rule under the given substitution to prove the sequent. */
  def by(lemma: Lemma, subst: Subst): BelleExpr = by(subst.toForward(lemma.fact))

  /* ******************************************************************
   * close/proceed by providing a Provable fact to unify and substitute with
     *******************************************************************/

  /**
   * byUS(pi) proves by a uniform substitution instance of provable (information) or axiom or axiomatic rule, obtained
   * by unification with the current goal. Like [[by(ProvableInfo,USubst)]] except that the required substitution is
   * automatically obtained by unification.
   * @see
   *   [[UnifyUSCalculus.US()]]
   */
  // @todo
  def byUS(pi: ProvableInfo): BelleExpr = new NamedTactic(pi.codeName, byUS(pi.provable))

  /**
   * byUS(pi) proves by a uniform substitution instance of provable (information), obtained by unification with the
   * current goal. Like [[by(ProvableInfo,USubst)]] except that the required substitution is automatically obtained by
   * unification.
   * @see
   *   [[UnifyUSCalculus.US()]]
   */
  def byUS(provable: ProvableSig): BuiltInTactic = US(provable) // US(provable.conclusion) & by(provable)
  /** byUS(lemma) proves by a uniform substitution instance of lemma. */
  def byUS(lemma: Lemma): BelleExpr = byUS(lemma.fact)

  /**
   * rule(pi,inst) uses the given axiom or axiomatic rule to prove the sequent. Unifies the fact's conclusion with the
   * current sequent and proceed to the instantiated premise of `fact`.
   * {{{
   *    s(a) |- s(b)      a |- b
   *   ------------- rule(---------) if s(g)=G and s(d)=D
   *      G  |-  D        g |- d
   * }}}
   *
   * The behavior of rule(Provable) is essentially the same as that of by(Provable) except that the former prefetches
   * the uniform substitution instance during tactics applicability checking.
   *
   * @author
   *   Andre Platzer
   * @param pi
   *   the provable info for the fact to use to prove the sequent
   * @param inst
   *   Transformation for instantiating additional unmatched symbols that do not occur in the conclusion. Defaults to
   *   identity transformation, i.e., no change in substitution found by unification. This transformation could also
   *   modify the unifier if other cases than the most-general unifier are preferred.
   * @see
   *   [[byUS()]]
   * @see
   *   [[by()]]
   */
  def byUS(pi: ProvableInfo, inst: Subst => Subst): BelleExpr = byUS(pi.provable, inst)

  private[btactics] def byUS(fact: ProvableSig, inst: Subst => Subst = us => us): BelleExpr = {
    // @todo could optimize to skip s.getRenamingTactic if fact's conclusion has no explicit variables in symbols
    def renameAndSubst = (us: RenUSubst) => {
      val s = inst(us)
      // @todo why not use s.toForward(fact) as in byUS(fact) instead of renaming the goal itself.
      // @todo unsure about use of renaming
      s.getRenamingTactic & by(fact(s.substitution.usubst))
    }
    USubstPatternTactic((SequentType(fact.conclusion), renameAndSubst) :: Nil)
  }

  private[btactics] def byUS(lemma: Lemma, inst: Subst => Subst): BelleExpr = byUS(lemma.fact, inst)

  /** Do-not-call: exclusively for internal tactic interpreter usage. */
  @deprecated("Exclusively use for tactic interpreters")
  @Tactic(("US", "byUS"), codeName = "byUS", conclusion = "|- S(P)", premises = "|- P")
  private[btactics]
  // NB: anon (Sequent) is necessary even though argument "seq" is not referenced:
  // this ensures that TacticInfo initialization routine can initialize byUSX without executing the body
  def byUSX(P: String, S: Option[Formula]): InputTactic = inputanon { (_seq: Sequent) =>
    S match {
      case None => TactixLibrary.byUS(AxiomInfo(P), us => us)
      case Some(substFml: Formula) =>
        val subst = RenUSubst(
          FormulaTools
            .conjuncts(substFml)
            .map({
              case Equal(l, r) => (l, r)
              case Equiv(l, r) => (l, r)
              case s => throw new IllegalArgumentException(
                  "Expected substitution of the shape t=s or p<->q, but got " + s.prettyString
                )
            })
        )
        TactixLibrary.byUS(AxiomInfo(P), (_: UnificationMatch.Subst) => subst)
    }
  }

  /* ******************************************************************
   * unification and matching based auto-tactics (backward tableaux/sequent)
     *******************************************************************/

  import TacticFactory._

  import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors.AxiomInfoAugmentor

  /**
   * useAt(axiom)(pos) uses the given (derived) axiom/axiomatic rule at the given position in the sequent (by unifying
   * and equivalence rewriting).
   */
  def useAt(axiom: ProvableInfo): BuiltInPositionTactic = useAtImpl(axiom)

  /** Do-not-call: exclusively for internal tactic interpreter usage. */
  // @note serializes as useAt({`axiomName`},{`k`})
  @deprecated("Exclusively use for tactic interpreters") @Tactic("useAt", codeName = "useAt")
  private[btactics] def useAtX(axiom: String, key: Option[String]): DependentPositionWithAppliedInputTactic =
    inputanon { (pos: Position, seq: Sequent) =>
      val keyPos = key.map(k => PosInExpr(k.split("\\.").map(Integer.parseInt).toList))
      val info = AxiomInfo(axiom)
      TryCatch(
        keyPos match {
          case None => TactixLibrary.useAt(info)(pos) // @note serializes as codeName
          case Some(k) =>
            if (k != info.key) TactixLibrary.useAt(info.provable, k)(pos)
            else TactixLibrary.useAt(info)(pos) // @note serializes as codeName
        },
        classOf[InapplicableUnificationKeyFailure],
        (ex: InapplicableUnificationKeyFailure) => {
          val keyExpr = keyPos match {
            case None => info.provable.conclusion.sub(SuccPosition.base0(0, info.key))
            case Some(k) => info.provable.conclusion.sub(SuccPosition.base0(0, k))
          }
          throw new InapplicableUnificationKeyFailure(
            "Axiom " + axiom + " is not applicable at " +
              seq.sub(pos).map(_.prettyString).getOrElse("<unknown>") +
              "; cannot match with axiom key " + keyExpr.map(_.prettyString).getOrElse("<unknown>"),
            ex,
          )
        },
      )
    }

  /**
   * useAt(axiom)(pos) uses the given axiom/axiomatic rule at the given position in the sequent (by unifying and
   * equivalence/implicational rewriting). Unifies the left or right part of fact with what's found at sequent(pos) and
   * use corresponding instance to make progress by reducing to the other side.
   * {{{
   *     G |- C{s(r)}, D
   *   ------------------ useAt(__l__<->r) if s=unify(c,l)
   *     G |- C{c}, D
   * }}}
   * and accordingly for implication facts that are `__l__->r` facts or conditional equivalences `p->(__l__<->r)` or
   * `p->(__l__->r)` facts and so on, where `__l__` indicates the key part of the fact. useAt automatically tries
   * proving the required assumptions/conditions of the fact it is using.
   *
   * Backward Tableaux-style proof analogue of [[useFor()]].
   *
   * Tactic specification:
   * {{{
   * useAt(fact)(p)(F) = let (C,c)=F(p) in
   *   case c of {
   *     s=unify(fact.left,_) => CutRight(C(s(fact.right))(p) ; <(
   *       "use cut": skip
   *       "show cut": EquivifyRight(p.top) ; CoHide(p.top) ; CE(C(_)) ; fact
   *     )
   *     s=unify(fact.right,_) => accordingly with an extra commuteEquivRightT
   *   }
   * }}}
   *
   * @author
   *   Andre Platzer
   * @param axiom
   *   describing what fact to use to simplify at the indicated position of the sequent
   * @param key
   *   the part of the Formula fact to unify the indicated position of the sequent with
   * @param inst
   *   Transformation for instantiating additional unmatched symbols that do not occur in fact(key). Defaults to
   *   identity transformation, i.e., no change in substitution found by unification. This transformation could also
   *   change the substitution if other cases than the most-general unifier are preferred.
   * @example
   *   useAt(AxiomInfo("[;] choice", PosInExpr(0::Nil))(0, PosInExpr(1::1::Nil)) applied to the indicated 1::1::Nil
   *   position of [x:=1;][{x'=22}] [x:=2*x;++x:=0;]x>=0 turns it into [x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)
   * @see
   *   [[useFor()]]
   * @todo
   *   could directly use prop rules instead of CE if key close to HereP if more efficient.
   */
  def useAt(axiom: ProvableInfo, key: PosInExpr, inst: Option[Subst] => Subst): BuiltInPositionTactic =
    useAtWithImpl(axiom, key, inst)

  /**
   * useAt(axiom)(pos) uses the given (derived) axiom/axiomatic rule at the given position in the sequent (by unifying
   * and equivalence rewriting), with a given instantiation augmentation.
   * @param inst
   *   transformation augmenting or replacing the uniform substitutions after unification with additional information.
   */
  def useAt(axiom: AxiomInfo, inst: Option[Subst] => Subst): BuiltInPositionTactic = useAtImpl(axiom, inst)

  /**
   * useAt(axiom)(pos) uses the given (derived) axiom/axiomatic rule at the given position in the sequent (by unifying
   * and equivalence rewriting), overwriting key.
   * @param key
   *   the optional position of the key in the axiom to unify with.
   */
  def useAt(axiom: ProvableInfo, key: PosInExpr): BuiltInPositionTactic = useAtWithImpl(axiom, key)

  /**
   * useAt(lem)(pos) uses the given lemma at the given position in the sequent (by unifying and equivalence rewriting).
   * @param key
   *   the optional position of the key in the axiom to unify with.
   * @param inst
   *   optional transformation augmenting or replacing the uniform substitutions after unification with additional
   *   information.
   */
  def useAt(lem: Lemma, key: PosInExpr, inst: Option[Subst] => Subst): BuiltInPositionTactic = lem.name match {
    case Some(name) if ProvableInfo.existsStoredName(name) =>
      val info = ProvableInfo.ofStoredName(name)
      if (info.provable == lem.fact) useAt(info, key, inst)
      else {
        logger.info("INFO: useAt({}) has an incompatible lemma name, which may disable tactic extraction", name)
        useAt(lem.fact, key, inst)
      }
    case Some(name) if !ProvableInfo.existsStoredName(name) => useAt(lem.fact, key, inst)
    case None =>
      logger.info("INFO: useAt of an anonymous lemma may disable tactic extraction")
      useAt(lem.fact, key, inst)
  }
  def useAt(lem: Lemma, key: PosInExpr): BuiltInPositionTactic = useAt(
    lem,
    key,
    (us: Option[Subst]) =>
      us.getOrElse(
        throw new InapplicableUnificationKeyFailure(
          "No substitution found by unification for " + lem + ", fix axiom key or try to patch locally with own substitution"
        )
      ),
  )

  /**
   * useAt(lem)(pos) uses the given lemma at the given position in the sequent (by unifying and equivalence rewriting).
   */
  def useAt(lem: Lemma): BuiltInPositionTactic = lem.name match {
    case Some(name) if ProvableInfo.existsStoredName(name) =>
      val info = ProvableInfo.ofStoredName(name)
      if (info.provable == lem.fact) useAt(info)
      else {
        logger.info("INFO: useAt({}) has an incompatible lemma name, which may disable tactic extraction", name)
        useAt(lem.fact)
      }
    case _ => useAt(lem, PosInExpr(0 :: Nil))
  }

  /**
   * useExpansionAt(axiom)(pos) uses the given axiom at the given position in the sequent (by unifying and equivalence
   * rewriting) in the direction that expands as opposed to simplifies operators.
   * @see
   *   [[useAt(AxiomInfo)]]
   */
  def useExpansionAt(axiom: AxiomInfo): BuiltInPositionTactic = useAt(axiom, axiom.key.sibling)

  /**
   * ***************************************************************** unification and matching based auto-tactics
   * (backward tableaux/sequent)
   */

  /**
   * US(subst, fact) reduces the proof to the given fact, whose uniform substitution instance under `subst` the current
   * goal is. When `fact` is an axiom:
   * {{{
   *       *              *
   *   ---------   if  -------- fact
   *     G |- D         g |- d
   *   where G=s(g) and D=s(d)
   * }}}
   * When `fact` is an axiomatic rule:
   * {{{
   *   s(g1) |- s(d1) ... s(gn) |- s(dn)        g1 |- d1 ... gn |- dn
   *   ---------------------------------   if  ----------------------- fact
   *           G |- D                                   g |- d
   *   where G=s(g) and D=s(d)
   * }}}
   * @param subst
   *   the substitution `s` that instantiates fact `g |- d` to the present goal `G |- D`.
   * @param fact
   *   the provable for the axiom `g |- d` to reduce the proof to (accordingly for axiomatic rules).
   * @see
   *   [[US(USubst,ProvableSig)]]
   */
  def US(subst: USubst, fact: ProvableInfo): BuiltInTactic = US(subst, fact.provable)

  /**
   * US(subst, fact) reduces the present proof to a proof of `fact`, whose uniform substitution instance under `subst`
   * the current goal is.
   * {{{
   *   s(g1) |- s(d1) ... s(gn) |- s(dn)        g1 |- d1 ... gn |- dn
   *   ---------------------------------   if  ----------------------- fact
   *           G |- D                                   g |- d
   *   where G=s(g) and D=s(d)
   * }}}
   * @param subst
   *   the substitution `s` that instantiates fact `g |- d` to the present goal `G |- D`.
   * @param fact
   *   the fact `g |- d` to reduce the proof to. Facts do not have to be proved yet.
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(USubst)]]
   * @see
   *   [[US(USubst, ProvableInfo)]]
   */
  def US(subst: USubst, fact: ProvableSig): BuiltInTactic = by(fact(subst))

  // *********************
  // main implementations
  // *********************

  /**
   * US(subst) uses a uniform substitution of rules to transform an entire provable.
   * {{{
   *    G1 |- D1 ... Gn |- Dn              s(G1) |- s(D1) ... s(Gn) |- s(Dn)
   *   -----------------------     =>     -----------------------------------   (USR)
   *            G |- D                                s(G) |- s(D)
   * }}}
   *
   * @param subst
   *   The uniform substitution `s` (of no free variables) to be used on the premises and conclusion of the provable.
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(USubst)]]
   * @see
   *   [[US(USubst, ProvableInfo)]]
   */
  def US(subst: USubst): BuiltInTactic = anon { (provable: ProvableSig) => provable(subst) }

  /**
   * US(fact) uses a suitable uniform substitution to reduce the proof to the proof of `fact`. Unifies the current
   * sequent with `fact.conclusion`. Use that unifier as a uniform substitution to instantiate `fact` with.
   * {{{
   *      fact:
   *     g |- d
   *   --------- US where G=s(g) and D=s(d) where s=unify(fact.conclusion, G|-D)
   *     G |- D
   * }}}
   *
   * @author
   *   Andre Platzer
   * @param fact
   *   the proof to reduce this proof to by a suitable Uniform Substitution.
   * @see
   *   [[byUS()]]
   */
  def US(fact: ProvableSig): BuiltInTactic = anon { pr: ProvableSig =>
    {
      val sequent = pr.subgoals.head
      if (logger.isDebugEnabled) logger.debug(
        "  US(" + fact.conclusion.prettyString + ")\n  unify: " + sequent + " matches against\n  form:  " + fact
          .conclusion + " ... checking"
      )
      // @todo is there a way of flagging a fact that comes from ProvableInfo with ProvableInfo.linear=true for faster LinearMatcher?
      // @note Probably not worth it, because all axiomatic rules in AxiomBase are nonlinear
      val subst = defaultMatcher(fact.conclusion, sequent)
      if (logger.isDebugEnabled) logger.debug(
        "  US(" + fact.conclusion.prettyString + ")\n  unify: " + sequent + " matches against\n  form:  " + fact
          .conclusion + " by " + subst
      )
      if (sequent != subst(fact.conclusion)) throw new UnsupportedTacticFeature(
        "unification computed an incorrect unifier\nunification should match:\n  unify: " + sequent + "\n  gives: " + subst(
          fact.conclusion
        ) + " when matching against\n  form:  " + fact.conclusion + "\n  by:    " + subst
      )
      pr(subst.toForward(fact), 0)
    }
  }

  // renaming

  /**
   * uniformRename(what,repl) renames `what` to `repl` uniformly and vice versa.
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.core.UniformRenaming]]
   */
  def uniformRename(what: Variable, repl: Variable): BuiltInTactic = ProofRuleTactics.uniformRenameFw(what, repl)

  /**
   * uniformRename(ur) renames `ur.what` to `ur.repl` uniformly and vice versa.
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.core.UniformRenaming]]
   */
  def uniformRename(ur: URename): BuiltInTactic = ProofRuleTactics.uniformRenameFw(ur.what, ur.repl)

  /**
   * boundRename(what,repl) renames `what` to `repl` at the indicated position (or vice versa).
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.core.BoundRenaming]]
   */
  def boundRename(what: Variable, repl: Variable): BuiltInPositionTactic = ProofRuleTactics.boundRenameFw(what, repl)

  /** @see [[US()]] */
  def uniformSubstitute(subst: USubst): InputTactic = inputanon { US(subst) }

  @Tactic(("US", "US"), codeName = "US", conclusion = "|- S(P)", premises = "|- P")
  def USX(S: List[SubstitutionPair]): InputTactic = inputanonP { (pr: ProvableSig) =>
    // add user-provided substitutions to the definitions
    US(USubst(S))(pr).reapply(pr.defs ++ Declaration.fromSubst(S, pr.defs))
  }

  private[btactics] def useAt(fact: ProvableSig, key: PosInExpr, inst: Option[Subst] => Subst): BuiltInPositionTactic =
    // @note linearity info no longer holds for nondefault key
    useAtImpl(TacticFactory.ANON, fact, key, defaultMatcher, inst)
  private[btactics] def useAt(fact: ProvableSig, key: PosInExpr): BuiltInPositionTactic = useAt(
    fact,
    key,
    (us: Option[Subst]) =>
      us.getOrElse(
        throw new InapplicableUnificationKeyFailure(
          "No substitution found by unification, fix given key " + key + " or try to patch locally with own substitution"
        )
      ),
  )
  private[btactics] def useAt(fact: ProvableSig): BuiltInPositionTactic = useAt(fact, PosInExpr(0 :: Nil))

  // main implementation

  private[this] def useAtImpl(
      fact: ProvableInfo,
      inst: Option[Subst] => Subst = us =>
        us.getOrElse(
          throw new InapplicableUnificationKeyFailure(
            "No substitution found by unification, fix axiom key or try to patch locally with own substitution"
          )
        ),
  ): BuiltInPositionTactic = fact match {
    case fact: AxiomInfo => useAtImpl(fact.codeName, fact.provable, fact.key, matcherFor(fact), inst)
    case _ => useAtImpl(fact.codeName, fact.provable, defaultPosition, defaultMatcher, inst)
  }

  private[this] def useAtWithImpl(
      fact: ProvableInfo,
      key: PosInExpr,
      inst: Option[Subst] => Subst = us =>
        us.getOrElse(
          throw new InapplicableUnificationKeyFailure(
            "No substitution found by unification, fix axiom key or try to patch locally with own substitution"
          )
        ),
  ): BuiltInPositionTactic = {
    // @note noncanonical position so fact.unifier has to be ignored
    useAtImpl(fact.codeName, fact.provable, key, defaultMatcher, inst)
  }

  /**
   * useAt(fact)(pos) uses the given fact at the given position in the sequent. Unifies the left or right part of fact
   * with what's found at sequent(pos) and use corresponding instance to make progress by reducing to the other side.
   * {{{
   *     G |- C{s(r)}, D
   *   ------------------ useAt(__l__<->r) if s=unify(c,l)
   *     G |- C{c}, D
   * }}}
   * and accordingly for implication facts that are `__l__->r` facts or conditional equivalences `p->(__l__<->r)` or
   * `p->(__l__->r)` facts and so on, where `__l__` indicates the key part of the fact. useAt automatically tries
   * proving the required assumptions/conditions of the fact it is using.
   *
   * Backward Tableaux-style proof analogue of [[useFor()]].
   *
   * Tactic specification:
   * {{{
   * useAt(fact)(p)(F) = {let (C,c)=F(p) in
   *   case c of {
   *     s=unify(fact.left,_) => CutRight(C(s(fact.right))(p) ; <(
   *       "use cut": skip
   *       "show cut": EquivifyRight(p.top) ; CoHide(p.top) ; CE(C(_)) ; fact
   *     )
   *     s=unify(fact.right,_) => accordingly with an extra commuteEquivRightT
   *   }
   * }
   * }}}
   *
   * @author
   *   Andre Platzer
   * @param codeName
   *   The unique alphanumeric identifier for this (derived) axiom use.
   * @param fact
   *   the fact to use to simplify at the indicated position of the sequent
   * @param key
   *   the part of the Formula fact to unify the indicated position of the sequent with
   * @param matcher
   *   which unifier to use.
   * @param inst
   *   Transformation for instantiating additional unmatched symbols that do not occur in fact(key). Defaults to
   *   identity transformation, i.e., no change in substitution found by unification. This transformation could also
   *   change the substitution if other cases than the most-general unifier are preferred.
   * @example
   *   {{{
   * useAt(Ax.choiceb, PosInExpr(0::Nil), byUS(Ax.composeb))
   *   }}}
   *   applied to the indicated `1::1::Nil` of
   *   {{{
   * [x:=1;][{x'=22}] [x:=2*x;++x:=0;]x>=0
   *   }}}
   *   turns it into
   *   {{{
   * [x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)
   *   }}}
   * @see
   *   [[useFor()]]
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.btactics]]
   * @todo
   *   could directly use prop rules instead of CE if key close to HereP if more efficient.
   */
  private[this] def useAtImpl(
      codeName: String,
      fact: ProvableSig,
      key: PosInExpr,
      matcher: Matcher,
      inst: Option[Subst] => Subst,
  ): BuiltInPositionTactic = {
    new BuiltInPositionTactic(codeName) {
      // @note performance impact
      import BelleExpr.RECHECK

      private val (keyCtx: Context[_], keyPart) = fact.conclusion.succ.head.at(key)

      private def checkSubst(matcher: Matcher, key: Expression, expr: Expression): Subst =
        matcher.unifiable(key, expr) match {
          case Some(us) => inst(Some(us))
          case None =>
            try { inst(None) }
            catch {
              case ex: InapplicableUnificationKeyFailure
                  if ex.getMessage == "No substitution found by unification, fix axiom key or try to patch locally with own substitution" =>
                throw new InapplicableUnificationKeyFailure(
                  "Axiom " + codeName + " " +
                    fact
                      .conclusion
                      .succ
                      .head
                      .prettyString + " cannot be applied: The shape of\n  expression               " +
                    expr.prettyString + "\n  does not match axiom key " + key.prettyString
                )
            }
        }

      override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
        val sequent = provable.subgoals.head
        val (ctx, expr) = sequent.at(pos)
        // unify keyPart against target expression by single-sided matching
        val subst =
          try { if (OPTIMIZE) checkSubst(matcher, keyPart, expr) else checkSubst(defaultMatcher, keyPart, expr) }
          catch {
            case ex: InapplicableUnificationKeyFailure => throw ex.inContext(
                "useAt(" + fact
                  .prettyString + ")\n  unify:   " + expr + "\tat " + pos + "\n  against: " + keyPart + "\tat " + key + "\n  of:      " + codeName + "\n  unsuccessful"
              )
          }
        if (this.logger.underlying.isDebugEnabled) this
          .logger
          .debug(
            "Doing a useAt(" + fact
              .prettyString + ")\n  unify:   " + expr + "\tat " + pos + "\n  against: " + keyPart + "\tat " + key + "\n  by:      " + subst
          )
        Predef.assert(
          !RECHECK || expr == subst(keyPart),
          "unification matched left successfully\n  unify:   " + expr + "\n  against: " + keyPart + "\n  by:      " + subst + "\n  gave:    " + subst(
            keyPart
          ) + "\n  that is: " + keyPart + " instantiated by " + subst,
        )
        // val keyCtxMatched = Context(subst(keyCtx.ctx))
        useAt(subst, keyCtx, keyPart, pos, ctx, expr, provable)
      }

      /**
       * useAt(K{k})(C{c}) uses, already under the given substitution subst, the key k from context K{k} in place of c
       * at position p in context C{_}.
       *
       * Direct congruential equivalence [[CE]] will be used for facts of the form
       * {{{
       *   left<->right
       * }}}
       * For conditional equivalence facts of the form
       * {{{
       *   prereq -> (left<->right)
       * }}}
       * this tactic will try only QE to prove `prereq` globally and will leave `C{prereq}` as an open goal otherwise.
       *
       * @param subst
       *   the substitution `subst=unify(k,c)`
       * @param K
       *   the context of fact in which key k occurs
       * @param k
       *   the key from context K{_} to use in place of c
       * @param p
       *   the position in `sequent` at which this useAt is applied.
       * @param C
       *   the context C{_} around the position p at which K{k} will be used
       * @param c
       *   the formula c at position p in context C{_} to be replaced by subst(k)
       * @param sequent
       *   the sequent in which this useAt happens.
       * @tparam T
       *   the type of the whole `k` in the context `K`
       * @return
       *   The tactic using key `k` of `fact` `K{k}` as a replacement for `c` at position `p` so in context `C{_}`.
       * @requires
       *   `C{c}.at(p.inExpr) == (C,c)`
       * @requires
       *   `subst(k) == c`
       * @author
       *   Andre Platzer
       * @note
       *   The implementation could be generalized because it sometimes fires irrelevant substitution clashes coming
       *   merely from the context embedding contracts.
       */
      private def useAt[T <: Expression](
          subst: Subst,
          K: Context[T],
          k: T,
          p: Position,
          C: Context[Formula],
          c: Expression,
          provable: ProvableSig,
      ): ProvableSig = {
        require(
          !RECHECK || subst(k) == c,
          "correctly matched input expected, but got " + subst(k).prettyString + " != " + c.prettyString,
        )
        // @note might cause some irrelevant clashes
        require(
          C(c).at(p.inExpr) == (C, c),
          "correctly split at position " + p
            .inExpr + "\ngiving context " + C + "\nsubexpression " + c + "\nreassembling to the same " + C(c),
        )
        // @todo generalization of DotTerm to other types should be acceptable, too
        require(
          List((C, DotFormula), (C, DotTerm())).contains(C.ctx.at(p.inExpr)),
          "correctly split at position " + p
            .inExpr + "\ngiving context " + C + "\nsubexpression " + c + "\nreassembling to the same " + C(
            c
          ) + "\nwith context at position " + p.inExpr + " having placeholder " + C.ctx.at(p.inExpr),
        )
        require(provable.subgoals.length == 1, "sole subgoal expected, but got " + provable.prettyString)

        val sequent = provable.subgoals.head

        /** Equivalence rewriting step using given `fact` to replace with substituted form of `other` */
        def equivStep(leftKey: Boolean, other: Expression, fact: ProvableSig): ProvableSig = {
          // The position at which the cut show formula will land depending on the side of cutLR
          val cutPos: SuccPos = p match {
            case p: SuccPosition => p.top
            case _: AntePosition => SuccPos(sequent.succ.length)
          }
          // @note ctx(fml) is meant to put fml in for DotTerm in ctx, i.e apply the corresponding USubst.
          // @note cut instead of cutLR might be a quicker proof to avoid the equivify but changes positions which would be unfortunate. Alleviated by CEimp/CErevimp
          // @todo would already know that ctx is the right context to use and subst(left)<->subst(right) is what we need to prove next, which results by US from left<->right
          // @todo optimizable equivalenceCongruenceT by a direct CE call using context ctx
          (provable(cutLRFw(C(subst(other))).computeResult(_, p.top), 0)(CoHideRight(cutPos), 1)(
            if (other.kind == FormulaKind)
              if (leftKey == p.isAnte) CEimpFw(p.inExpr).result _ else CErevimpFw(p.inExpr).result _
            else if (other.kind == TermKind)
              if (leftKey == p.isAnte) CQimpFw(p.inExpr).result _ else CQrevimpFw(p.inExpr).result _
            else throw new UnsupportedTacticFeature("Don't know how to handle kind " + other.kind + " of " + other),
            1,
          )(subst.toForward(fact), 1))
        }

        /** Implication rewriting step using [[CMon]] */
        def implyStep(other: Expression): ProvableSig = {
          // cohide to the position at which the cut show formula will land depending on the side of cutLR
          val cohide = p match {
            case p: SuccPosition => p.top
            case _: AntePosition => SuccPos(provable.subgoals.head.succ.length) // 'Rlast
          }
          (provable(cutLRFw(C(subst(other))).computeResult(_, p.topLevel), 0)(CoHideRight(cohide), 1)(
            CMonFw(p.inExpr).result _,
            1,
          )(subst.toForward(fact), 1))
        }

        K.ctx match {
          case DotFormula =>
            if (p.isTopLevel) { provable(subst.toForward(fact), 0) }
            else {
              // @todo if fact.isProved this could get faster with a derivedrule
              // |- fml
              // ---------------
              // |- fml<->true
              // @todo optimizable by proving this once and using it, although maybe the inline proof is fast anyhow
              val provedFact = (ProvableSig.startProof(Equiv(fact.conclusion.succ.head, True), fact.defs)(
                EquivRight(SuccPos(0)),
                0,
              )(CoHideRight(SuccPos(0)), 1)(fact, 1)(CloseTrue(SuccPos(0)), 0))
              equivStep(leftKey = true, True, provedFact)
            }

          case Equiv(DotFormula, other) => equivStep(leftKey = true, other, fact)

          case Equiv(other, DotFormula) => equivStep(leftKey = false, other, fact)

          case Equal(DotTerm(_, _), other) => equivStep(leftKey = true, other, fact)

          case Equal(other, DotTerm(_, _)) => equivStep(leftKey = false, other, fact)

          case Imply(other, DotFormula) => implyStep(other)

          case Imply(DotFormula, other) => implyStep(other)

          // @note all DotTerms are equal
          case Imply(prereq, remainder) =>
            if (StaticSemantics.signature(prereq).intersect(Set(DotFormula, DotTerm())).nonEmpty)
              throw new UnsupportedTacticFeature(
                "Unimplemented case which works at a negative polarity position: " + K.ctx
              )

            val rewrite = remainder match {
              case _: Equiv => Some((pos: AntePos) => equivRewriting(pos, p))
              case Equal(_: DotTerm, _) => Some((pos: AntePos) => EqualityTactics.eqL2R(pos.checkAnte)(p))
              case Equal(_, _: DotTerm) => Some((pos: AntePos) => EqualityTactics.eqR2L(pos.checkAnte)(p))
              case _ => None
            }

            val bv = StaticSemantics.boundVars(C(subst(k)))

            val sub = provable.sub(0)
            val lastSucc = SuccPos(sub.subgoals.head.succ.length)
            // @note don't call auto to avoid infinite proof search for ODEs
            lazy val prereqFact = Try(TactixLibrary.proveBy(subst(prereq), TactixLibrary.QE & done)).toOption
            lazy val prereqObligation = ProvableSig
              .startPlainProof(Sequent(sub.subgoals.head.ante, sub.subgoals.head.succ ++ IndexedSeq(subst(prereq))))
            lazy val prereqProof = prereqFact match {
              case Some(prf) => prereqObligation(CoHideRight(lastSucc), 0)(byUS(prf), 0)
              case _ => prereqObligation(prop, 0)
            }

            if (
              rewrite.nonEmpty &&
              bv.intersect(StaticSemantics.freeVars(subst(prereq))).isEmpty &&
              bv.intersect(StaticSemantics.freeVars(subst(k))).isEmpty &&
              prereqProof.isProved
            ) {
              // prereq can be proved from current assumptions without considering context, equivalence is unaffected by context

              val useEquivGoal = if (fact.isProved) 0 else 1

              val lastAnte = AntePos(sub.subgoals.head.ante.length)
              val lastSucc = SuccPos(sub.subgoals.head.succ.length)

              val rewritten = (sub(Cut(subst(fact.conclusion.succ.head)), 0)
              // show cut using fact
              (CoHideRight(lastSucc), 1)(subst.toForward(fact), 1)(
                ImplyLeft(lastAnte),
                0,
              ) // 0-th subgoal: G ==> D, prereq; last subgoal: G, k ==> D
              // G ==> D, prereq: show prereq from assumptions
              (prereqProof, 0)
              // G, k ==> D: rewrite equivalence
              (rewrite.get(lastAnte), useEquivGoal)(HideLeft(lastAnte), useEquivGoal))
              provable(rewritten, 0)
            } else
              try {
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

                // |- subst(prereq)
                require(
                  prereqFact.isDefined && prereqFact.get.isProved,
                  "only globally provable requirements currently supported. Ese useAt instead " + prereqFact,
                )

                // |- subst(remainder{k})
                val remFact: ProvableSig = (ProvableSig.startProof(subst(Context(remainder)(k)), provable.defs)
                // |- subst(prereq)      |- subst(prereq -> remainder)
                (CutRight(subst(prereq), SuccPos(0)), 0)
                // prove right branch   |- subst(prereq -> remainder)
                // right branch  |- subst(prereq -> remainder)  byUS(fact)
                (subst.toForward(fact), 1)
                // left branch   |- subst(prereq)
                (prereqFact.get, 0))
                remFact ensures (r => r.subgoals == fact.subgoals, "Proved / no new subgoals expected " + remFact)

                val remKey: PosInExpr = key.child
                require(
                  remFact.conclusion(SuccPos(0)).at(remKey)._2 == subst(keyPart),
                  "position guess within fact are usually expected to succeed " + remKey + " in\n" + remFact + "\nis remaining from " + key + " in\n" + fact,
                )
                UnifyUSCalculus.this
                  .useAtImpl("useAtRem", remFact, remKey, defaultMatcher, inst)(p)
                  .computeResult(provable)
              } catch {
                // @todo catch less
                case _: Throwable =>
                  // @todo if global proof of prereq is unsuccessful could also rewrite (DotFormula<->bla)<-prereq to prereq&bla -> DotFormula and use the latter.

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

                  val remR = sequent.sub(p).get.asInstanceOf[Formula]

                  // @todo assumes no more context around remainder (no other examples so far)
                  val (conclusion, equiv, commute, op) = remainder match {
                    case Equiv(DotFormula, other) => (other, Equiv(remR, other), p.isSucc, Equiv)
                    case Equiv(other, DotFormula) => (other, Equiv(other, remR), p.isAnte, Equiv)
                    case Imply(DotFormula, other) => (other, Imply(remR, other), p.isSucc, Imply)
                    case Imply(other, DotFormula) => (other, Imply(other, remR), p.isAnte, Imply)
                    //              case Equal(DotTerm, other) => (other, if (p.isSucc) TactixLibrary.useAt(DerivedAxioms.equalCommute)(1) else ident)
                    //              case Equal(other, DotTerm) => (other, if (p.isAnte) TactixLibrary.useAt(DerivedAxioms.equalCommute)(1) else ident)
                  }

                  val hide2Fw =
                    if (p.isSucc) (pr: ProvableSig) => pr(CoHide2(AntePos(sequent.ante.size), p.checkSucc.top), 0)
                    else (sequent.ante.indices.reverse.tail.map(i => HideLeft(AntePos(i))) ++
                      sequent.succ.indices.reverseIterator.map(i => HideRight(SuccPos(i))))
                      .foldLeft(_: ProvableSig)({ case (pr, rule) => pr(rule, 0) })

                  // uses specialized congruence tactic for DC, may not work with other conditional equivalences
                  (
                    provable(Cut(C(subst(prereq))), 0)
                    /* Show C(subst(prereq)): leave open: show prereq (@todo stripped down master might show) */
                    (if (p.isSucc) HideRight(p.checkSucc.top) else HideLeft(p.checkAnte.top), 1)
                    /* Use C(subst(prereq)): result remains open */
                    (cutAtFw(subst(conclusion)).computeResult(_, p), 0) // creates subgoals: 0+2
                    /* Use subst(conclusion) */
                    (HideLeft(AntePos(provable.subgoals.head.ante.length)), 0)
                    /* Show subst(conclusion) */
                    (hide2Fw, 2)(Cut(C(subst(equiv))), 2) // creates subgoals 2+3
                    /* Show C(subst(equiv)) */
                    (HideRight(SuccPos(0)), 3) /* hide C(r)->C(l) */
                    (implyRi.computeResult _, 3)(CMonFw(p.inExpr).result _, 3)(
                      ProvableSig.startProof(Imply(subst(prereq), subst(Context(remainder)(k))), fact.defs)(
                        subst.toForward(fact),
                        0,
                      ),
                      3,
                    )
                    /* Use C(subst(equiv)) */
                    (HideLeft(AntePos(0)), 2) /* hide C(prereq) */
                    (ImplyRight(SuccPos(0)), 2)(andLi.computeResult _, 2)(implyRi.computeResult _, 2)(
                      condEquivCongruence(C.ctx, p.inExpr, HereP, commute, op),
                      2,
                    )(CloseTrue(SuccPos(0)), 2)
                  )
              }

          case Forall(vars, remainder) => ???
          // useAt(subst, new Context(remainder), k, p, C, c, /*@todo instantiateQuanT(vars.head, subst(vars.head))(SuccPos(0))*/ ident, sequent)

          // @todo unfold box by step*
          case Box(a, remainder) => ???
        }
      }
    }
  }

  /* Specialized congruence reasoning for the questions arising in the axiomatic ODE solver DC step */
  private def condEquivCongruence(
      context: Formula,
      towards: PosInExpr,
      subPos: PosInExpr,
      commute: Boolean,
      op: (Formula, Formula) => Formula,
  ): ProvableSig => ProvableSig = (provable: ProvableSig) =>
    context match {
      case Box(_, p) if towards.head == 1 => (
        provable(useAt(Ax.boxAnd, PosInExpr(1 :: Nil))(1, subPos ++ 0).computeResult _, 0)(
          useAt(Ax.K, PosInExpr(1 :: Nil))(1, subPos).computeResult _,
          0,
        )(condEquivCongruence(p, towards.child, subPos ++ 1, commute, op), 0)(
          useAt(Ax.boxTrueTrue)(1, subPos).computeResult _,
          0,
        )
      )
      case Imply(_, p) if towards.head == 1 => (
        provable(useAt(Ax.impliesRightAnd)(1, subPos ++ 0).computeResult _, 0)(
          useAt(Ax.sameImpliesImplies)(1, subPos).computeResult _,
          0,
        )(condEquivCongruence(p, towards.child, subPos ++ 1, commute, op), 0)(
          useAt(Ax.implyTrue)(1, subPos).computeResult _,
          0,
        )
      )
      case And(p, _) if towards.head == 0 => (
        provable(useAt(Ax.factorAndRight)(1, subPos ++ 0).computeResult _, 0)(
          useAt(Ax.impliesMonAndLeft, PosInExpr(1 :: Nil))(1, subPos).computeResult _,
          0,
        )(condEquivCongruence(p, towards.child, subPos, commute, op), 0)
      )
      case And(_, p) if towards.head == 1 => (
        provable(useAt(Ax.factorAndLeft)(1, subPos ++ 0).computeResult _, 0)(
          useAt(Ax.impliesMonAndRight, PosInExpr(1 :: Nil))(1, subPos).computeResult _,
          0,
        )(condEquivCongruence(p, towards.child, subPos, commute, op), 0)
      )
      case Or(p, _) if towards.head == 0 => (
        provable(useAt(Ax.factorOrRight)(1, subPos ++ 0).computeResult _, 0)(
          useAt(Ax.factorImpliesOrRight)(1, subPos).computeResult _,
          0,
        )(condEquivCongruence(p, towards.child, subPos ++ 0, commute, op), 0)(
          useAt(Ax.trueOr)(1, subPos).computeResult _,
          0,
        )
      )
      case Or(_, p) if towards.head == 1 => (
        provable(useAt(Ax.factorOrLeft)(1, subPos ++ 0).computeResult _, 0)(
          useAt(Ax.factorImpliesOrLeft)(1, subPos).computeResult _,
          0,
        )(condEquivCongruence(p, towards.child, subPos ++ 1, commute, op), 0)(
          useAt(Ax.orTrue)(1, subPos).computeResult _,
          0,
        )
      )
      case Forall(x, p) if towards.head == 0 => (
        provable(useAt(Ax.randomb, PosInExpr(1 :: Nil))(1, subPos ++ 0 ++ 0).computeResult _, 0)(
          useAt(Ax.randomb, PosInExpr(1 :: Nil))(1, subPos ++ 0 ++ 1).computeResult _,
          0,
        )(useAt(Ax.randomb, PosInExpr(1 :: Nil))(1, subPos ++ 1).computeResult _, 0)(
          condEquivCongruence(Box(AssignAny(x.head), p), PosInExpr(towards.pos.updated(0, 1)), subPos, commute, op),
          0,
        )
      )
      case DotFormula =>
        val ponensAndPassThrough = op match {
          case Equiv => if (commute) Ax.ponensAndPassthrough_coEquiv else Ax.ponensAndPassthrough_Equiv
          case Imply => if (commute) Ax.ponensAndPassthrough_coImply else Ax.ponensAndPassthrough_Imply
        }
        provable(useAt(ponensAndPassThrough)(1, subPos).computeResult _, 0)
    }

  // Let auto-tactics

  /**
   * Let(abbr, value, inner) alias `let abbr=value in inner` abbreviates `value` by `abbr` in the provable and proceeds
   * with an internal proof by tactic `inner`, resuming to the outer proof by a uniform substitution of `value` for
   * `abbr` of the resulting provable.
   */
  def let(abbr: Expression, value: Expression, inner: BelleExpr): BelleExpr = Let(abbr, value, inner)

  /* ******************************************************************
   * Congruence Reasoning
     *******************************************************************/

  /**
   * CQ(pos) at the indicated position within an equivalence reduces contextual equivalence `p(left)<->p(right)` to
   * argument equality `left=right`. This tactic will use [[CEat()]] under the hood as needed.
   * {{{
   *        f(x) = g(x)
   *   --------------------- CQ
   *    c(f(x)) <-> c(g(x))
   * }}}
   *
   * @param inEqPos
   *   the position *within* the two sides of the equivalence at which the context DotTerm happens.
   * @see
   *   [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   */
  @Tactic(premises = "e=k", conclusion = "c(e)↔c(k)")
  def CQ(inEqPos: PosInExpr): InputTactic = inputanon { CQFw(inEqPos) }

  /** Builtin forward implementation of CQ. */
  private[btactics] def CQFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    val f_ = UnitFunctional("f_", AnyArg, Real)
    val g_ = UnitFunctional("g_", AnyArg, Real)
    val c_ = PredOf(Function("ctx_", None, Real, Bool), DotTerm())
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent, but got " + sequent,
    )
    sequent.succ.head match {
      case Equiv(p, q) =>
        val (ctxF, f) = p.at(inEqPos)
        val (ctxG, g) = q.at(inEqPos)
        require(ctxF == ctxG, "Same context expected, but got contexts " + ctxF + " and " + ctxG)
        Predef.assert(ctxF.ctx == ctxG.ctx, "Same context formulas expected, but got " + ctxF.ctx + " and " + ctxG.ctx)
        Predef.assert(ctxF.isTermContext, "Formula context expected for CQ")
        if (logger.isDebugEnabled) logger.debug(
          "CQ: boundAt(" + ctxF
            .ctx + "," + inEqPos + ")=" + boundAt(ctxF.ctx, inEqPos) + " intersecting FV(" + f + ")=" + freeVars(
            f
          ) + "\\/FV(" + g + ")=" + freeVars(g) + " i.e. " + (freeVars(f) ++ freeVars(g)) + "\nIntersect: " + boundAt(
            ctxF.ctx,
            inEqPos,
          ).intersect(freeVars(f) ++ freeVars(g))
        )
        if (boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f) ++ freeVars(g)).isEmpty) {
          val subst =
            USubst(SubstitutionPair(c_, ctxF.ctx) :: SubstitutionPair(f_, f) :: SubstitutionPair(g_, g) :: Nil)
          provable(Ax.CQrule.provable(subst), 0)
        } else {
          if (logger.isDebugEnabled) logger.debug("CQ: Split " + p + " around " + inEqPos)
          val (fmlPos, termPos): (PosInExpr, PosInExpr) = Context.splitPos(p, inEqPos)
          if (logger.isDebugEnabled) logger.debug(
            "CQ: Split " + p + " around " + inEqPos + "\ninto " + fmlPos + " and " + termPos + "\n  as " + p
              .at(fmlPos)
              ._1 + " and " + Context.at(p.at(fmlPos)._2, termPos)._1
          )
          if (p.at(fmlPos)._2.isInstanceOf[Modal]) logger.warn(">>CE TACTIC MAY PRODUCE INFINITE LOOP<<")
          if (fmlPos == HereP)
            throw new InfiniteTacticLoopError("CQ split void, would cause infinite loop unless stopped")
          // @todo could optimize to build directly since ctx already known
          (provable(CEFw(fmlPos).result _, 0)(CQFw(termPos).result _, 0))
        }
      case fml => throw new TacticInapplicableFailure("Expected equivalence, but got " + fml)
    }
  }

  /**
   * CQimply(pos) at the indicated position within an equivalence reduces contextual implication `p(left)->p(right)` to
   * argument equality `left=right`. This tactic will use [[CEat()]] under the hood as needed.
   * {{{
   *        f(x) = g(x)
   *   --------------------- CQ
   *    c(f(x)) -> c(g(x))
   * }}}
   *
   * @param inEqPos
   *   the position *within* the two sides of the equivalence at which the context DotTerm happens.
   * @see
   *   [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   */
  @Tactic(premises = "e=k", conclusion = "c(e)→c(k)")
  def CQimp(inEqPos: PosInExpr): InputTactic = inputanon { CQimpFw(inEqPos) }

  /** Builtin forward implementation of CQimp. */
  private[btactics] def CQimpFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    val f_ = UnitFunctional("f_", AnyArg, Real)
    val g_ = UnitFunctional("g_", AnyArg, Real)
    val c_ = PredOf(Function("ctx_", None, Real, Bool), DotTerm())
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(p, q) =>
        val (ctxF, f) = p.at(inEqPos)
        val (ctxG, g) = q.at(inEqPos)
        require(ctxF == ctxG, "Same context expected, but got contexts " + ctxF + " and " + ctxG)
        Predef.assert(ctxF.ctx == ctxG.ctx, "Same context formulas expected, but got " + ctxF.ctx + " and " + ctxG.ctx)
        Predef.assert(ctxF.isTermContext, "Formula context expected for CQ")
        if (logger.isDebugEnabled) logger.debug(
          "CQ: boundAt(" + ctxF
            .ctx + "," + inEqPos + ")=" + boundAt(ctxF.ctx, inEqPos) + " intersecting FV(" + f + ")=" + freeVars(
            f
          ) + "\\/FV(" + g + ")=" + freeVars(g) + " i.e. " + (freeVars(f) ++ freeVars(g)) + "\nIntersect: " + boundAt(
            ctxF.ctx,
            inEqPos,
          ).intersect(freeVars(f) ++ freeVars(g))
        )
        // @todo this would be too permissive due to lack of special permission for CQimplyCongruence: if (boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f)++freeVars(g)).isEmpty)
        if (StaticSemantics.vars(ctxF.ctx).isEmpty) {
          val subst =
            USubst(SubstitutionPair(c_, ctxF.ctx) :: SubstitutionPair(f_, f) :: SubstitutionPair(g_, g) :: Nil)
          provable(Ax.CQimplyCongruence.provable(subst), 0)
        } else {
          if (logger.isDebugEnabled) logger.debug("CQ: Split " + p + " around " + inEqPos)
          val (fmlPos, termPos): (PosInExpr, PosInExpr) = Context.splitPos(p, inEqPos)
          if (logger.isDebugEnabled) logger.debug(
            "CQ: Split " + p + " around " + inEqPos + "\ninto " + fmlPos + " and " + termPos + "\n  as " + p
              .at(fmlPos)
              ._1 + " and " + Context.at(p.at(fmlPos)._2, termPos)._1
          )
          // if (p.at(fmlPos)._2.isInstanceOf[Modal]) logger.warn(">>CE TACTIC MAY PRODUCE INFINITE LOOP<<")
          // if (fmlPos == HereP) throw new InfiniteTacticLoopError("CQ split void, would cause infinite loop unless stopped")
          // @todo could optimize to build directly since ctx already known
          (provable(CEimpFw(fmlPos).result _, 0)(CQFw(termPos).result _, 0))
        }
      case fml => throw new TacticInapplicableFailure("Expected equivalence, but got " + fml)
    }
  }

  /**
   * CQrevimp(pos) at the indicated position within an equivalence reduces contextual implication `p(left)->p(right)` to
   * argument equality `left=right`. This tactic will use [[CEat()]] under the hood as needed.
   * {{{
   *        g(x) = f(x)
   *   --------------------- CQ
   *    c(f(x)) -> c(g(x))
   * }}}
   *
   * @param inEqPos
   *   the position *within* the two sides of the equivalence at which the context DotTerm happens.
   * @see
   *   [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   */
  @Tactic(premises = "k=e", conclusion = "c(e)→c(k)")
  def CQrevimp(inEqPos: PosInExpr): InputTactic = inputanon { CQrevimpFw(inEqPos) }

  /** Builtin forward implementation of CQrevimp. */
  private[btactics] def CQrevimpFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    val f_ = UnitFunctional("f_", AnyArg, Real)
    val g_ = UnitFunctional("g_", AnyArg, Real)
    val c_ = PredOf(Function("ctx_", None, Real, Bool), DotTerm())
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(p, q) =>
        //          println("CQr: " + Ax.CQrevimplyCongruence + "\n" + Ax.CQrevimplyCongruence.provable + "\nfor: " + Imply(p,q))
        val (ctxF, f) = p.at(inEqPos)
        val (ctxG, g) = q.at(inEqPos)
        require(ctxF == ctxG, "Same context expected, but got contexts " + ctxF + " and " + ctxG)
        Predef.assert(ctxF.ctx == ctxG.ctx, "Same context formulas expected, but got " + ctxF.ctx + " and " + ctxG.ctx)
        Predef.assert(ctxF.isTermContext, "Formula context expected for CQ")
        if (logger.isDebugEnabled) logger.debug(
          "CQ: boundAt(" + ctxF
            .ctx + "," + inEqPos + ")=" + boundAt(ctxF.ctx, inEqPos) + " intersecting FV(" + f + ")=" + freeVars(
            f
          ) + "\\/FV(" + g + ")=" + freeVars(g) + " i.e. " + (freeVars(f) ++ freeVars(g)) + "\nIntersect: " + boundAt(
            ctxF.ctx,
            inEqPos,
          ).intersect(freeVars(f) ++ freeVars(g))
        )
        // @todo this would be too permissive due to lack of special permission for CQimplyCongruence: if (boundAt(ctxF.ctx, inEqPos).intersect(freeVars(f)++freeVars(g)).isEmpty)
        if (StaticSemantics.vars(ctxF.ctx).isEmpty) {
          val subst =
            USubst(SubstitutionPair(c_, ctxF.ctx) :: SubstitutionPair(f_, f) :: SubstitutionPair(g_, g) :: Nil)
          provable(Ax.CQrevimplyCongruence.provable(subst), 0)
        } else {
          if (logger.isDebugEnabled) logger.debug("CQ: Split " + p + " around " + inEqPos)
          val (fmlPos, termPos): (PosInExpr, PosInExpr) = Context.splitPos(p, inEqPos)
          if (logger.isDebugEnabled) logger.debug(
            "CQ: Split " + p + " around " + inEqPos + "\ninto " + fmlPos + " and " + termPos + "\n  as " + p
              .at(fmlPos)
              ._1 + " and " + Context.at(p.at(fmlPos)._2, termPos)._1
          )
          // if (p.at(fmlPos)._2.isInstanceOf[Modal]) logger.warn(">>CE TACTIC MAY PRODUCE INFINITE LOOP<<")
          // if (fmlPos == HereP) throw new InfiniteTacticLoopError("CQ split void, would cause infinite loop unless stopped")
          // @todo could optimize to build directly since ctx already known
          (provable(CErevimpFw(fmlPos).result _, 0)(CQFw(termPos).result _, 0))
        }
      case fml => throw new TacticInapplicableFailure("Expected equivalence, but got " + fml)
    }
  }

  /**
   * CE(pos) at the indicated position within an equivalence reduces contextual equivalence `C{left}<->C{right}`to
   * argument equivalence `left<->right`.
   * {{{
   *       p(x) <-> q(x)
   *   --------------------- CE
   *    C{p(x)} <-> C{q(x)}
   * }}}
   * Part of the differential dynamic logic Hilbert calculus.
   *
   * @param inEqPos
   *   the position *within* the two sides of the equivalence at which the context DotFormula occurs.
   * @see
   *   [[UnifyUSCalculus.CE(Context)]]
   * @see
   *   [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CEat(Provable)]]
   * @see
   *   Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].
   *   In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
   *   Germany, Proceedings, LNCS. Springer, 2015.
   *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
   */
  @Tactic(premises = "P↔Q", conclusion = "C{P}↔C{Q}", codeName = "CECongruence")
  def CE(inEqPos: PosInExpr): InputTactic = inputanon { CEFw(inEqPos) }

  /** Builtin forward implementation of CE. */
  private[btactics] def CEFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    val p_ = UnitPredicational("p_", AnyArg)
    val q_ = UnitPredicational("q_", AnyArg)
    val c_ = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent formula, but got " + sequent,
    )
    sequent.succ.head match {
      case Equiv(l, r) =>
        if (inEqPos == HereP) provable
        else {
          val (ctxP, p) = l.at(inEqPos)
          val (ctxQ, q) = r.at(inEqPos)
          // @note Could skip the construction of ctxQ but it's part of the .at construction anyways.
          require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
          Predef.assert(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
          Predef.assert(ctxP.isFormulaContext, "Formula context expected for CE")
          val subst =
            USubst(SubstitutionPair(c_, ctxP.ctx) :: SubstitutionPair(p_, p) :: SubstitutionPair(q_, q) :: Nil)
          provable(Ax.CErule.provable(subst), 0)
        }
      case fml => throw new TacticInapplicableFailure("Expected equivalence, but got " + fml)
    }
  }

  /**
   * CEimply(pos) at the indicated position within an equivalence reduces contextual implication `C{left}->C{right}`to
   * argument equivalence `left<->right`.
   * {{{
   *       p(x) <-> q(x)
   *   --------------------- CE
   *    C{p(x)} -> C{q(x)}
   * }}}
   * Part of the differential dynamic logic Hilbert calculus.
   *
   * @param inEqPos
   *   the position *within* the two sides of the equivalence at which the context DotFormula occurs.
   * @see
   *   [[UnifyUSCalculus.CE(Context)]]
   * @see
   *   Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].
   *   In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
   *   Germany, Proceedings, LNCS. Springer, 2015.
   *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
   */
  @Tactic(premises = "P↔Q", conclusion = "C{P}→C{Q}")
  def CEimp(inEqPos: PosInExpr): InputTactic = inputanon { CEimpFw(inEqPos) }

  /** Builtin forward implementation of CEimp. */
  private[btactics] def CEimpFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    val p_ = UnitPredicational("p_", AnyArg)
    val q_ = UnitPredicational("q_", AnyArg)
    val c_ = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent formula, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(l, r) =>
        if (inEqPos == HereP) equivifyR(1).computeResult(provable)
        else {
          val (ctxP, p) = l.at(inEqPos)
          val (ctxQ, q) = r.at(inEqPos)
          // @note Could skip the construction of ctxQ but it's part of the .at construction anyways.
          require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
          Predef.assert(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
          Predef.assert(ctxP.isFormulaContext, "Formula context expected for CE")
          val subst =
            USubst(SubstitutionPair(c_, ctxP.ctx) :: SubstitutionPair(p_, p) :: SubstitutionPair(q_, q) :: Nil)
          provable(Ax.CEimplyCongruence.provable(subst), 0)
        }
      case fml => throw new TacticInapplicableFailure("Expected implication, but got " + fml)
    }
  }

  /**
   * CErevimply(pos) at the indicated position within an equivalence reduces contextual implication
   * `C{left}->C{right}`to argument equivalence `left<->right`.
   * {{{
   *       q(x) <-> p(x)
   *   --------------------- CE
   *    C{p(x)} -> C{q(x)}
   * }}}
   * Part of the differential dynamic logic Hilbert calculus.
   *
   * @param inEqPos
   *   the position *within* the two sides of the equivalence at which the context DotFormula occurs.
   * @see
   *   [[UnifyUSCalculus.CE(Context)]]
   * @see
   *   Andre Platzer.
   *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].
   *   In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
   *   Germany, Proceedings, LNCS. Springer, 2015.
   *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
   */
  @Tactic(premises = "Q↔P", conclusion = "C{P}→C{Q}")
  def CErevimp(inEqPos: PosInExpr): InputTactic = inputanon { CErevimpFw(inEqPos) }

  /** Builtin forward implementation of CErevimp. */
  private[btactics] def CErevimpFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    val p_ = UnitPredicational("p_", AnyArg)
    val q_ = UnitPredicational("q_", AnyArg)
    val c_ = PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula)
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)

    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent formula, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(l, r) =>
        //          println("NOW: " + Ax.CErevimplyCongruence + "\n" + Ax.CErevimplyCongruence.provable + "\nfor: " + Imply(l,r))
        if (inEqPos == HereP) commuteEquivR(1).computeResult(equivifyR(1).computeResult(provable))
        else {
          val (ctxP, p) = l.at(inEqPos)
          val (ctxQ, q) = r.at(inEqPos)
          // @note Could skip the construction of ctxQ but it's part of the .at construction anyways.
          require(ctxP == ctxQ, "Same context expected, but got " + ctxP + " and " + ctxQ)
          Predef.assert(ctxP.ctx == ctxQ.ctx, "Same context formula expected, but got " + ctxP.ctx + " and " + ctxQ.ctx)
          Predef.assert(ctxP.isFormulaContext, "Formula context expected for CE")
          val subst =
            USubst(SubstitutionPair(c_, ctxP.ctx) :: SubstitutionPair(p_, p) :: SubstitutionPair(q_, q) :: Nil)
          provable(Ax.CErevimplyCongruence.provable(subst), 0)
        }
      case fml => throw new TacticInapplicableFailure("Expected implication, but got " + fml)
    }
  }

  /* ******************************************************************
   * Contextual Monotonicity by directed analogy to Congruence
     *******************************************************************/

  /**
   * CMon(pos) at the indicated position within an implication reduces contextual implication `C{o}->C{k}` to argument
   * implication `o->k` for positive C. Contextual monotonicity proof rule.
   * {{{
   *   |- o -> k
   *   ------------------------- for positive C{.}
   *   |- C{o} -> C{k}
   * }}}
   * {{{
   *   |- k -> o
   *   ------------------------- for negative C{.}
   *   |- C{o} -> C{k}
   * }}}
   *
   * @param inEqPos
   *   the position *within* the two sides C{.} of the implication at which the context DotFormula happens.
   * @see
   *   [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(Context)]]
   * @see
   *   [[UnifyUSCalculus.CEat())]]
   * @see
   *   [[HilbertCalculus.monb]]
   * @see
   *   [[HilbertCalculus.mond]]
   */
  @Tactic(premises = "P→Q", conclusion = "C{P}→C{Q}", codeName = "CMonCongruence")
  def CMon(inEqPos: PosInExpr): InputTactic = inputanon { CMonFw(inEqPos) }

  /** Builtin forward implementation of CMon. */
  private[btactics] def CMonFw(inEqPos: PosInExpr): BuiltInTactic = anon { (provable: ProvableSig) =>
    require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)
    val sequent = provable.subgoals.head
    require(
      sequent.ante.isEmpty && sequent.succ.length == 1,
      "Expected empty antecedent and single succedent formula, but got " + sequent,
    )
    sequent.succ.head match {
      case Imply(l, r) =>
        if (inEqPos == HereP) provable
        else {
          val (ctxP, p: Formula) = l.at(inEqPos)
          val (ctxQ, q: Formula) = r.at(inEqPos)
          require(ctxP == ctxQ, "Contexts must be equal, but " + ctxP + " != " + ctxQ)
          if (FormulaTools.polarityAt(l, inEqPos) < 0) implyR(SuccPos(0)).computeResult(provable)(
            CMon(ctxP)(ProvableSig.startProof(Sequent(IndexedSeq(q), IndexedSeq(p)), provable.defs)),
            0,
          )(inverseImplyR(ProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq(Imply(q, p))), provable.defs)), 0)
          else implyR(SuccPos(0)).computeResult(provable)(
            CMon(ctxP)(ProvableSig.startProof(Sequent(IndexedSeq(p), IndexedSeq(q)), provable.defs)),
            0,
          )(inverseImplyR(ProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq(Imply(p, q))), provable.defs)), 0)
        }
    }
  }

  /**
   * Convenience CMon first hiding other context.
   * {{{
   *     |- o -> k
   *   ------------------------- for positive C{.}
   *   G |- C{o} -> C{k}, D
   * }}}
   * {{{
   *     |- k -> o
   *   ------------------------- for negative C{.}
   *   G |- C{o} -> C{k}, D
   * }}}
   * @see
   *   [[CMon()]]
   */
  @Tactic(premises = "P→Q", conclusion = "C{P}→C{Q}")
  def CMon: BuiltInRightTactic = anon { (provable: ProvableSig, pos: SuccPosition) =>
    // require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
    (provable(CoHideRight(pos.top), 0)(CMonFw(PosInExpr(pos.inExpr.pos.tail)).result _, 0))
  }
//  def CMon: DependentPositionTactic = new DependentPositionTactic("CMon") {
//    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
//      override def computeExpr(sequent: Sequent): BelleExpr = {
//        require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
//        require(pos.isSucc, "Expected CMon in succedent, but got position " + pos.prettyString)
//        cohideR(pos.top) & CMon(PosInExpr(pos.inExpr.pos.tail))
//      }
//    }
//  }

  /**
   * CEat(fact) uses the equivalence `left<->right` or equality `left=right` or implication `left->right` fact for
   * congruence reasoning at the indicated position to replace `right` by `left` at indicated position (literally, no
   * substitution). Efficient unification-free version of [[UnifyUSCalculus#useAt(Provable, PosInExpr):PositionTactic]]
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
   * @see
   *   [[UnifyUSCalculus.CEat(Provable,Context)]]
   * @see
   *   [[useAtImpl()]]
   * @see
   *   [[CE(Context)]]
   * @see
   *   [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   * @example
   *   `CEat(fact)` is equivalent to `CEat(fact, Context("⎵".asFormula))`
   * @todo
   *   Optimization: Would direct propositional rules make CEat faster at pos.isTopLevel?
   */
  //  @Tactic(premises = "Γ |- C{Q}, Δ ;; Q↔P",
  //    conclusion = "Γ |- C{P}, Δ")
  def CEat(fact: ProvableSig): BuiltInPositionTactic = {
    require(
      fact.conclusion.ante.isEmpty && fact.conclusion.succ.length == 1,
      "expected equivalence shape without antecedent and exactly one succedent " + fact,
    )
    def splitFact: (Expression, Expression, ProvableSig => ProvableSig, PosInExpr => BuiltInTactic) =
      fact.conclusion.succ.head match {
        case Equal(l, r) => (l, r, equivifyR(SuccPos(0)).computeResult, CQFw)
        case Equiv(l, r) => (l, r, equivifyR(SuccPos(0)).computeResult, CEFw)
        case Imply(l, r) => (l, r, ident.result, CMonFw)
        case _ => throw new UnsupportedTacticFeature("CE expects equivalence or equality or implication fact " + fact)
      }
    val (otherInit, keyInit, equivify, tactic) = splitFact
    anon { (provable: ProvableSig, pos: Position) =>
      {
        val sequent = provable.subgoals.head
        // todo: Should this be TacticFailure or Illformed?
        // Case for Illformed: user should not be applying tactics in sequents where positions don't exist
        // Case for TacticFailure: some automation might need to do that
        if (sequent.sub(pos).isEmpty) throw new IllFormedTacticApplicationException(
          "In-applicable CE(" + fact + ")\nat " + pos +
            "which is <ill-positioned>\n at " + sequent
        )

        val (other, key) = {
          if (fact.conclusion.succ.head.isInstanceOf[Imply]) {
            // The polarity of the sub position within the top level formula
            val polarity = FormulaTools.polarityAt(sequent.sub(pos.top).get.asInstanceOf[Formula], pos.inExpr)
            // polarity really shouldn't end up being 0 here..
            if (pos.isAnte && polarity < 0 || pos.isSucc && polarity > 0) (otherInit, keyInit) // positive polarity
            else (keyInit, otherInit) // negative
          } else (otherInit, keyInit)
        }
        require(
          sequent.sub(pos).contains(key),
          "In-applicable CE(" + fact + ")\nat " + pos + " which is " + sequent
            .sub(pos)
            .getOrElse("<ill-positioned>") + "\nat " + sequent,
        )
        val (ctx, _) = sequent.at(pos)
        val (cutPos: SuccPos, commute: (ProvableSig => ProvableSig)) = pos match {
          case p: SuccPosition => (p.top, ident.result _)
          case _: AntePosition => (
              SuccPos(sequent.succ.length),
              fact.conclusion.succ.head match {
                case _: Equal => commuteEqual(1).computeResult _
                case _: Equiv => commuteEquivR(1).computeResult _
                case _ => ident.result _
              },
            )
        }
        val ctxOther = if (!LIBERAL) ctx(other) else sequent.replaceAt(pos, other)
        (provable(cutLRFw(ctxOther)(pos.top).computeResult _, 0)(CoHideRight(cutPos), 1)(equivify, 1)(
          tactic(pos.inExpr).result _,
          1,
        )(commute, 1)(fact, 1))
      }
    }
  }

  /** CEat replacing `key` with the other expression in the equality/equivalence. @see [[CEat(ProvableSig)]] */
  def CEat(fact: ProvableSig, key: PosInExpr): BuiltInPositionTactic = {
    require(
      fact.conclusion.ante.isEmpty && fact.conclusion.succ.length == 1,
      "expected equivalence shape without antecedent and exactly one succedent " + fact,
    )
    key.pos match {
      case 0 :: Nil => fact.conclusion.succ.head match {
          case Equiv(l, r) =>
            CEat(ProvableSig.startProof(Equiv(r, l), fact.defs)(commuteEquivR(SuccPos(0)), 0)(fact, 0))
          case Equal(l, r) => CEat(ProvableSig.startProof(Equal(r, l), fact.defs)(commuteEqual(SuccPos(0)), 0)(fact, 0))
          case p => throw new InputFormatFailure("fact must be either equality or equivalence, but got " + p)
        }
      case 1 :: Nil => CEat(fact)
      case _ => throw new InputFormatFailure("key must be either .0 or .1, but got " + key.prettyString)
    }
  }

  /**
   * CEat(fact,C) uses the equivalence `left<->right` or equality `left=right` or implication `left->right` fact for
   * congruence reasoning in the given context C at the indicated position to replace `right` by `left` in that context
   * (literally, no substitution).
   *
   * @see
   *   [[UnifyUSCalculus.CEat(Provable)]]
   * @see
   *   [[useAtImpl()]]
   * @see
   *   [[CE(Context)]]
   * @see
   *   [[UnifyUSCalculus.CE(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CQ(PosInExpr)]]
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   * @example
   *   `CE(fact, Context("⎵".asFormula))` is equivalent to `CE(fact)`.
   * @example
   *   `CE(fact, Context("x>0&⎵".asFormula))(p)` is equivalent to `CE(fact)(p+PosInExpr(1::Nil))`. Except that the
   *   former has the shape `x>0&⎵` for the context starting from position `p`.
   */
  def CEat(fact: ProvableSig, C: Context[Formula]): DependentPositionTactic =
    new DependentPositionTactic("CE(Provable,Context)") {
      require(
        fact.conclusion.ante.isEmpty && fact.conclusion.succ.length == 1,
        "expected equivalence shape without antecedent and exactly one succedent " + fact,
      )

      def splitFact: (Expression, Expression, BelleExpr, (Context[Formula] => ForwardTactic)) =
        fact.conclusion.succ.head match {
          case Equal(l, r) => (l, r, equivifyR(SuccPos(0)), CE) // @note this CE can also use CQ
          case Equiv(l, r) => (l, r, equivifyR(SuccPos(0)), CE)
          case Imply(l, r) => (l, r, implyR(1), ((c: Context[Formula]) => inverseImplyR.andThen(CMon(c))))
          case _ => throw new UnsupportedTacticFeature("CE expects equivalence or equality or implication fact " + fact)
        }
      val (otherInit, keyInit, equivify, tactic) = splitFact

      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {

          // todo: See above
          if (sequent.sub(pos).isEmpty) throw new IllFormedTacticApplicationException(
            "In-applicable CE(" + fact + ")\nat " + pos +
              "which is <ill-positioned>\n at " + sequent
          )

          val (posctx, c) = sequent.at(pos)
          val ctx = posctx(C) // The combined context at the position

          val (other, key) = {
            if (fact.conclusion.succ.head.isInstanceOf[Imply]) {
              // Polarity of the combined context
              val polarity = FormulaTools.polarityAt(
                ctx.ctx,
                FormulaTools
                  .posOf(ctx.ctx, DotFormula)
                  .getOrElse(throw new TacticAssertionError(s"Context should contain DotFormula, but is ${C.ctx}")),
              )
              // polarity really shouldn't end up being 0 here..
              if (pos.isAnte && polarity < 0 || pos.isSucc && polarity > 0) (otherInit, keyInit) // positive polarity
              else (keyInit, otherInit) // negative
            } else (otherInit, keyInit)
          }

          require(
            sequent.sub(pos).contains(C(key)),
            "In-applicable CE(" + fact + ",\n" + C + ")\nat " + pos + "\nwhich is " + sequent
              .sub(pos)
              .getOrElse("none") + "\nat " + sequent,
          )

          val (cutPos: SuccPos, commute: BelleExpr) = pos match {
            case p: SuccPosition => (p.top, ident)
            case p: AntePosition => (
                SuccPos(sequent.succ.length),
                fact.conclusion.succ.head match {
                  case _: Equal => commuteEqual(1)
                  case _: Equiv => commuteEquivR(1)
                  case _ => ident
                },
              )
          }
          cutLR(ctx(other))(pos.top) < (
            /* use */ ident,
            /* show */ cohideR(cutPos) & // assertT(0,1) &
              equivify & /*commuteEquivR(SuccPosition(0)) &*/
              commute &
              by(tactic(ctx)(fact))
          )
        }
      }
    }

  /**
   * cutAt(repl) cuts left/right to replace the expression at the indicated position in its context C{.} by `repl`.
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
   * @see
   *   [[UnifyUSCalculus.CEat(Provable)]]
   */
  @Tactic(premises = "Γ |- C{repl}, Δ ;; Γ |- C{repl}→C{c}, Δ", conclusion = "Γ |- C{c}, Δ")
  def cutAt(repl: Expression): DependentPositionWithAppliedInputTactic = inputanon { (pos: Position) =>
    cutAtFw(repl)(pos)
  }

  /** Builtin forward implementation of cutAt. */
  private[btactics] def cutAtFw(repl: Expression): BuiltInPositionTactic =
    anon { (provable: ProvableSig, pos: Position) =>
      require(provable.subgoals.size == 1, "Sole subgoal expected, but got " + provable.prettyString)
      val seq = provable.subgoals.head
      require(seq.sub(pos).isDefined, "Position " + pos + " not defined in sequent " + seq)
      val (ctx, _) = seq.at(pos)
      cutLRFw(ctx(repl))(pos.top).computeResult(provable)
    }

  /* ******************************************************************
   * unification and matching based auto-tactics (forward Hilbert)
     *******************************************************************/

  /** Forward-style tactic mapping provables to provables that follow from it. */
  type ForwardTactic = (ProvableSig => ProvableSig)

  /** Forward-style position tactic mapping positions and provables to provables that follow from it. */
  type ForwardPositionTactic = (Position => ForwardTactic)
  // @todo add the following def &() for composition and def | as implicit definitions to ForwardTactic
  /** seqCompose(first,second) runs `first` followed by `second` (for forward tactics). */
  def seqCompose(first: ForwardTactic, second: ForwardTactic): ForwardTactic = first andThen second

  /** either(left,right) runs `left` if successful and `right` otherwise (for forward tactics). */
  def either(left: ForwardTactic, right: ForwardTactic): ForwardTactic = pr =>
    try { left(pr) }
    catch { case _: ProverException => right(pr) }

  /** ifThenElse(cond,thenT,elseT) runs `thenT` if `cond` holds and `elseT` otherwise (for forward tactics). */
  def ifThenElse(cond: ProvableSig => Boolean, thenT: ForwardTactic, elseT: ForwardTactic): ForwardTactic =
    pr => if (cond(pr)) thenT(pr) else elseT(pr)

  /** seqComposeP(first,second) runs `first` followed by `second` (for forward tactics). */
  def seqComposeP(first: ForwardPositionTactic, second: ForwardPositionTactic): ForwardPositionTactic =
    pos => seqCompose(first(pos), second(pos))

  /** eitherP(left,right) runs `left` if successful and `right` otherwise (for forward tactics). */
  def eitherP(left: ForwardPositionTactic, right: ForwardPositionTactic): ForwardPositionTactic =
    pos => either(left(pos), right(pos))

  /** ifThenElseP(cond,thenT,elseT) runs `thenT` if `cond` holds and `elseT` otherwise (for forward tactics). */
  def ifThenElseP(
      cond: Position => (ProvableSig => Boolean),
      thenT: ForwardPositionTactic,
      elseT: ForwardPositionTactic,
  ): ForwardPositionTactic = pos => ifThenElse(cond(pos), thenT(pos), elseT(pos))

  /** identity tactic skip that does not no anything (for forward tactics). */
  def iden: ForwardTactic = pr => pr

  /** uniformRenameF(what,repl) renames `what` to `repl` uniformly (for forward tactics). */
  def uniformRenameF(what: Variable, repl: Variable): ForwardTactic =
    pr => pr(UniformRenaming(what, repl)(pr.conclusion).head, UniformRenaming(what, repl))

  /** commuteEquivFR commutes the equivalence at the given position (for forward tactics). */
  def commuteEquivFR: ForwardPositionTactic = pos =>
    pr => pr(CommuteEquivRight(pos.checkSucc.checkTop)(pr.conclusion).head, CommuteEquivRight(pos.checkSucc.checkTop))

  /**
   * useFor(axiom) use the given (derived) axiom/axiomatic rule forward for the selected position in the given Provable
   * to conclude a new Provable
   */
  def useFor(axiom: ProvableInfo): ForwardPositionTactic = useForImpl(axiom)

  def useFor(axiom: ProvableInfo, key: PosInExpr): ForwardPositionTactic = useForWithImpl(axiom, key)

  /**
   * useFor(axiom, key) use the key part of the given axiom forward for the selected position in the given Provable to
   * conclude a new Provable
   */
  private[btactics] def useFor(axiom: Lemma, key: PosInExpr, inst: Subst => Subst): ForwardPositionTactic =
    useForImpl(axiom.fact, key, defaultMatcher, inst)

  /**
   * useFor(pi, key) use the key part of the given axiom or provable info forward for the selected position in the given
   * Provable to conclude a new Provable
   * @param key
   *   the optional position of the key in the axiom to unify with. Defaults to [[AxiomInfo.theKey]]
   * @param inst
   *   optional transformation augmenting or replacing the uniform substitutions after unification with additional
   *   information. Defaults to no change.
   */
  def useFor(pi: ProvableInfo, key: PosInExpr, inst: Subst => Subst): ForwardPositionTactic =
    useForWithImpl(pi, key, inst)
  def useFor(axiom: ProvableInfo, inst: Subst => Subst): ForwardPositionTactic = useForImpl(axiom, inst)

  /**
   * CE(C) will wrap any equivalence `left<->right` or equality `left=right` fact it gets within context C. Uses CE or
   * CQ as needed.
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
   * @see
   *   [[CE(PosInExpr]]
   * @see
   *   [[CEat(Provable)]]
   * @see
   *   [[CMon(Context)]]
   * @todo
   *   likewise for Context[Term] using CT instead.
   */
  def CE(C: Context[Formula]): ForwardTactic = equiv => {
    require(
      equiv.conclusion.ante.isEmpty && equiv.conclusion.succ.length == 1,
      "expected equivalence shape without antecedent and exactly one succedent " + equiv,
    )
    equiv.conclusion.succ.head match {
      case Equiv(left, right) =>
        require(C.isFormulaContext, "Formula context expected to make use of equivalences with CE " + C)
        equiv(ProvableSig.rules("CE congruence")(USubst(
          SubstitutionPair(PredicationalOf(Function("ctx_", None, Bool, Bool), DotFormula), C.ctx) ::
            SubstitutionPair(UnitPredicational("p_", AnyArg), left) ::
            SubstitutionPair(UnitPredicational("q_", AnyArg), right) ::
            Nil
        )))
      case Equal(left, right) =>
        require(C.isTermContext, "Term context expected to make use of equalities with CE " + C)
        equiv(ProvableSig.rules("CQ equation congruence")(USubst(
          SubstitutionPair(PredOf(Function("ctx_", None, Real, Bool), DotTerm()), C.ctx) ::
            SubstitutionPair(UnitFunctional("f_", AnyArg, Real), left) ::
            SubstitutionPair(UnitFunctional("g_", AnyArg, Real), right) ::
            Nil
        )))
      case _ => throw new TacticInapplicableFailure("expected equivalence or equality fact " + equiv.conclusion)
    }
  }

  /**
   * CMon(C) will wrap any implication `left->right` fact it gets within a (positive or negative) context C by
   * monotonicity.
   * {{{
   *      k |- o
   *   ------------ CMon if C{⎵} of positive polarity
   *   C{k} |- C{o}
   * }}}
   *
   * @note
   *   The direction in the conclusion switches for negative polarity C{⎵}
   * @author
   *   Andre Platzer
   * @author
   *   Stefan Mitsch
   * @see
   *   [[UnifyUSCalculus.CMon(PosInExpr)]]
   * @see
   *   [[CE(Context)]]
   */
  def CMon(C: Context[Formula]): ForwardTactic = impl => {
    import StaticSemantics.symbols
    require(
      impl.conclusion.ante.length == 1 && impl.conclusion.succ.length == 1,
      "expected equivalence shape with exactly one antecedent and exactly one succedent " + impl,
    )

    // global polarity switch for all cases, except Modal and Equiv, which modify this switch if necessary
    val polarity = FormulaTools.polarityAt(
      C.ctx,
      FormulaTools
        .posOf(C.ctx, DotFormula)
        .getOrElse(throw new TacticAssertionError(s"Context should contain DotFormula, but is ${C.ctx}")),
    )
    val (left, right) =
      if (polarity < 0) (impl.conclusion.succ.head, impl.conclusion.ante.head)
      else (impl.conclusion.ante.head, impl.conclusion.succ.head)

    require(C.isFormulaContext, "Formula context expected to make use of equivalences with CE " + C)
    if (logger.isDebugEnabled) logger.debug("CMon(" + C + ")" + "(" + impl + ")")

    /** Monotonicity rewriting step to replace occurrence of instance of k by instance of o in context */
    def monStep(C: Context[Formula], mon: ProvableSig): ProvableSig = {
      // @todo assert(mon.ante.head == C{left or right} && mon.succ.head == C{right or left})
      if (logger.isDebugEnabled)
        logger.debug("in monStep(" + C + ", " + mon + ")") // \nin CMon(" + C + ")" + "(" + impl + ")")

      val localPolarity = FormulaTools.polarityAt(
        C.ctx,
        FormulaTools
          .posOf(C.ctx, DotFormula)
          .getOrElse(throw new TacticAssertionError("Context should contain DotFormula")),
      )
      val (ante, succ) =
        if (polarity * localPolarity < 0 || (polarity == 0 && localPolarity < 0))
          (IndexedSeq(C(right)), IndexedSeq(C(left)))
        else (IndexedSeq(C(left)), IndexedSeq(C(right)))

      (
        // which context to use it in
        C.ctx match {
          case DotFormula => mon

          case And(e, c) if !symbols(e).contains(DotFormula) =>
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)(AndLeft(AntePos(0)), 0)(AndRight(SuccPos(0)), 0)(
              Close(AntePos(0), SuccPos(0)),
              0,
            )
            // right branch
            (CoHide2(AntePos(1), SuccPos(0)), 0))(monStep(Context(c), mon), 0)

          case And(c, e) if !symbols(e).contains(DotFormula) =>
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)(AndLeft(AntePos(0)), 0)(AndRight(SuccPos(0)), 0)(
              Close(AntePos(1), SuccPos(0)),
              1,
            )
            // left branch
            (CoHide2(AntePos(0), SuccPos(0)), 0))(monStep(Context(c), mon), 0)

          case Or(e, c) if !symbols(e).contains(DotFormula) =>
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)(OrRight(SuccPos(0)), 0)(OrLeft(AntePos(0)), 0)(
              Close(AntePos(0), SuccPos(0)),
              0,
            )
            // right branch
            (CoHide2(AntePos(0), SuccPos(1)), 0))(monStep(Context(c), mon), 0)

          case Or(c, e) if !symbols(e).contains(DotFormula) =>
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)(OrRight(SuccPos(0)), 0)(OrLeft(AntePos(0)), 0)(
              Close(AntePos(0), SuccPos(1)),
              1,
            )
            // right branch
            (CoHide2(AntePos(0), SuccPos(0)), 0))(monStep(Context(c), mon), 0)

          case Imply(e, c) if !symbols(e).contains(DotFormula) =>
            if (logger.isDebugEnabled) logger.debug(
              "CMon check case: " + C + " to prove " + Sequent(ante, succ) + "\nfrom " + mon +
                "\nnext step in context " + Context(
                  c
                ) + "\n having current polarity " + polarity + " and new polarity " + localPolarity
            )
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)
              // e->c{a} |- e->c{s}
              (ImplyRight(SuccPos(0)), 0)
              // e->c{a}, e |- c{s}
              (ImplyLeft(AntePos(0)), 0)
              // e |- c{s}, e    c{a}, e |- c{s}
              // left branch     e |- c{s}, e closes
              (Close(AntePos(0), SuccPos(1)), 0)
              // right branch    c{a}, e |- c{s}
              (HideLeft(AntePos(1)), 0) // @note was: (CoHide2(AntePos(1), SuccPos(0)), 0)
              // right branch  c{a} |- c{s}
            )(monStep(Context(c), mon), 0)

          case Imply(c, e) if !symbols(e).contains(DotFormula) =>
            if (logger.isDebugEnabled) logger.debug(
              "CMon check case: " + C + " to prove " + Sequent(ante, succ) + "\nfrom " + mon +
                "\nnext step in context " + Context(
                  c
                ) + "\n having current polarity " + polarity + " and new polarity " + localPolarity
            )
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)
              // c{a}->e |- c{s}->e
              (ImplyRight(SuccPos(0)), 0)
              // c{a}->e, c{s} |- e
              (ImplyLeft(AntePos(0)), 0)
              // c{s} |- e, c{a}    e, c{s} |- e
              // right branch       e, c{s} |- e
              (Close(AntePos(0), SuccPos(0)), 1) // @note was: AntePos(1) for ImplyLeftOld for some reason
              // left branch        c{s} |- e, c{a}
              (HideRight(SuccPos(0)), 0) // @note was: (CoHide2(AntePos(0), SuccPos(1)), 0)
            )(monStep(Context(c), mon), 0)

          case Equiv(e, c) if !symbols(e).contains(DotFormula) =>
            // @note fallback to implication
            // polarity(k)=-1, polarity(o)=+1
            // orient equivalence Equiv(c,e) such that polarity of k in that will be +1
            // and polarity of o in that will be -1
            val newPol = FormulaTools.polarityAt(
              Imply(c, e),
              FormulaTools
                .posOf(Imply(c, e), DotFormula)
                .getOrElse(throw new TacticAssertionError("Context should contain DotFormula")),
            )
            if (newPol < 0) {
              // polarity of k in (Context(Imply(c,e))(k) will be +1
              // polarity of o in (Context(Imply(c,e))(o) will be -1
              monStep(Context(Imply(c, e)), mon)
            } else if (newPol > 0) {
              Predef.assert(
                FormulaTools.polarityAt(
                  Imply(e, c),
                  FormulaTools
                    .posOf(Imply(e, c), DotFormula)
                    .getOrElse(throw new TacticAssertionError("Context should contain DotFormula")),
                ) < 0
              )
              // polarity of k in (Context(Imply(e,c))(k) will be +1
              // polarity of o in (Context(Imply(e,c))(o) will be -1
              monStep(Context(Imply(e, c)), mon)
            } else {
              Predef.assert(
                assertion = false,
                "polarity rotations should ultimately be nonzero except with too many nested equivalences " + C,
              ); ???
            }

          case Equiv(c, e) if !symbols(e).contains(DotFormula) =>
            // @note fallback to implication
            // polarity(k)=-1, polarity(o)=+1
            // orient equivalence Equiv(c,e) such that polarity of k in that will be +1
            // and polarity of o in that will be -1
            val newPol = FormulaTools.polarityAt(
              Imply(c, e),
              FormulaTools
                .posOf(Imply(c, e), DotFormula)
                .getOrElse(throw new TacticAssertionError("Context should contain DotFormula")),
            )
            if (newPol > 0) {
              // polarity of k in (Context(Imply(c,e))(k) will be +1
              // polarity of o in (Context(Imply(c,e))(o) will be -1
              monStep(Context(Imply(c, e)), mon)
            } else if (newPol < 0) {
              Predef.assert(
                FormulaTools.polarityAt(
                  Imply(e, c),
                  FormulaTools
                    .posOf(Imply(e, c), DotFormula)
                    .getOrElse(throw new TacticAssertionError("Context should contain DotFormula")),
                ) > 0
              )
              // polarity of k in (Context(Imply(e,c))(k) will be +1
              // polarity of o in (Context(Imply(e,c))(o) will be -1
              monStep(Context(Imply(e, c)), mon)
            } else {
              Predef.assert(
                assertion = false,
                "polarity rotations should ultimately be nonzero except with too many nested equivalences " + C,
              ); ???
            }

          case Equiv(e, c) =>
            Predef.assert(
              symbols(e).contains(DotFormula) || symbols(c).contains(DotFormula),
              "proper contexts have dots somewhere " + C,
            )
            throw new ProverException(
              "No monotone context for equivalences " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")"
            )

          case Box(a, c) if !symbols(a).contains(DotFormula) =>
            // @note rotate substitution into same order as current ante/succ
            val (bleft, bright) =
              if (polarity * localPolarity < 0 || (polarity == 0 && localPolarity < 0)) (right, left) else (left, right)
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)(
              Ax.monbaxiom
                .provable(USubst(
                  SubstitutionPair(ProgramConst("a_"), a)
                    :: SubstitutionPair(UnitPredicational("p_", AnyArg), Context(c)(bleft))
                    :: SubstitutionPair(UnitPredicational("q_", AnyArg), Context(c)(bright))
                    :: Nil
                )),
              0,
            ))(monStep(Context(c), mon), 0)

          case Diamond(a, c) if !symbols(a).contains(DotFormula) =>
            // @note rotate substitution into same order as current ante/succ
            val (dleft, dright) =
              if (polarity * localPolarity < 0 || (polarity == 0 && localPolarity < 0)) (right, left) else (left, right)
            (ProvableSig.startProof(Sequent(ante, succ), mon.defs)(
              ProvableSig.rules("<> monotone")(USubst(
                SubstitutionPair(ProgramConst("a_"), a)
                  :: SubstitutionPair(UnitPredicational("p_", AnyArg), Context(c)(dleft))
                  :: SubstitutionPair(UnitPredicational("q_", AnyArg), Context(c)(dright))
                  :: Nil
              )),
              0,
            ))(monStep(Context(c), mon), 0)

          case m: Modal if symbols(m.program).contains(DotFormula) =>
            // @todo implement good cases. For example nibble of assign on both sides. Or random. Or ....
            throw new ProverException(
              "No monotone context within programs " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")"
            )

          case Forall(vars, c) => // if !StaticSemantics.freeVars(subst(c)).symbols.intersect(vars.toSet).isEmpty =>
            // @todo optimizable by using HilbertCalculus.allG?
            require(vars.size == 1, "Universal quantifier must not be block quantifier")
            // @note would also work with all distribute and all generalization instead
            // @note would also work with Skolemize and all instantiate but disjointness is more painful
            val rename = (us: RenUSubst) =>
              (us match {
                case usB4URen: DirectUSubstAboveURen =>
                  // @note transpose substitution since subsequent renaming does the same
                  usB4URen.reapply(
                    us.usubst
                      .subsDefsInput
                      .map(sp =>
                        (
                          sp.what,
                          sp.repl match {
                            case t: Term => vars.head match {
                                case _: BaseVariable => t.replaceFree(vars.head, Variable("x_"))
                                case _: DifferentialSymbol =>
                                  t.replaceFree(vars.head, DifferentialSymbol(Variable("x_")))
                                case _ =>
                                  throw new ProverException("Only variables/differential symbols in block quantifier")
                              }
                            case f: Formula => vars.head match {
                                case _: BaseVariable => f.replaceAll(vars.head, Variable("x_"))
                                case _: DifferentialSymbol =>
                                  f.replaceAll(vars.head, DifferentialSymbol(Variable("x_")))
                                case _ =>
                                  throw new ProverException("Only variables/differential symbols in block quantifier")
                              }
                          },
                        )
                      )
                  )
                case usB4URen: FastUSubstAboveURen =>
                  // @note transpose substitution since subsequent renaming does the same
                  usB4URen.reapply(
                    us.usubst
                      .subsDefsInput
                      .map(sp =>
                        (
                          sp.what,
                          sp.repl match {
                            case t: Term => vars.head match {
                                case _: BaseVariable => t.replaceFree(vars.head, Variable("x_"))
                                case _: DifferentialSymbol =>
                                  t.replaceFree(vars.head, DifferentialSymbol(Variable("x_")))
                                case _ =>
                                  throw new ProverException("Only variables/differential symbols in block quantifier")
                              }
                            case f: Formula => vars.head match {
                                case _: BaseVariable => f.replaceAll(vars.head, Variable("x_"))
                                case _: DifferentialSymbol =>
                                  f.replaceAll(vars.head, DifferentialSymbol(Variable("x_")))
                                case _ =>
                                  throw new ProverException("Only variables/differential symbols in block quantifier")
                              }
                          },
                        )
                      )
                  )
                case _ => us
              }) ++ RenUSubst(vars.head match {
                case _: BaseVariable => Seq((Variable("x_"), vars.head))
                case DifferentialSymbol(v) => Seq((Variable("x_"), v))
                case _ => throw new ProverException("Only variables/differential symbols in block quantifier")
              })
            // NB: all eliminate axiom not implemented
            if (
              vars.forall({
                case _: DifferentialSymbol => false
                case _ => true
              })
            ) {
              useFor(Ax.alle, PosInExpr(1 :: Nil), rename)(AntePosition.base0(1 - 1))(monStep(Context(c), mon))(
                Sequent(ante, succ),
                Skolemize(SuccPos(0)),
              )
            } else {
              useFor(Ax.alleprime, PosInExpr(1 :: Nil), rename)(AntePosition.base0(1 - 1))(monStep(Context(c), mon))(
                Sequent(ante, succ),
                Skolemize(SuccPos(0)),
              )
            }

          /*case Forall(vars, c) if StaticSemantics.freeVars(subst(c)).symbols.intersect(vars.toSet).isEmpty =>
            useFor(DerivedAxioms.allV)(SuccPosition(0))(
              useFor(DerivedAxioms.allV)(AntePosition(0))(monStep(Context(c), mon))
            )*/

          case Exists(vars, c) =>
            require(vars.size == 1, "Existential quantifier must not be block quantifier")
            // @note would also work with exists distribute and exists generalization instead
            // @note would also work with Skolemize and all instantiate but disjointness is more painful
            val rename = (us: RenUSubst) =>
              (us match {
                case usB4URen: DirectUSubstAboveURen =>
                  // @note transpose substitution since subsequent renaming does the same
                  usB4URen.reapply(
                    us.usubst
                      .subsDefsInput
                      .map(sp =>
                        (
                          sp.what,
                          sp.repl match {
                            case t: Term => t.replaceFree(vars.head, Variable("x_"))
                            case f: Formula => f.replaceAll(vars.head, Variable("x_"))
                          },
                        )
                      )
                  )
                case usB4URen: FastUSubstAboveURen =>
                  // @note transpose substitution since subsequent renaming does the same
                  usB4URen.reapply(
                    us.usubst
                      .subsDefsInput
                      .map(sp =>
                        (
                          sp.what,
                          sp.repl match {
                            case t: Term => t.replaceFree(vars.head, Variable("x_"))
                            case f: Formula => f.replaceAll(vars.head, Variable("x_"))
                          },
                        )
                      )
                  )
                case _ => us
              }) ++ RenUSubst(Seq((Variable("x_"), vars.head)))
            useFor(Ax.existse, PosInExpr(0 :: Nil), rename)(SuccPosition(1))(monStep(Context(c), mon))(
              Sequent(ante, succ),
              Skolemize(AntePos(0)),
            )

          case Not(c) =>
            // @note no polarity switch necessary here, since global polarity switch at beginning of CMon
            (
              ProvableSig.startProof(Sequent(ante, succ), mon.defs)(NotLeft(AntePos(0)), 0)(NotRight(SuccPos(0)), 0)
            )(monStep(Context(c), mon), 0)

          case _ => throw new ProverException(
              "Not implemented for other cases yet " + C + "\nin CMon.monStep(" + C + ",\non " + mon + ")"
            )
        }
        // @todo ensures is not correct yet (needs to keep track of when to switch polarity)
//        ) ensures(r => {true || r.conclusion ==
//        (if (C.ctx == DotFormula && polarity < 0) Sequent(IndexedSeq(right), IndexedSeq(left))
//        else if (C.ctx == DotFormula && polarity >= 0) Sequent(IndexedSeq(left), IndexedSeq(right))
//        else if (polarity >= 0) Sequent(IndexedSeq(C(right)), IndexedSeq(C(left)))
//        else Sequent(IndexedSeq(C(left)), IndexedSeq(C(right))))}, "Expected conclusion " + "\nin CMon.monStep(" + C + ",\nwhich is " + (if (polarity < 0) C(right) + "/" + C(left) else C(left) + "/" + C(right)) + ",\non " + mon + ")"
      ) ensures (
        r =>
          !impl.isProved || r.isProved, "Proved if input fact proved" + "\nin CMon.monStep(" + C + ",\non " + mon + ")"
      )
    }
    monStep(C, impl)
  }

  // Forward axiom usage implementation

  /**
   * useFor(fact,key,inst) use the key part of the given fact forward for the selected position in the given Provable to
   * conclude a new Provable Forward Hilbert-style proof analogue of [[useAtImpl()]].
   * {{{
   *     G |- C{c}, D
   *   ------------------ useFor(__l__<->r) if s=unify(c,l)
   *     G |- C{s(r)}, D
   * }}}
   * and accordingly for facts that are `__l__->r` facts or conditional `p->(__l__<->r)` or `p->(__l__->r)` facts and so
   * on, where `__l__` indicates the key part of the fact. useAt automatically tries proving the required
   * assumptions/conditions of the fact it is using.
   *
   * For facts of the form
   * {{{
   *   prereq -> (left<->right)
   * }}}
   * this tactic currently only uses master to prove `prereq` globally and otherwise gives up.
   *
   * @author
   *   Andre Platzer
   * @param fact
   *   the Provable fact whose conclusion to use to simplify at the indicated position of the sequent
   * @param key
   *   the part of the fact's conclusion to unify the indicated position of the sequent with
   * @param inst
   *   Transformation for instantiating additional unmatched symbols that do not occur in `fact.conclusion(key)`.
   *   Defaults to identity transformation, i.e., no change in substitution found by unification. This transformation
   *   could also change the substitution if other cases than the most-general unifier are preferred.
   * @example
   *   {{{
   * useFor(Axiom.axiom(Ax.composeb), PosInExpr(0::Nil))
   *   }}}
   *   applied to the indicated `1::1::Nil` of
   *   {{{
   * [x:=1;][{x'=22}]__[x:=2*x;++x:=0;]x>=0__
   *   }}}
   *   turns it into
   *   {{{
   * [x:=1;][{x'=22}] ([x:=2*x;]x>=0 & [x:=0;]x>=0)
   *   }}}
   * @see
   *   [[useAtImpl()]]
   * @see
   *   [[edu.cmu.cs.ls.keymaerax.btactics]]
   */
  def useFor(fact: ProvableSig, key: PosInExpr, inst: Subst => Subst = (us => us)): ForwardPositionTactic =
    useForImpl(fact, key, defaultMatcher, inst)

  private def useForImpl(fact: ProvableInfo, inst: Subst => Subst = (us => us)): ForwardPositionTactic = {
    fact match {
      case fact: AxiomInfo => useForImpl(fact.provable, fact.key, matcherFor(fact), inst)
      case _ => useForImpl(fact.provable, defaultPosition, defaultMatcher, inst)
    }
  }

  private def useForWithImpl(
      fact: ProvableInfo,
      key: PosInExpr,
      inst: Subst => Subst = (us => us),
  ): ForwardPositionTactic = {
    // @note noncanonical position so fact.unifier has to be ignored
    useForImpl(fact.provable, key, defaultMatcher, inst)
  }

  private def useForImpl(
      fact: ProvableSig,
      key: PosInExpr,
      matcher: Matcher,
      inst: Subst => Subst,
  ): ForwardPositionTactic = {
    // split key into keyCtx{keyPart} = fact
    val (keyCtx: Context[_], keyPart) = fact.conclusion(SuccPos(0)).at(key)
    if (logger.isDebugEnabled) logger
      .debug("useFor(" + fact.conclusion + ") key: " + keyPart + " in key context: " + keyCtx)

    pos =>
      proof => {
        // split proof into ctx{expr} at pos
        val (ctx, expr) = proof.conclusion.at(pos)
        // instantiated unification of expr against keyPart
        val subst = if (OPTIMIZE) inst(matcher(keyPart, expr)) else inst(defaultMatcher(keyPart, expr))
        if (logger.isDebugEnabled) logger.debug(
          "useFor(" + fact.conclusion.prettyString + ") unify: " + expr + " matches against " + keyPart + " by " + subst
        )
        if (logger.isDebugEnabled) logger.debug("useFor(" + fact.conclusion + ") on " + proof)
        Predef.assert(
          expr == subst(keyPart),
          "unification matched key successfully:\nexpr     " + expr + "\nequals   " + subst(
            keyPart
          ) + "\nwhich is " + keyPart + "\ninstantiated by " + subst,
        )

        /**
         * useFor(subst, K,k, p, C,c)
         *
         * @param subst
         *   the substitution that unifies key k with occurrence c==subst(k).
         * @param K
         *   the context within which k occurs in fact.conclusion==K{k}
         * @param k
         *   the key
         * @param p
         *   the position at which occurrence c occurs in proof.conclusion
         * @param C
         *   the context within which occurrence c occurs in proof.conclusion(p.top)==C{c}
         * @param c
         *   the occurrence c at position p in proof.conclusion
         * @tparam T
         *   the type of the key
         * @return
         *   The Provable following from proof by using key k of fact at p in proof.conclusion
         * @see
         *   [[useFor()]]
         */
        def useFor[T <: Expression](
            subst: Subst,
            K: Context[T],
            k: T,
            p: Position,
            C: Context[Formula],
            c: Expression,
        ): ProvableSig = {
          Predef.assert(subst(k) == c, "correctly matched input")
          Predef.assert(fact.conclusion.succ.head == K(k), "correctly matched key in fact")
          Predef.assert(proof.conclusion(p.top) == C(c), "correctly matched occurrence in input proof")
          Predef.assert(C(c).at(p.inExpr) == (C, c), "correctly split at position p")
          Predef
            .assert(List((C, DotFormula), (C, DotTerm())).contains(C.ctx.at(p.inExpr)), "correctly split at position p")

          /**
           * Forward equivalence rewriting step to replace occurrence of instance of key `k` by instance of other `o` in
           * context
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
           *   Replacement expression
           */
          def equivStep(o: Expression): ProvableSig = {
            require(fact.isProved, "currently want proved facts as input only\n" + fact)
            require(proof.conclusion.updated(p.top, C(subst(k))) == proof.conclusion, "expected context split")
            // |- fact: k=o or k<->o, respectively; commute fact if key=1
            val sideUS: ProvableSig = fact.conclusion.succ.head match {
              case Equiv(l, r) =>
                if (key == PosInExpr(0 :: Nil)) subst.toForward(fact)
                else subst
                  .toForward(fact(Sequent(IndexedSeq(), IndexedSeq(Equiv(r, l))), CommuteEquivRight(SuccPos(0))))
              case _ => subst.toForward(fact) // @note not an equivalence axiom, cannot commute
            }

            // |- subst(fact): subst(k)=subst(o) or subst(k)<->subst(o) by US
            val sideCE: ProvableSig = CE(C)(sideUS)
            // @todo could shortcut proof by using "CO one-sided congruence" instead of CE
            // |- C{subst(k)} <-> C{subst(o)} by CQ or CE, respectively
            val sideImply: ProvableSig =
              if (pos.isSucc)
                sideCE(Sequent(IndexedSeq(), IndexedSeq(Imply(C(subst(k)), C(subst(o))))), EquivifyRight(SuccPos(0)))
              else sideCE(
                Sequent(IndexedSeq(), IndexedSeq(Equiv(C(subst(o)), C(subst(k))))),
                CommuteEquivRight(SuccPos(0)),
              )(Sequent(IndexedSeq(), IndexedSeq(Imply(C(subst(o)), C(subst(k))))), EquivifyRight(SuccPos(0)))
            // succ: |- C{subst(k)}  -> C{subst(other)} by EquivifyRight or
            // ante: |- C{subst(other)}  -> C{subst(k)} by CommuteEquivRight and EquivifyRight
            // assert(C(subst(k)) == expr, "matched expression expected")
            val coside: ProvableSig =
              if (pos.isSucc) sideImply(
                proof.conclusion.updated(p.top, Imply(C(subst(k)), C(subst(o)))),
                CoHideRight(p.top.asInstanceOf[SuccPos]),
              )
              else sideImply(
                Sequent(
                  proof.conclusion.ante.patch(p.index0, Nil, 1),
                  proof.conclusion.succ :+ Imply(C(subst(o)), C(subst(k))),
                ),
                CoHideRight(SuccPos(proof.conclusion.succ.size)),
              )
            // succ: G |- C{subst(k)}  -> C{subst(o)}, D by CoHideRight
            // ante: G |- D, C{subst(o)} -> C{subst(k)} by CoHideRight
            val proved = {
              ProvableSig.startProof(proof.conclusion.updated(p.top, C(subst(o))), proof.defs)(
                if (pos.isSucc) CutRight(C(subst(k)), p.top.asInstanceOf[SuccPos])
                else CutLeft(C(subst(k)), p.top.asInstanceOf[AntePos]),
                0,
              )(coside, 1)
            } ensures (
              r => r.conclusion == proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
            ) ensures (
              r => r.subgoals == List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved"
            )
            //                           *
            //                        ------
            // G |- C{subst(k)}, D    coside
            // ------------------------------ CutRight
            // G |- C{subst(o)}, D

            //                           *
            //                        ------
            // G, C{subst(k)} |- D    coside
            // ------------------------------ CutLeft
            // G, C{subst(o)} |- D
            proved(proof, 0)
          } ensures (
            r => r.conclusion == proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
          ) ensures (r => r.subgoals == proof.subgoals, "expected original premises")

          // in which context of the fact does the key occur
          K.ctx match {
            case Equal(DotTerm(_, _), o) => fact.conclusion.succ.head match {
                case Equal(l, r) =>
                  if (l == r) proof // @note shortcut for stutter/recursor axioms
                  else equivStep(o)
              }

            case Equal(o, DotTerm(_, _)) => fact.conclusion.succ.head match {
                case Equal(l, r) =>
                  if (l == r) proof // @note shortcut for stutter/recursor axioms
                  else equivStep(o)
              }

            case Equiv(DotFormula, o) => fact.conclusion.succ.head match {
                case Equiv(l, r) =>
                  if (l == r) proof // @note shortcut for stutter/recursor axioms
                  else equivStep(o)
              }

            case Equiv(o, DotFormula) => fact.conclusion.succ.head match {
                case Equiv(l, r) =>
                  if (l == r) proof // @note shortcut for stutter/recursor axioms
                  else equivStep(o)
              }

            case Imply(o, DotFormula) =>
              // |- o->k
              val deduct = inverseImplyR(fact)
              // o |- k
              val sideUS: ProvableSig = subst.toForward(deduct)
              // subst(o) |- subst(k) by US

              // @note align context with implication o -> _ to get correct case (_ -> o or o -> _ depending on polarity)
              val Cmon = C.ctx match {
                case Equiv(ctxL, ctxR) if symbols(ctxL).contains(DotFormula) => CMon(Context(Equiv(ctxR, ctxL)))(sideUS)
                case _ => CMon(C)(sideUS)
              }

              // C{subst(k)} |- C{subst(o)} for polarity < 0
              // C{subst(o)} |- C{subst(k)} for polarity > 0
              // Ci{subst(k)} |- Ci{subst(o)} for polarity = 0, where <-> in C are turned into -> in Ci
              // @note do not need to inverse polarity if pos.isAnte, because sideImply implicitly inverses polarity for
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
              val cutPos: SuccPos = pos match {
                case p: SuccPosition => p.top
                case p: AntePosition => SuccPos(proof.conclusion.succ.length)
              }
              val coside: ProvableSig = sideImply(
                if (pos.isSucc) proof.conclusion.updated(p.top, Imply(kk, oo))
                // @note drop p.top too and glue
                else Sequent(proof.conclusion.ante.patch(p.top.getIndex, Nil, 1), proof.conclusion.succ)
                  .glue(Sequent(IndexedSeq(), IndexedSeq(Imply(kk, oo)))),
                CoHideRight(cutPos),
              )
              // G |- C{subst(o)}  -> C{subst(k)}, D by CoHideRight
              val proved = {
                if (pos.isSucc)
                  // G |- C{subst(o)}, D by CutRight with coside
                  ProvableSig.startProof(proof.conclusion.updated(pos.top, oo), proof.defs)(
                    CutRight(kk, pos.top.asInstanceOf[SuccPos]),
                    0,
                  )(coside, 1)
                else
                  // C{subst(o)}, G |- D by CutLeft with coside
                  ProvableSig.startProof(proof.conclusion.updated(pos.top, kk), proof.defs)(
                    CutLeft(oo, pos.top.asInstanceOf[AntePos]),
                    0,
                  )(coside, 1)
              } /*ensures(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
                ) ensures(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")*/

              if (polarity == 0 && pos.isSucc) {
                val equivified = proved(
                  ProvableSig
                    .startProof(proved.subgoals.head, proved.defs)(EquivifyRight(pos.top.asInstanceOf[SuccPos]), 0),
                  0,
                )
                // @note equiv assumed to always be top-level, so looking at inExpr.head determines direction
                val commuted =
                  if (pos.inExpr.head == 1) equivified(CommuteEquivRight(pos.top.asInstanceOf[SuccPos]), 0)
                  else equivified
                commuted(proof, 0)
              } else if (polarity == 0 && pos.isAnte) { ??? }
              else proved(proof, 0)

            case Imply(DotFormula, o) =>
              // |- k->o
              val deduct = inverseImplyR(fact)
              // k |- o
              val sideUS: ProvableSig = subst.toForward(deduct)
              // subst(k) |- subst(o) by US

              // @note align context with implication _ -> o to get correct case (_ -> o or o -> _ depending on polarity)
              val Cmon = C.ctx match {
                case Equiv(ctxL, ctxR) if symbols(ctxR).contains(DotFormula) => CMon(Context(Equiv(ctxR, ctxL)))(sideUS)
                case _ => CMon(C)(sideUS)
              }

              // C{subst(o)} |- C{subst(k)} for polarity < 0
              // C{subst(k)} |- C{subst(o)} for polarity > 0
              // Ci{subst(o)} |- Ci{subst(k)} for polarity = 0, where <-> in C are turned into -> in Ci
              // @note do not need to inverse polarity if pos.isAnte, because sideImply implicitly inverses polarity for
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
              val cutPos: SuccPos = pos match {
                case p: SuccPosition => p.top
                case p: AntePosition => SuccPos(proof.conclusion.succ.length)
              }
              val coside: ProvableSig = sideImply(
                if (pos.isSucc) proof.conclusion.updated(p.top, impl)
                // @note drop p.top too and glue
                else Sequent(proof.conclusion.ante.patch(p.top.getIndex, Nil, 1), proof.conclusion.succ)
                  .glue(Sequent(IndexedSeq(), IndexedSeq(impl))),
                CoHideRight(cutPos),
              )

              val proved = {
                // G |- C{subst(k)}  -> C{subst(o)}, D by CoHideRight
                if (pos.isSucc)
                  // C{subst(k)}, G |- D by CutLeft with coside
                  ProvableSig.startProof(proof.conclusion.updated(pos.top, oo), proof.defs)(
                    CutRight(kk, pos.top.asInstanceOf[SuccPos]),
                    0,
                  )(coside, 1)
                else
                  // G |- C{subst(o)}, D by CutRight with coside
                  ProvableSig.startProof(proof.conclusion.updated(pos.top, kk), proof.defs)(
                    CutLeft(oo, pos.top.asInstanceOf[AntePos]),
                    0,
                  )(coside, 1)
              } /*ensures(r=>r.conclusion==proof.conclusion.updated(p.top, C(subst(o))), "prolonged conclusion"
              ) ensures(r=>r.subgoals==List(proof.conclusion.updated(p.top, C(subst(k)))), "expected premise if fact.isProved")*/

              if (polarity == 0 && pos.isSucc) {
                val equivified = proved(
                  ProvableSig
                    .startProof(proved.subgoals.head, proved.defs)(EquivifyRight(pos.top.asInstanceOf[SuccPos]), 0),
                  0,
                )
                // @note equiv assumed to always be top-level, so looking at inExpr.head determines direction
                val commuted =
                  if (pos.inExpr.head == 0) equivified(CommuteEquivRight(pos.top.asInstanceOf[SuccPos]), 0)
                  else equivified
                commuted(proof, 0)
              } else if (polarity == 0 && pos.isAnte) { ??? }
              else proved(proof, 0)

            case Imply(prereq, remainder) =>
              if (StaticSemantics.signature(prereq).intersect(Set(DotFormula, DotTerm())).nonEmpty)
                throw new UnsupportedTacticFeature(
                  "Unimplemented case which works at a negative polarity position: " + K.ctx
                )
              // try to prove prereq globally
              // @todo if that fails preserve context and fall back to CMon and C{prereq} -> ...
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
              val prereqFact = TactixLibrary.proveBy(
                subst(prereq),
                TactixLibrary.prop & done | TactixLibrary.QE & done | TactixLibrary.master() & done,
              )
              require(
                prereqFact.isProved,
                "only globally provable requirements currently supported. Use useAt instead " + prereqFact,
              )

              // |- subst(remainder{k})
              val remFact: ProvableSig = (ProvableSig.startProof(subst(Context(remainder)(k)), prereqFact.defs)
              // |- subst(prereq)      |- subst(prereq -> remainder)
              (CutRight(subst(prereq), SuccPos(0)), 0)
              // prove right branch   |- subst(prereq -> remainder)
              // right branch  |- subst(prereq -> remainder)  byUS(fact)
              (subst.toForward(fact), 1)
              // left branch   |- subst(prereq)
              (prereqFact, 0))
              remFact ensures (r => r.subgoals == fact.subgoals, "Proved / no new subgoals expected " + remFact)

              val remKey: PosInExpr = key.child
              require(
                remFact.conclusion(SuccPos(0)).at(remKey)._2 == subst(keyPart),
                "position guess within fact are usually expected to succeed " + remKey + " in\n" + remFact + "\nis remaining from " + key + " in\n" + fact,
              )
              UnifyUSCalculus.this.useFor(remFact, remKey, inst)(pos)(proof)

            case DotFormula =>
              throw new UnsupportedTacticFeature("Not implemented for other cases yet, see useAt: " + K)

            case _ => throw new UnsupportedTacticFeature("Not implemented for other cases yet, see useAt: " + K)
          }
        }

        val r = useFor(subst, keyCtx, keyPart, pos, ctx, expr)
        if (logger.isDebugEnabled) logger.debug("useFor(" + fact.conclusion + ") on " + proof + "\n ~~> " + r)
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
   * @see
   *   "Andre Platzer. Differential dynamic logic for hybrid systems. Journal of Automated Reasoning, 41(2), pages
   *   143-189, 2008. Lemma 7"
   */
  private def inverseImplyR: ForwardTactic = pr => {
    val pos = SuccPos(0)
    val last = AntePos(pr.conclusion.ante.length)
    val Imply(a, b) = pr.conclusion.succ.head
    (ProvableSig.startProof(pr.conclusion.updated(pos, b).glue(Sequent(IndexedSeq(a), IndexedSeq())), pr.defs)(
      CutRight(a, pos),
      0,
    )
    // left branch
    (Close(last, pos), 0)
    // right branch
    (HideLeft(last), 0))(pr, 0)
    /*(Provable.startProof(pr.conclusion.updated(pos, b).glue(Sequent(IndexedSeq(a), IndexedSeq())))
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

  /* ******************************************************************
   * Computation-based auto-tactics
     *******************************************************************/

  /**
   * Chases the expression at the indicated position forward until it is chased away or can't be chased further without
   * critical choices. Unlike [[TactixLibrary.chaseAt]] will not branch or use propositional rules, merely transform the
   * chosen formula in place.
   */
  @Tactic(longDisplayName = "Decompose")
  val chase: BuiltInPositionTactic = anon { chase(3, 3, AxIndex.axiomsFor(_: Expression)).computeResult _ }
  private[btactics] val chaseInfo: TacticInfo = TacticInfo("chase")

  /**
   * Chases the expression at the indicated position forward. Unlike [[chase]] descends into formulas and terms
   * exhaustively.
   */
  @Tactic(longDisplayName = "Deep Decompose")
  val deepChase: BuiltInPositionTactic = anon { (pr: ProvableSig, pos: Position) =>
    ProofRuleTactics.requireOneSubgoal(pr, "deepChase")
    val expanded = pr(TactixLibrary.expandAllDefsFw(Nil), 0)
    val chased = expanded(chase(3, 3, AxIndex.verboseAxiomsFor(_: Expression))(pos), 0)
    if (chased != expanded) chased else pr
  }

  private[btactics] val deepChaseInfo: TacticInfo = TacticInfo("deepChase")

  /**
   * Chase with bounded breadth and giveUp to stop.
   *
   * @param breadth
   *   how many alternative axioms to pursue locally, using the first applicable one. Equivalent to pruning keys so that
   *   all lists longer than giveUp are replaced by Nil, and then all lists are truncated beyond breadth.
   * @param giveUp
   *   how many alternatives are too much so that the chase stops without trying any for applicability. Equivalent to
   *   pruning keys so that all lists longer than giveUp are replaced by Nil.
   */
  def chase(breadth: Int, giveUp: Int): BuiltInPositionTactic = chase(breadth, giveUp, AxIndex.axiomsFor(_: Expression))
  def chase(breadth: Int, giveUp: Int, keys: Expression => List[ProvableInfo]): BuiltInPositionTactic =
    chase(breadth, giveUp, keys, (ax, pos) => pr => pr)
  def chase(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
  ): BuiltInPositionTactic = chaseI(breadth, giveUp, keys, modifier, ax => us => us)
  def chaseI(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      inst: ProvableInfo => (Subst => Subst),
  ): BuiltInPositionTactic = chaseI(breadth, giveUp, keys, (ax, pos) => pr => pr, inst)
  def chaseI(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
      inst: ProvableInfo => (Subst => Subst),
  ): BuiltInPositionTactic = chaseI(breadth, giveUp, keys, modifier, inst, AxIndex.axiomIndex)

  def chaseI(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
      inst: ProvableInfo => (Subst => Subst),
      index: ProvableInfo => (PosInExpr, List[PosInExpr]),
  ): BuiltInPositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chase(
      e =>
        keys(e) match {
          case l: List[ProvableInfo] if l.size > giveUp => Nil
          case l: List[ProvableInfo] => l.take(breadth)
        },
      modifier,
      inst,
      index,
    )
  }

  def chaseFor(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
  ): ForwardPositionTactic = chaseFor(breadth, giveUp, keys, modifier, ax => us => us)
  def chaseFor(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
      inst: ProvableInfo => (Subst => Subst),
  ): ForwardPositionTactic = chaseFor(breadth, giveUp, keys, modifier, inst, AxIndex.axiomIndex)
  def chaseFor(
      breadth: Int,
      giveUp: Int,
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
      inst: ProvableInfo => (Subst => Subst),
      index: ProvableInfo => (PosInExpr, List[PosInExpr]),
  ): ForwardPositionTactic = {
    require(breadth <= giveUp, "less breadth than giveup expected: " + breadth + "<=" + giveUp)
    chaseFor(
      e =>
        keys(e) match {
          case l: List[ProvableInfo] if l.size > giveUp => Nil
          case l: List[ProvableInfo] => l.take(breadth)
        },
      modifier,
      inst,
      index,
    )
  }

  // main implementation turning chase to chaseFor

  /**
   * chase: Chases the expression at the indicated position forward until it is chased away or can't be chased further
   * without critical choices.
   *
   * Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
   * Follows canonical axioms toward all their recursors while there is an applicable simplifier axiom according to
   * `keys`.
   *
   * @param keys
   *   maps expressions to a list of axiom names to be used for those expressions. First returned axioms will be favored
   *   (if applicable) over further axioms. Defaults to [[AxIndex.axiomFor()]].
   * @param modifier
   *   will be notified after successful uses of axiom at a position with the result of the use. The result of
   *   modifier(ax,pos)(step) will be used instead of step for each step of the chase. Defaults to identity
   *   transformation, i.e., no modification in found match.
   * @param inst
   *   Transformation for instantiating additional unmatched symbols that do not occur when using the given axiom _1.
   *   Defaults to identity transformation, i.e., no change in substitution found by unification. This transformation
   *   could also change the substitution if other cases than the most-general unifier are preferred.
   * @param index
   *   Provides recursors to continue chase after applying an axiom from `keys`. Defaults to [[AxIndex.axiomIndex]].
   * @note
   *   Chase is search-free and, thus, quite efficient. It directly follows the [[AxIndex axiom index]] information to
   *   compute follow-up positions for the chase.
   * @example
   *   When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+(x'*y+x*y')>=0
   * @example
   *   When applied at Nil, turns [?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into ((x>0->x+1>=1) & (x=0->1>=1))
   * @example
   *   When applied at 1::Nil, turns [{x'=22}][?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into [{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))
   * @author
   *   Andre Platzer
   * @see
   *   [[HilbertCalculus.derive]]
   * @see
   *   [[chaseFor()]]
   * @todo
   *   also implement a backwards chase in tableaux/sequent style based on useAt instead of useFor
   */
  // @todo change keys to Expression=>List[DerivationInfo]
  def chase(
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
      inst: ProvableInfo => (Subst => Subst) = ax => us => us,
      index: ProvableInfo => (PosInExpr, List[PosInExpr]) = AxIndex.axiomIndex,
  ): BuiltInPositionTactic = chaseFor2Back("chase", chaseFor(keys, modifier, inst, index))

  /**
   * Converts a forward chase tactic into a backwards chase by a single CEat.
   * @param name
   *   What name to give to the use of of this tactic.
   * @author
   *   Andre Platzer
   */
  private[this] def chaseFor2Back(name: String, forward: ForwardPositionTactic): BuiltInPositionTactic = {

    /** Construct a proof proving the answer of the chase of e, so proves e=chased(e) or e<->chased(e) */
    def chaseProof(e: Expression): ProvableSig = {
      // reflexive setup corresponds to no-progress chase
      val initial: ProvableSig = e match {
        case t: Term => // t=t
          Ax.equalReflexive
            .provable(USubst(SubstitutionPair(FuncOf(Function("s_", None, Unit, Real), Nothing), t) :: Nil))
        case f: Formula => // f<->f
          Ax.equivReflexive
            .provable(USubst(SubstitutionPair(PredOf(Function("p_", None, Unit, Bool), Nothing), f) :: Nil))
      }
      Predef.assert(
        initial.isProved && initial.conclusion.ante.isEmpty && initial.conclusion.succ.length == 1,
        "Proved reflexive start " + initial + " for " + e,
      )
      if (logger.isDebugEnabled) logger.debug("chase starts at " + initial)
      // @note start the chase on the left-hand side
      val r = forward(SuccPosition(1, 0 :: Nil))(initial)
      if (logger.isDebugEnabled) logger.debug("chase(" + e.prettyString + ") = ~~> " + r + " done")
      r
    } ensures (r => r.isProved, "chase remains proved: " + " final chase(" + e + ")")
    anon { (provable: ProvableSig, pos: Position) =>
      {
        val sequent = provable.subgoals.head
        if (sequent.sub(pos).isEmpty) throw new IllFormedTacticApplicationException(
          "ill-positioned " + pos + " in " + sequent + "\nin " +
            "chase\n(" + sequent + ")"
        )
        CEat(chaseProof(sequent.sub(pos).get))(pos).computeResult(provable)
      }
    }
  }
  // central chasing implementation

  /**
   * chaseFor: Chases the expression of Provables at given positions forward until it is chased away or can't be chased
   * further without critical choices.
   *
   * Chase the expression at the indicated position forward (Hilbert computation constructing the answer by proof).
   * Follows canonical axioms toward all their recursors while there is an applicable simplifier axiom according to
   * `keys`.
   *
   * @param keys
   *   maps expressions to a list of axioms/tactics to be used for those expressions. The first applicable axiom/tactic
   *   will be chosen. Defaults to [[AxIndex.axiomIndex]].
   * @param modifier
   *   will be notified after successful uses of axiom at a position with the result of the use. The result of
   *   modifier(ax,pos)(step) will be used instead of step for each step of the chase. Defaults to identity
   *   transformation, i.e., no modification in found match.
   * @param inst
   *   Transformation for instantiating additional unmatched symbols that do not occur when using the given axiom.
   *   Defaults to identity transformation, i.e., no change in substitution found by unification. This transformation
   *   could also change the substitution if other cases than the most-general unifier are preferred.
   * @param index
   *   The key and recursor information determining (as in [[AxiomInfo]])
   *   - `._1` which subexpression of the ProvableInfo to match against.
   *   - `._2` which resulting recursors to continue chasing after in the resulting expression. Defaults to
   *     [[AxIndex.axiomIndex]].
   * @note
   *   Chase is search-free and, thus, quite efficient. It directly follows the [[AxIndex.axiomIndex() axiom index]]
   *   information to compute follow-up positions for the chase.
   * @example
   *   When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+(x'*y+x*y')>=0
   * @example
   *   When applied at Nil, turns [?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into ((x>0->x+1>=1) & (x=0->1>=1))
   * @example
   *   When applied at 1::Nil, turns [{x'=22}][?x>0;x:=x+1;++?x=0;x:=1;]x>=1 into [{x'=22}]((x>0->x+1>=1) & (x=0->1>=1))
   * @author
   *   Andre Platzer
   * @see
   *   [[chase()]]
   * @see
   *   [[HilbertCalculus.derive]]
   */
  def chaseFor(
      keys: Expression => List[ProvableInfo],
      modifier: (ProvableInfo, Position) => ForwardTactic,
      inst: ProvableInfo => (Subst => Subst) = ax => us => us,
      index: ProvableInfo => (PosInExpr, List[PosInExpr]),
  ): ForwardPositionTactic = pos =>
    de => {

      /** Recursive chase implementation */
      def doChase(de: ProvableSig, pos: Position): ProvableSig = {
        if (logger.isDebugEnabled) logger.debug("chase(" + de.conclusion.sub(pos).get.prettyString + ")")
        // generic recursor
        keys(de.conclusion.sub(pos).get) match {
          case Nil =>
            if (logger.isDebugEnabled) logger.debug("no chase(" + de.conclusion.sub(pos).get.prettyString + ")")
            de
          /*throw new IllegalArgumentException("No axiomFor for: " + expr)*/
          case List(ax) =>
            val (key, recursor) = index(ax)
            try {
              val axUse = modifier(ax, pos)(useFor(ax, key, inst(ax))(pos)(de))
              recursor.foldLeft(axUse)((pf, cursor) => doChase(pf, pos ++ cursor))
            } catch {
              case e: ProverException => throw e.inContext(
                  "useFor(" + ax + ", " + key
                    .prettyString + ")\nin " + "chase(" + de.conclusion.sub(pos).get.prettyString + ")"
                )
            }
          // take the first axiom among breadth that works for one useFor step
          case l: List[ProvableInfo] =>
            // useFor the first applicable axiom if any, or None
            def firstAxUse: Option[(ProvableSig, List[PosInExpr])] = {
              for (ax <- l)
                try {
                  val (key, recursor) = index(ax)
                  return Some((modifier(ax, pos)(useFor(ax, key, inst(ax))(pos)(de)), recursor))
                } catch { case _: ProverException => /* ignore and try next */ }
              None
            }
            firstAxUse match {
              case None =>
                if (logger.isDebugEnabled) logger.debug("no chase(" + de.conclusion.sub(pos).get.prettyString + ")")
                de
              case Some((axUse, recursor)) => recursor.foldLeft(axUse)((pf, cursor) =>
                  // @note avoid infinite recursion on . recursor when earlier recursors don't make progress
                  if (cursor.pos.nonEmpty || pf != de) doChase(pf, pos ++ cursor) else pf
                )
            }
        }
      } ensures (
        r => r.subgoals == de.subgoals, "chase keeps subgoals unchanged: " + " final chase(" + de
          .conclusion
          .sub(pos)
          .get
          .prettyString + ")\nhad subgoals: " + de.subgoals
      )
      doChase(de, pos)
    }

  /**
   * chaseCustom: Unrestricted form of chase where AxiomIndex is not built in, i.e. it takes keys of the form Expression
   * \=> List[(Provable,PosInExpr, List[PosInExpr])] This allows customized rewriting using provables derived at runtime
   */
  def chaseCustom(keys: Expression => List[(ProvableSig, PosInExpr, List[PosInExpr])]): BuiltInPositionTactic =
    chaseFor2Back("chaseCustom", chaseCustomFor(keys))

  def chaseCustomFor(keys: Expression => List[(ProvableSig, PosInExpr, List[PosInExpr])]): ForwardPositionTactic =
    pos =>
      de => {

        /** Recursive chase implementation */
        def doChase(de: ProvableSig, pos: Position): ProvableSig = {
          if (logger.isDebugEnabled) logger.debug("chase(" + de.conclusion.sub(pos).get.prettyString + ")")
          // generic recursor
          keys(de.conclusion.sub(pos).get) match {
            case Nil =>
              if (logger.isDebugEnabled) logger.debug("no chase(" + de.conclusion.sub(pos).get.prettyString + ")")
              de
            // take the first axiom among breadth that works for one useFor step
            case l: List[(ProvableSig, PosInExpr, List[PosInExpr])] =>
              // useFor the first applicable axiom if any, or None
              def firstAxUse: Option[(ProvableSig, List[PosInExpr])] = {
                for ((ax, key, recursor) <- l)
                  try { return Some((useFor(ax, key)(pos)(de), recursor)) }
                  catch { case _: ProverException => /* ignore and try next */ }
                None
              }
              firstAxUse match {
                case None =>
                  if (logger.isDebugEnabled) logger.debug("no chase(" + de.conclusion.sub(pos).get.prettyString + ")")
                  de
                case Some((axUse, recursor)) => recursor.foldLeft(axUse)((pf, cursor) => doChase(pf, pos ++ cursor))
              }
          }
        } ensures (
          r => r.subgoals == de.subgoals, "chase keeps subgoals unchanged: " + " final chase(" + de
            .conclusion
            .sub(pos)
            .get
            .prettyString + ")\nhad subgoals: " + de.subgoals
        )
        doChase(de, pos)
      }

  /**
   * Which unification matcher to use for which [[ProvableInfo]]. [[AxiomInfo.unifier]] declaration will be consulted
   * from @[[edu.cmu.cs.ls.keymaerax.btactics.macros.Axiom]] declarations:
   *   - 'surjective: A formula is surjective iff rule US can instantiate it to any of its axiom schema instances, so
   *     those obtained by uniformly replacing program constant symbols by hybrid games and unit predicationals by
   *     formulas. If no arguments occur, so no function or predicate symbols or predicationals, then the axiom is
   *     surjective. UnitFunctional, UnitPredicational, ProgramConst etc. can still occur. Function or predicate symbols
   *     that occur in a context without any bound variables are exempt. For example [[Ax.testb]]. Using
   *     [[UniformMatcher]]
   *   - 'linear: No symbol can occur twice in the shape. If a symbol does occur twice, it is assumed that the identical
   *     match is found in all use cases, which is a strong assumption and can lead to unpredictable behavior otherwise.
   *     Using [[LinearMatcher]]
   *   - 'surjlinear: Both 'surject and 'linear Using [[UniformMatcher]] but [[LinearMatcher]] would be okay/
   *   - 'surjlinearpretend: An axiom that pretends to be surjective and linear even if it isn't necessarily so.
   *   - 'full: General unification [[UnificationMatch]] is the default fallback.
   * @see
   *   Andre Platzer.
   *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
   *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017. arXiv:1601.06183
   */
  private[keymaerax] def matcherFor(pi: ProvableInfo): Matcher = pi match {
    case ifo: AxiomInfo => ifo.unifier match {
        case Symbol("surjective") => UniformMatcher
        case Symbol("surjlinear") => UniformMatcher
        case Symbol("linear") => LinearMatcher
        case Symbol("surjlinearpretend") => UniformMatcher
        case _ => defaultMatcher
      }
    case _ => defaultMatcher
  }

}
