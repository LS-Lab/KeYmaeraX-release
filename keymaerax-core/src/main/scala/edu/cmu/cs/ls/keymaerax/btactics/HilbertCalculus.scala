/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._

import scala.collection.immutable._
import scala.language.postfixOps

/**
  * Hilbert Calculus for differential dynamic logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see [[HilbertCalculus]]
  */
object HilbertCalculus extends HilbertCalculus

/**
  * Hilbert Calculus for differential dynamic logic.
  *
  * Provides the axioms and axiomatic proof rules from Figure 2 and Figure 3 in:
  * Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
  * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
  * @see Andre Platzer. [[http://dx.doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
  * @see [[HilbertCalculus.stepAt()]]
  * @see [[HilbertCalculus.derive()]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.DerivedAxioms]]
  */
trait HilbertCalculus extends UnifyUSCalculus {
  import TacticFactory._

  /** True when insisting on internal useAt technology, false when more elaborate external tactic calls are used on demand. */
  private[btactics] val INTERNAL = false

  /**
    * Make the canonical simplifying proof step at the indicated position
    * except when a decision needs to be made (e.g. invariants for loops or for differential equations).
    * Using the canonical [[AxiomIndex]].
    * @author Andre Platzer
    * @note Efficient source-level indexing implementation.
    * @see [[AxiomIndex]]
    */
  val stepAt: DependentPositionTactic = stepAt(AxiomIndex.axiomFor)


  //
  // axiomatic rules
  //

  /** G: Gödel generalization rule reduces a proof of `|- [a]p(x)` to proving the postcondition `|- p(x)` in isolation.
    * {{{
    *     |- p(||)
    *   --------------- G
    *   G |- [a]p(||), D
    * }}}
    * The more flexible and more general rule [[monb]] with p(x)=True gives `G` using [[boxTrue]].
    * @note Unsound for hybrid games
    * @see [[monb]] with p(x)=True
    * @see [[boxTrue]]
    */
  val G            : DependentPositionTactic = "G" by ((pos:Position) =>
    SequentCalculus.cohideR(pos) & DLBySubst.G
    )

  /** allG: all generalization rule reduces a proof of `|- \forall x p(x)` to proving `|- p(x)` in isolation */
  lazy val allG               : BelleExpr         = ??? //AxiomaticRuleTactics.forallGeneralizationT
  /** monb: Monotone `[a]p(x) |- [a]q(x)` reduces to proving `p(x) |- q(x)` */
  lazy val monb               : BelleExpr         = byUS("[] monotone")
  /** mond: Monotone `⟨a⟩p(x) |- ⟨a⟩q(x)` reduces to proving `p(x) |- q(x)` */
  lazy val mond               : BelleExpr         = byUS("<> monotone")

  //
  // axioms
  //

  //
  //box modality
  //

  /** diamond: <.> reduce double-negated box `![a]!p(x)` to a diamond `⟨a⟩p(x)`. */
  lazy val diamond            : DependentPositionTactic = useAt("<> diamond")
  /** assignb: [:=] simplify assignment `[x:=f;]p(x)` by substitution `p(f)` or equation.
    * Box assignment by substitution assignment [v:=t();]p(v) <-> p(t()) (preferred),
    * or by equality assignment [x:=f();]p(||) <-> \forall x (x=f() -> p(||)) as a fallback.
    * Universal quantifiers are skolemized if applied at top-level in the succedent; they remain unhandled in the
    * antecedent and in non-top-level context.
    * @example{{{
    *    |- 1>0
    *    --------------------assignb(1)
    *    |- [x:=1;]x>0
    * }}}
    * @example{{{
    *           1>0 |-
    *    --------------------assignb(-1)
    *    [x:=1;]x>0 |-
    * }}}
    * @example{{{
    *    x_0=1 |- [{x_0:=x_0+1;}*]x_0>0
    *    ----------------------------------assignb(1)
    *          |- [x:=1;][{x:=x+1;}*]x>0
    * }}}
    * @example{{{
    *    \\forall x_0 (x_0=1 -> [{x_0:=x_0+1;}*]x_0>0) |-
    *    -------------------------------------------------assignb(-1)
    *                           [x:=1;][{x:=x+1;}*]x>0 |-
    * }}}
    * @example{{{
    *    |- [y:=2;]\\forall x_0 (x_0=1 -> x_0=1 -> [{x_0:=x_0+1;}*]x_0>0)
    *    -----------------------------------------------------------------assignb(1, 1::Nil)
    *    |- [y:=2;][x:=1;][{x:=x+1;}*]x>0
    * }}}
    * @see [[DLBySubst.assignEquality]] */
  lazy val assignb            : DependentPositionTactic = "assignb" by { (pos:Position) =>
    if (INTERNAL) useAt("[:=] assign")(pos) | useAt("[:=] assign equality")(pos) /*| useAt("[:=] assign update")(pos)*/
    else useAt("[:=] assign")(pos) | useAt("[:=] self assign")(pos) | DLBySubst.assignEquality(pos)
  }

  /** randomb: [:*] simplify nondeterministic assignment `[x:=*;]p(x)` to a universal quantifier `\forall x p(x)` */
  lazy val randomb            : DependentPositionTactic = useAt("[:*] assign nondet")
  /** testb: [?] simplifies test `[?q;]p` to an implication `q->p` */
  lazy val testb              : DependentPositionTactic = useAt("[?] test")
  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)` */
  //def diffSolve               : DependentPositionTactic = ???
  /** choiceb: [++] handles both cases of a nondeterministic choice `[a++b]p(x)` separately `[a]p(x) & [b]p(x)` */
  lazy val choiceb            : DependentPositionTactic = useAt("[++] choice")
  /** composeb: [;] handle both parts of a sequential composition `[a;b]p(x)` one at a time `[a][b]p(x)` */
  lazy val composeb           : DependentPositionTactic = useAt("[;] compose")

  /** iterateb: [*] prove a property of a loop `[{a}*]p(x)` by unrolling it once `p(x) & [a][{a}*]p(x)` */
  lazy val iterateb           : DependentPositionTactic = useAt("[*] iterate")
  /** dualb: [^d^] handle dual game `[{a}^d^]p(x)` by `![a]!p(x)` */
  lazy val dualb              : DependentPositionTactic = useAt("[d] dual")

  //
  // diamond modality
  //

  /** box: [.] to reduce double-negated diamond `!⟨a⟩!p(x)` to a box `[a]p(x)`. */
  lazy val box                : DependentPositionTactic = useAt("[] box")
  /** assignd: <:=> simplify assignment `<x:=f;>p(x)` by substitution `p(f)` or equation */
  lazy val assignd            : DependentPositionTactic = "assignd" by { (pos:Position) =>
    useAt("<:=> assign")(pos) | DLBySubst.assigndEquality(pos)
  }

  /** randomd: <:*> simplify nondeterministic assignment `<x:=*;>p(x)` to an existential quantifier `\exists x p(x)` */
  lazy val randomd            : DependentPositionTactic = useAt("<:*> assign nondet")
  /** testd: <?> simplifies test `<?q;>p` to a conjunction `q&p` */
  lazy val testd              : DependentPositionTactic = useAt("<?> test")
  /** diffSolve: solve a differential equation `<x'=f>p(x)` to `\exists t>=0 <x:=solution(t)>p(x)` */
  //def diffSolved              : DependentPositionTactic = ???
  /** choiced: <++> handles both cases of a nondeterministic choice `⟨a++b⟩p(x)` separately `⟨a⟩p(x) | ⟨b⟩p(x)` */
  lazy val choiced            : DependentPositionTactic = useAt("<++> choice")
  /** composed: <;> handle both parts of a sequential composition `⟨a;b⟩p(x)` one at a time `⟨a⟩⟨b⟩p(x)` */
  lazy val composed           : DependentPositionTactic = useAt("<;> compose")
  /** iterated: <*> prove a property of a loop `⟨{a}*⟩p(x)` by unrolling it once `p(x) | ⟨a⟩⟨{a}*⟩p(x)` */
  lazy val iterated           : DependentPositionTactic = useAt("<*> iterate")
  /** duald: `<^d^>` handle dual game `⟨{a}^d^⟩p(x)` by `!⟨a⟩!p(x)` */
  lazy val duald              : DependentPositionTactic = useAt("<d> dual")

//  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
//  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
//  def loop(invariant: Formula) = I(invariant)
  /** K: modal modus ponens (hybrid systems)
    * @note Use with care since limited to hybrid systems. Use [[monb]] instead.
    * @see [[monb]]
    * @see [[mond]]
    */
  lazy val K                  : DependentPositionTactic = useAt("K modal modus ponens", PosInExpr(1::Nil))
  /** V: vacuous box `[a]p()` will be discarded and replaced by `p()` provided program `a` does not change values of postcondition `p()`.
    * @note Unsound for hybrid games
    */
  lazy val V                  : DependentPositionTactic = useAt("V vacuous")
  /** VK: vacuous box `[a]p()` will be discarded and replaced by `p()` provided program `a` does not change values of postcondition `p()`
    * and provided `[a]true` proves, e.g., since `a` is a hybrid system.
    */
  lazy val VK                 : DependentPositionTactic = useAt("VK vacuous")

  //
  // differential equations
  //

  /** DW: Differential Weakening to use evolution domain constraint `[{x'=f(x)&q(x)}]p(x)` reduces to `[{x'=f(x)&q(x)}](q(x)->p(x))` */
  lazy val DW                 : DependentPositionTactic = useAt("DW differential weakening")
  /** DWd: Diamond Differential Weakening to use evolution domain constraint `<{x'=f(x)&q(x)}>p(x)` reduces to `<{x'=f(x)&q(x)}>(q(x)&p(x))` */
  lazy val DWd                 : DependentPositionTactic = useAt("DWd diamond differential weakening")
  /** DC: Differential Cut a new invariant for a differential equation `[{x'=f(x)&q(x)}]p(x)` reduces to `[{x'=f(x)&q(x)&C(x)}]p(x)` with `[{x'=f(x)&q(x)}]C(x)`. */
  def DC(invariant: Formula)  : DependentPositionTactic = "ANON" byWithInput (invariant, (pos: Position, _: Sequent) => {
    useAt("DC differential cut",
      (us:Option[Subst])=>us.getOrElse(throw BelleUnsupportedFailure("Unexpected missing substitution in DC"))++RenUSubst(Seq((UnitPredicational("r",AnyArg), invariant)))
    )(pos)
  })
  /** DCd: Diamond Differential Cut a new invariant for a differential equation `<{x'=f(x)&q(x)}>p(x)` reduces to `<{x'=f(x)&q(x)&C(x)}>p(x)` with `[{x'=f(x)&q(x)}]C(x)`. */
  def DCd(invariant: Formula)  : DependentPositionTactic = useAt("DCd diamond differential cut",
    (us:Option[Subst])=>us.getOrElse(throw BelleUnsupportedFailure("Unexpected missing substitution in DCd"))++RenUSubst(Seq((UnitPredicational("r",AnyArg), invariant)))
  )
  /** DE: Differential Effect exposes the effect of a differential equation `[x'=f(x)]p(x,x')` on its differential symbols
    * as `[x'=f(x)][x':=f(x)]p(x,x')` with its differential assignment `x':=f(x)`.
    * {{{
    *   G |- [{x'=f(||)&H(||)}][x':=f(||);]p(||), D
    *   -------------------------------------------
    *   G |- [{x'=f(||)&H(||)}]p(||), D
    * }}}
    *
    * @example{{{
    *    |- [{x'=1}][x':=1;]x>0
    *    -----------------------DE(1)
    *    |- [{x'=1}]x>0
    * }}}
    * @example{{{
    *    |- [{x'=1, y'=x & x>0}][y':=x;][x':=1;]x>0
    *    -------------------------------------------DE(1)
    *    |- [{x'=1, y'=x & x>0}]x>0
    * }}}
    */
  lazy val DE                 : DependentPositionTactic = DifferentialTactics.DE
  /** DI: Differential Invariants are used for proving a formula to be an invariant of a differential equation.
    * `[x'=f(x)&q(x)]p(x)` reduces to `q(x) -> p(x) & [x'=f(x)]p(x)'`.
    * @see [[DifferentialTactics.diffInd()]] */
  lazy val DI                 : DependentPositionTactic = useAt("DI differential invariant")

  /** DGC: Differential ghost add auxiliary differential equation with extra constant g */
  private[btactics] def DGC(y:Variable, b:Term) =
    useAt("DG differential ghost constant", PosInExpr(0::Nil),
      (us:Option[Subst])=>{
        val singular = FormulaTools.singularities(b)
        insist(singular.isEmpty, "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " + singular.mkString(","))
        us.getOrElse(throw BelleUnsupportedFailure("Unexpected missing substitution in DG"))++RenUSubst(Seq(
          (Variable("y_",None,Real), y),
          (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b)
        ))
      }
    )

  //@todo unclear
  private[btactics] def DGCa(y:Variable, b:Term) =
    useAt("DG differential ghost constant all", PosInExpr(0::Nil),
      (us:Option[Subst])=>{
        val singular = FormulaTools.singularities(b)
        insist(singular.isEmpty, "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " + singular.mkString(","))
        us.getOrElse(throw BelleUnsupportedFailure("Unexpected missing substitution in DG"))++RenUSubst(Seq(
          (Variable("y_",None,Real), y),
          (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b)
        ))
      }
    )

  /** DGC: Differential ghost add auxiliary differential equation with extra constant g */
  private[btactics] def DGCd(y:Variable, b:Term) =
  useAt("DGd diamond differential ghost constant", PosInExpr(0::Nil),
    (us:Option[Subst])=>{
      val singular = FormulaTools.singularities(b)
      insist(singular.isEmpty, "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " + singular.mkString(","))
      us.getOrElse(throw BelleUnsupportedFailure("Unexpected missing substitution in DGd"))++RenUSubst(Seq(
        (Variable("y_",None,Real), y),
        (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b)
      ))
    }
  )
  private[btactics] def DGCde(y:Variable, b:Term) =
    useAt("DGd diamond differential ghost constant exists", PosInExpr(0::Nil),
      (us:Option[Subst])=>{
        val singular = FormulaTools.singularities(b)
        insist(singular.isEmpty, "Possible singularities during DG(" + DifferentialSymbol(y) + "=" + b + ") will be rejected: " + singular.mkString(","))
        us.getOrElse(throw BelleUnsupportedFailure("Unexpected missing substitution in DGde"))++RenUSubst(Seq(
          (Variable("y_",None,Real), y),
          (UnitFunctional("b", Except(Variable("y_", None, Real)), Real), b)
        ))
      }
    )

  //  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
//  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
  /** DS: Differential Solution solves a simple differential equation `[x'=c&q(x)]p(x)` by reduction to
    * `\forall t>=0 ((\forall 0<=s<=t  q(x+c()*s) -> [x:=x+c()*t;]p(x))` */
  lazy val DS                 : DependentPositionTactic = useAt("DS& differential equation solution")

  /** Dassignb: [':=] Substitute a differential assignment `[x':=f]p(x')` to `p(f)` */
  //@note potential incompleteness here should not ever matter
  lazy val Dassignb           : DependentPositionTactic =  useAt("[':=] differential assign")

  /*******************************************************************
    * Derive by proof
    *******************************************************************/

  /** Derive the differential expression at the indicated position (Hilbert computation deriving the answer by proof).
    * @example When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+x'*y+x*y'>=0
    * @see [[UnifyUSCalculus.chase]]
    */
  lazy val derive: DependentPositionTactic = "derive" by {(pos:Position) => chase(pos)}

  /**
    * Derive: provides individual differential axioms bundled as [[HilbertCalculus.derive]].
    *
    * There is rarely a reason to use these separate axioms, since [[HilbertCalculus.derive]] already
    * uses the appropriate differential axiom as needed.
    * @see Figure 3 in Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see [[HilbertCalculus.derive]]
    */
  object Derive {
    /** Dplus: +' derives a sum `(f(x)+g(x))' = (f(x))' + (g(x))'` */
    lazy val Dplus              : DependentPositionTactic = useAt("+' derive sum")
    /** neg: -' derives unary negation `(-f(x))' = -(f(x)')` */
    lazy val Dneg               : DependentPositionTactic = useAt("-' derive neg")
    /** Dminus: -' derives a difference `(f(x)-g(x))' = (f(x))' - (g(x))'` */
    lazy val Dminus             : DependentPositionTactic = useAt("-' derive minus")
    /** Dtimes: *' derives a product `(f(x)*g(x))' = f(x)'*g(x) + f(x)*g(x)'` */
    lazy val Dtimes             : DependentPositionTactic = useAt("*' derive product")
    /** Dquotient: /' derives a quotient `(f(x)/g(x))' = (f(x)'*g(x) - f(x)*g(x)') / (g(x)^2)` */
    lazy val Dquotient          : DependentPositionTactic = useAt("/' derive quotient")
    /** Dpower: ^' derives a power */
    lazy val Dpower             : DependentPositionTactic = useAt("^' derive power")
    /** Dcompose: o' derives a function composition by chain rule */
    lazy val Dcompose           : DependentPositionTactic = ???
    /** Dconst: c()' derives a constant `c()' = 0` */
    lazy val Dconst             : DependentPositionTactic = useAt("c()' derive constant fn")
    /** Dvariable: x' derives a variable `(x)' = x'`
      * Syntactically derives a differential of a variable to a differential symbol.
      * {{{
      *   G |- x'=f, D
      *   --------------
      *   G |- (x)'=f, D
      * }}}
      *
      * @example{{{
      *   |- x'=1
      *   ----------Dvariable(1, 0::Nil)
      *   |- (x)'=1
      * }}}
      * @example{{{
      *   |- [z':=1;]z'=1
      *   ------------------Dvariable(1, 1::0::Nil)
      *   |- [z':=1;](z)'=1
      * }}}
      * @incontext
      */
    lazy val Dvar: DependentPositionTactic = "Dvar" by {(pos:Position) => (if (INTERNAL) useAt("x' derive var") else DifferentialTactics.Dvariable)(pos)}

    /** Dand: &' derives a conjunction `(p(x)&q(x))'` to obtain `p(x)' & q(x)'` */
    lazy val Dand               : DependentPositionTactic = useAt("&' derive and")
    /** Dor: |' derives a disjunction `(p(x)|q(x))'` to obtain `p(x)' & q(x)'` */
    lazy val Dor                : DependentPositionTactic = useAt("|' derive or")
    /** Dimply: ->' derives an implication `(p(x)->q(x))'` to obtain `(!p(x) | q(x))'` */
    lazy val Dimply             : DependentPositionTactic = useAt("->' derive imply")
    /** Dequal: =' derives an equation `(f(x)=g(x))'` to obtain `f(x)'=g(x)'` */
    lazy val Dequal             : DependentPositionTactic = useAt("=' derive =")
    /** Dnotequal: !=' derives a disequation `(f(x)!=g(x))'` to obtain `f(x)'=g(x)'` */
    lazy val Dnotequal          : DependentPositionTactic = useAt("!=' derive !=")
    /** Dless: <' derives less-than `(f(x)⟨g(x))'` to obtain `f(x)'<=g(x)'` */
    lazy val Dless              : DependentPositionTactic = useAt("<' derive <")
    /** Dlessequal: <=' derives a less-or-equal `(f(x)<=g(x))'` to obtain `f(x)'<=g(x)'` */
    lazy val Dlessequal         : DependentPositionTactic = useAt("<=' derive <=")
    /** Dgreater: >' derives greater-than `(f(x)>g(x))'` to obtain `f(x)'>=g(x)'` */
    lazy val Dgreater           : DependentPositionTactic = useAt(">' derive >")
    /** Dgreaterequal: >=' derives a greater-or-equal `(f(x)>=g(x))'` to obtain `f(x)'>=g(x)'` */
    lazy val Dgreaterequal      : DependentPositionTactic = useAt(">=' derive >=")
    /** Dforall: \forall' derives an all quantifier `(\forall x p(x))'` to obtain `\forall x (p(x)')` */
    lazy val Dforall            : DependentPositionTactic = useAt("forall' derive forall")
    /** Dexists: \exists' derives an exists quantifier */
    lazy val Dexists            : DependentPositionTactic = useAt("exists' derive exists")
  }

  //
  // Additional
  //

  /** boxAnd: splits `[a](p&q)` into `[a]p & [a]q` */
  lazy val boxAnd             : DependentPositionTactic = useAt("[] split")
  /** diamondOr: splits `⟨a⟩(p|q)` into `⟨a⟩p | ⟨a⟩q` */
  lazy val diamondOr          : DependentPositionTactic = useAt("<> split")
  /** boxImpliesAnd: splits `[a](p->q&r)` into `[a](p->q) & [a](p->r)` */
  lazy val boxImpliesAnd      : DependentPositionTactic = useAt("[] conditional split")

  // def ind

  /** boxTrue: proves `[a]true` directly for hybrid systems `a` that are not hybrid games. */
  val boxTrue                : DependentPositionTactic = useAt("[]T system")


  /*******************************************************************
    * First-order logic
    *******************************************************************/

  /** allV: vacuous `\forall x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val allV               : DependentPositionTactic = useAt("vacuous all quantifier")
  /** existsV: vacuous `\exists x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val existsV            : DependentPositionTactic = useAt("vacuous exists quantifier")
  //@todo document and unclear what it really does depending on the index
  lazy val allDist            : DependentPositionTactic = useAt(DerivedAxioms.allDistributeAxiom)

  //@todo document and unclear what it really does depending on the index
  lazy val existsE            : DependentPositionTactic = useAt("exists eliminate")

}
