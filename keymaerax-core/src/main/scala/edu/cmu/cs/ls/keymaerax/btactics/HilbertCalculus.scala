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
 * @author Andre Platzer
 * @author Stefan Mitsch
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see Andre Platzer. [[http://dx.doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
 * @see Andre Platzer. [[http://dx.doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @see [[HilbertCalculus.derive()]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
trait HilbertCalculus extends UnifyUSCalculus {

  /** True when insisting on internal useAt technology, false when more elaborate external tactic calls are used on demand. */
  private[btactics] val INTERNAL = false

  // axiomatic rules

  /** G: Gödel generalization rule reduces a proof of `|- [a]p(x)` to proving the postcondition `|- p(x)` in isolation.
    * {{{
    *       p(??)
    *   ----------- G
    *    [a]p(??)
    * }}}
    * The more flexible and more general rule [[monb]] with p(x)=True gives `G` using [[boxTrue]].
    * @note Unsound for hybrid games
    * @see [[monb]] with p(x)=True
    * @see [[boxTrue]]
    * @todo should lift to a PositionTactic = cohideR(pos) & DLBySubst.G
    */
  lazy val G                  : BelleExpr         = DLBySubst.G
  lazy val hideG              : BelleExpr         = new DependentPositionTactic("hideG") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = {
        ProofRuleTactics.coHideR(SuccPos(0)) & DLBySubst.G
      }
    }
  }

  /** allG: all generalization rule reduces a proof of `|- \forall x p(x)` to proving `|- p(x)` in isolation */
  lazy val allG               : BelleExpr         = ??? //AxiomaticRuleTactics.forallGeneralizationT
  /** CT: Term Congruence: Contextual Equivalence of terms at the indicated position to reduce an equality `c(f(x))=c(g(x))` to an equality `f(x)=g(x)` */
  //def CT(inEqPos: PosInExpr)  : Tactic         = ???
  /** CQ: Equation Congruence: Contextual Equivalence of terms at the indicated position to reduce an equivalence to an equation */
  //def CQ(inEqPos: PosInExpr)  : Tactic
  /** CE: Congruence: Contextual Equivalence at the indicated position to reduce an equivalence to an equivalence */
  //def CE(inEqPos: PosInExpr)  : Tactic
  /** monb: Monotone `[a]p(x) |- [a]q(x)` reduces to proving `p(x) |- q(x)` */
  lazy val monb               : BelleExpr         = DLBySubst.monb
  /** mond: Monotone `⟨a⟩p(x) |- ⟨a⟩q(x)` reduces to proving `p(x) |- q(x)` */
  lazy val mond               : BelleExpr         = DLBySubst.mond


  // axioms

  // modalities
  /** diamond: <.> reduce double-negated box `![a]!p(x)` to a diamond `⟨a⟩p(x)`. */
  lazy val diamond            : DependentPositionTactic = useAt("<> diamond")
  /** assignb: [:=] simplify assignment `[x:=f;]p(x)` by substitution `p(f)` or equation */
  lazy val assignb            : DependentPositionTactic =
//    "[:=]" by(pos =>
//    if (INTERNAL) ((useAt("[:=] assign")(pos) partial) | (useAt("[:=] assign equality")(pos) partial) /*| (useAt("[:=] assign update")(pos) partial)*/) partial
//    else DLBySubst.assignb(pos)
//    )
    new DependentPositionTactic("assignb") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = {
        if (INTERNAL) (useAt("[:=] assign")(pos) partial) | ((useAt("[:=] assign equality")(pos) partial) /*| (useAt("[:=] assign update")(pos) partial)*/) partial
        else DLBySubst.assignb(pos)
      }
    }
  }

  private def namedUseAt(name: String, axiomName: String) = new DependentPositionTactic(name) {
    assert(DerivationInfo.hasCodeName(name), s"${name} is a tactic name but is not a DerivationInfo codeName.")
    override def factory(pos: Position): DependentTactic = useAt(axiomName)(pos)
  }

  /** randomb: [:*] simplify nondeterministic assignment `[x:=*;]p(x)` to a universal quantifier `\forall x p(x)` */
  lazy val randomb            : DependentPositionTactic = namedUseAt("randomb", "[:*] assign nondet")
  /** testb: [?] simplifies test `[?q;]p` to an implication `q->p` */
  lazy val testb              : DependentPositionTactic = namedUseAt("testb", "[?] test")
  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)` */
  //def diffSolve               : DependentPositionTactic = ???
  /** choiceb: [++] handles both cases of a nondeterministic choice `[a++b]p(x)` separately `[a]p(x) & [b]p(x)` */
  lazy val choiceb            : DependentPositionTactic = namedUseAt("choiceb", "[++] choice")
  /** composeb: [;] handle both parts of a sequential composition `[a;b]p(x)` one at a time `[a][b]p(x)` */
  lazy val composeb           : DependentPositionTactic = namedUseAt("composeb", "[;] compose")

  /** iterateb: [*] prove a property of a loop `[{a}*]p(x)` by unrolling it once `p(x) & [a][{a}*]p(x)` */
  lazy val iterateb           : DependentPositionTactic = namedUseAt("iterateb", "[*] iterate")
  /** dualb: [^d^] handle dual game `[{a}^d^]p(x)` by `![a]!p(x)` */
  lazy val dualb              : DependentPositionTactic = namedUseAt("dualb", "[d] dual")

  /** assignd: <:=> simplify assignment `<x:=f;>p(x)` by substitution `p(f)` or equation */
  lazy val assignd            : DependentPositionTactic = new DependentPositionTactic("assignd") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = {
        useAt("<:=> assign") | useAt("<:=> assign equational") //@todo or "[:=] assign" if no clash
      }
    }
  }

  /** box: [.] to reduce double-negated diamond `!⟨a⟩!p(x)` to a box `[a]p(x)`. */
  lazy val box                : DependentPositionTactic = useAt("[] box")
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
  /** K: modal modus ponens (hybrid systems) */
  @deprecated("Use with care since limited to hybrid systems. Use monb instead.")
  lazy val K                  : DependentPositionTactic = useAt("K modal modus ponens", PosInExpr(1::Nil))
  /** V: vacuous box [a]p() will be discarded and replaced by p() provided a does not changes values of postcondition p.
    * @note Unsound for hybrid games
    * @see [[boxTrue]]
    */
    //@todo useAt except with dualFree as the tactic to prove the global prereq [a]true.
  lazy val V                  : DependentPositionTactic = useAt("V vacuous")
//
//  // differential equations
  /** DW: Differential Weakening to use evolution domain constraint `[{x'=f(x)&q(x)}]p(x)` reduces to `[{x'=f(x)&q(x)}](q(x)->p(x))` */
  lazy val DW                 : DependentPositionTactic = useAt("DW differential weakening")
  /** DC: Differential Cut a new invariant for a differential equation `[{x'=f(x)&q(x)}]p(x)` reduces to `[{x'=f(x)&q(x)&C(x)}]p(x)` with `[{x'=f(x)&q(x)}]C(x)`. */
  def DC(invariant: Formula)  : DependentPositionTactic = useAt("DC differential cut", PosInExpr(1::0::Nil),
    (us:Subst)=>us++RenUSubst(Seq((PredOf(Function("r",None,Real,Bool),Anything), invariant)))
  )
  /** DE: Differential Effect exposes the effect of a differential equation `[x'=f(x)]p(x,x')` on its differential symbols as `[x'=f(x)][x':=f(x)]p(x,x')` with its differential assignment `x':=f(x)`. */
  lazy val DE                 : DependentPositionTactic = DifferentialTactics.DE
  /** DI: Differential Invariants are used for proving a formula to be an invariant of a differential equation.
    * `[x'=f(x)&q(x)]p(x)` reduces to `q(x) -> p(x) & [x'=f(x)]p(x)'`.
    * @see [[DifferentialTactics.diffInd()]] */
  lazy val DI                 : DependentPositionTactic = useAt("DI differential invariant")

  /** DG: Differential Ghost add auxiliary differential equations with extra variables `y'=a*y+b`.
    * `[x'=f(x)&q(x)]p(x)` reduces to `\exists y [x'=f(x),y'=a*y+b&q(x)]p(x)`.
    */
  def DG(y:Variable, a:Term, b:Term) : BelleExpr = useAt("DG differential ghost", PosInExpr(1::0::Nil),
    (us:Subst)=>us++RenUSubst(Seq(
      (Variable("y",None,Real), y),
      (FuncOf(Function("t",None,Real,Real),DotTerm), a),
      (FuncOf(Function("s",None,Real,Real),DotTerm), b)))
  )

  //  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
//  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
  /** DS: Differential Solution solves a simple differential equation `[x'=c&q(x)]p(x)` by reduction to
    * `\forall t>=0 ((\forall 0<=s<=t  q(x+c()*s) -> [x:=x+c()*t;]p(x))` */
  lazy val DS                 : DependentPositionTactic = namedUseAt("DS", "DS& differential equation solution")
  
  /** Dassignb: [:='] Substitute a differential assignment `[x':=f]p(x')` to `p(f)` */
  lazy val Dassignb           : DependentPositionTactic = namedUseAt("Dassignb", "[':=] differential assign")
  /** Dplus: +' derives a sum `(f(x)+g(x))' = (f(x))' + (g(x))'` */
  lazy val Dplus              : DependentPositionTactic = namedUseAt("Dplus", "+' derive sum")
  /** neg: -' derives unary negation `(-f(x))' = -(f(x)')` */
  lazy val Dneg               : DependentPositionTactic = namedUseAt("Dneg", "-' derive neg")
  /** Dminus: -' derives a difference `(f(x)-g(x))' = (f(x))' - (g(x))'` */
  lazy val Dminus             : DependentPositionTactic = namedUseAt("Dminus", "-' derive minus")
  /** Dtimes: *' derives a product `(f(x)*g(x))' = f(x)'*g(x) + f(x)*g(x)'` */
  lazy val Dtimes             : DependentPositionTactic = namedUseAt("Dtimes", "*' derive product")
  /** Dquotient: /' derives a quotient `(f(x)/g(x))' = (f(x)'*g(x) - f(x)*g(x)') / (g(x)^2)` */
  lazy val Dquotient          : DependentPositionTactic = namedUseAt("Dquotient", "/' derive quotient")
  /** Dpower: ^' derives a power */
  lazy val Dpower             : DependentPositionTactic = namedUseAt("Dpower", "^' derive power")
  /** Dcompose: o' derives a function composition by chain rule */
  lazy val Dcompose           : DependentPositionTactic = ???
  /** Dconst: c()' derives a constant `c()' = 0` */
  lazy val Dconst             : DependentPositionTactic = namedUseAt("Dconst", "c()' derive constant fn")
  /** Dvariable: x' derives a variable `(x)' = x'` */
  lazy val Dvar               : DependentPositionTactic = new DependentPositionTactic("Dvar") {
    /** Create the actual tactic to be applied at position pos */
    override def factory(pos: Position): DependentTactic = (if (INTERNAL) useAt("x' derive var", PosInExpr(0::Nil)) else DifferentialTactics.Dvariable)(pos)
  }

  /** Dcompose: o' derives a function composition by chain rule */
  //@todo lazy val Dcompose           : BuiltInPositionTactic = ???

  /** Dand: &' derives a conjunction `(p(x)&q(x))'` to obtain `p(x)' & q(x)'` */
  lazy val Dand               : DependentPositionTactic = namedUseAt("Dand", "&' derive and")
  /** Dor: |' derives a disjunction `(p(x)|q(x))'` to obtain `p(x)' & q(x)'` */
  lazy val Dor                : DependentPositionTactic = namedUseAt("Dor", "|' derive or")
  /** Dimply: ->' derives an implication `(p(x)->q(x))'` to obtain `(!p(x) | q(x))'` */
  lazy val Dimply             : DependentPositionTactic = namedUseAt("Dimply", "->' derive imply")
  /** Dequal: =' derives an equation `(f(x)=g(x))'` to obtain `f(x)'=g(x)'` */
  lazy val Dequal             : DependentPositionTactic = namedUseAt("Dequal", "=' derive =")
  /** Dnotequal: !=' derives a disequation `(f(x)!=g(x))'` to obtain `f(x)'=g(x)'` */
  lazy val Dnotequal          : DependentPositionTactic = namedUseAt("Dnotequal", "!=' derive !=")
  /** Dless: <' derives less-than `(f(x)<g(x))'` to obtain `f(x)'<=g(x)'` */
  lazy val Dless              : DependentPositionTactic = namedUseAt("Dless", "<' derive <")
  /** Dlessequal: <=' derives a less-or-equal `(f(x)<=g(x))'` to obtain `f(x)'<=g(x)'` */
  lazy val Dlessequal         : DependentPositionTactic = namedUseAt("Dlessequal", "<=' derive <=")
  /** Dgreater: >' derives greater-than `(f(x)>g(x))'` to obtain `f(x)'>=g(x)'` */
  lazy val Dgreater           : DependentPositionTactic = namedUseAt("Dgreater", ">' derive >")
  /** Dgreaterequal: >=' derives a greater-or-equal `(f(x)>=g(x))'` to obtain `f(x)'>=g(x)'` */
  lazy val Dgreaterequal      : DependentPositionTactic = namedUseAt("Dgreaterequal", ">=' derive >=")
  /** Dforall: \forall' derives an all quantifier `(\forall x p(x))'` to obtain `\forall x (p(x)')` */
  lazy val Dforall            : DependentPositionTactic = namedUseAt("Dforall", "forall' derive forall")
  /** Dexists: \exists' derives an exists quantifier */
  lazy val Dexists            : DependentPositionTactic = namedUseAt("Dexists", "exists' derive exists")



  /** splitb: splits `[a](p&q)` into `[a]p & [a]q` */
  //@todo rename to boxAnd? Does this replicate DerivedAxioms.boxAnd?
  lazy val splitb             : DependentPositionTactic = namedUseAt("boxAnd", "[] split") //@todo correct codeName might be boxAnd.
  /** splitd: splits `⟨a⟩(p|q)` into `⟨a⟩p | ⟨a⟩q` */
  lazy val splitd             : DependentPositionTactic = namedUseAt("splitd", "<> split")

  // def ind

  /** dualFree: proves `[a]true` directly for hybrid systems `a` that are not hybrid games. */
  val dualFree                : PositionalTactic = ProofRuleTactics.dualFree
  //@todo could do boxTrue = dualFree | master
  val boxTrue                 : PositionalTactic = dualFree


  /*******************************************************************
    * First-order logic
    *******************************************************************/

  /** allV: vacuous `\forall x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val allV               : DependentPositionTactic = namedUseAt("allV", "vacuous all quantifier")
  /** existsV: vacuous `\exists x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val existsV            : DependentPositionTactic = namedUseAt("existsV", "vacuous exists quantifier")
  lazy val allDist            : DependentPositionTactic = useAt(DerivedAxioms.allDistributeAxiom)

  //@todo make the other quantifier axioms accessible by useAt too

  /**
   * Make the canonical simplifying proof step based at the indicated position
   * except when an unknown decision needs to be made (e.g. invariants for loops or for differential equations).
   * Using the canonical [[AxiomIndex]].
   * @author Andre Platzer
   * @note Efficient source-level indexing implementation.
   * @see [[AxiomIndex]]
   */
  lazy val stepAt: DependentPositionTactic = stepAt(AxiomIndex.axiomFor)

  /*******************************************************************
    * Derive by proof
    *******************************************************************/

  /** Derive the differential expression at the indicated position (Hilbert computation deriving the answer by proof).
    * @example When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+x'*y+x*y'>=0
    * @see [[UnifyUSCalculus.chase]]
    */
  lazy val derive: DependentPositionTactic = new DependentPositionTactic("derive") {
    override def factory(pos: Position): DependentTactic = chase(pos)
  }

}
