/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

//import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.{PosInExpr, Position}
import edu.cmu.cs.ls.keymaerax.tools.Tool

import scala.collection.immutable._

/**
 * Hilbert Calculus for differential dynamic logic.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see [[HilbertCalculus.derive()]]
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 */
object HilbertCalculus extends UnifyUSCalculus {

  /** True when insisting on internal useAt technology, false when external tactic calls are okay. */
  private val INTERNAL = true

  // modalities
  /** assignb: [:=] simplify assignment `[x:=f;]p(x)` by substitution `p(f)` or equation */
  lazy val assignb            : DependentPositionTactic = new DependentPositionTactic("[:=]") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = {
        if (INTERNAL) useAt("[:=] assign")(pos) | useAt("[:=] assign equational")(pos) | useAt("[:=] assign update")(pos)
        else ??? //TacticLibrary.boxAssignT
      }
    }
  }

  /** randomb: [:*] simplify nondeterministic assignment `[x:=*;]p(x)` to a universal quantifier `\forall x p(x)` */
  lazy val randomb            : DependentPositionTactic = useAt("[:*] assign nondet")
  /** testb: [?] simplifies test `[?q;]p` to an implication `q->p` */
  lazy val testb              : DependentPositionTactic = useAt("[?] test")
  /** diffSolve: solve a differential equation `[x'=f]p(x)` to `\forall t>=0 [x:=solution(t)]p(x)` */
  def diffSolve               : DependentPositionTactic = ??? //TacticLibrary.diffSolutionT
  /** choiceb: [++] handles both cases of a nondeterministic choice `[a++b]p(x)` separately `[a]p(x) & [b]p(x)` */
  lazy val choiceb            : DependentPositionTactic = useAt("[++] choice")
  /** composeb: [;] handle both parts of a sequential composition `[a;b]p(x)` one at a time `[a][b]p(x)` */
  lazy val composeb           : DependentPositionTactic = useAt("[;] compose")
  /** iterateb: [*] prove a property of a loop `[{a}*]p(x)` by unrolling it once `p(x) & [a][{a}*]p(x)` */
  lazy val iterateb           : DependentPositionTactic = useAt("[*] iterate")
  /** dualb: [^d] handle dual game `[{a}^d]p(x)` by `![a]!p(x)` */
  lazy val dualb              : DependentPositionTactic = useAt("[d] dual")

  /** assignd: <:=> simplify assignment `<x:=f;>p(x)` by substitution `p(f)` or equation */
  lazy val assignd            : DependentPositionTactic = new DependentPositionTactic("<:=>") {
    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v: BelleValue): BelleExpr = {
        useAt("<:=> assign") | useAt("<:=> assign equational") //@todo or "[:=] assign" if no clash
      }
    }
  }

  /** randomd: <:*> simplify nondeterministic assignment `<x:=*;>p(x)` to an existential quantifier `\exists x p(x)` */
  lazy val randomd            : DependentPositionTactic = useAt("<:*> assign nondet")
  /** testd: <?> simplifies test `<?q;>p` to a conjunction `q&p` */
  lazy val testd              : DependentPositionTactic = useAt("<?> test")
  /** diffSolve: solve a differential equation `<x'=f>p(x)` to `\exists t>=0 <x:=solution(t)>p(x)` */
  def diffSolved              : DependentPositionTactic = ???
  /** choiced: <++> handles both cases of a nondeterministic choice `<a++b>p(x)` separately `<a>p(x) | <b>p(x)` */
  lazy val choiced            : DependentPositionTactic = useAt("<++> choice")
  /** composed: <;> handle both parts of a sequential composition `<a;b>p(x)` one at a time `<a><b>p(x)` */
  lazy val composed           : DependentPositionTactic = useAt("<;> compose")
  /** iterated: <*> prove a property of a loop `<{a}*>p(x)` by unrolling it once `p(x) | <a><{a}*>p(x)` */
  lazy val iterated           : DependentPositionTactic = useAt("<*> iterate")
  /** duald: `<^d>` handle dual game `<{a}^d>p(x)` by `!<a>!p(x)` */
  lazy val duald              : DependentPositionTactic = useAt("<d> dual")

//  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
//  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
//  def loop(invariant: Formula) = I(invariant)
  /** K: modal modus ponens */
  //def K                       : PositionTactic = PropositionalTacticsImpl.kModalModusPonensT
  /** V: vacuous box [a]p() will be discarded and replaced by p() provided a does not changes values of postcondition p */
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
    * @see [[diffInd()]] */
  lazy val DI                 : DependentPositionTactic = useAt("DI differential invariant", PosInExpr(1::Nil))//TacticLibrary.diffInvariant
  /** diffInd: Differential Invariant proves a formula to be an invariant of a differential equation (by DI, DW, DE) */
  lazy val diffInd            : DependentPositionTactic = ???
//    new PositionTactic("diffInd") {
//      override def applies(s: Sequent, p: Position): Boolean = p.isSucc && (s.sub(p) match {
//        case Some(Box(_: ODESystem, _)) => true
//        case Some(_) => false
//        case None => println("ill-positioned " + p + " in " + s + "\nin " + "diffInd(" + p + ")\n(" + s + ")"); return false
//      })
//      def apply(p: Position): Tactic = new ConstructionTactic(name) {
//        override def applicable(node : ProofNode) = applies(node.sequent, p)
//        override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
//        //@todo Dconstify usually needed for DI
//          if (p.isTopLevel && p.isSucc)
//            Some(DI(p) &
//              (stepAt(p) & stepAt(p)) && (
//              QE,
//              //@note derive before DE to keep positions easier
//              derive(p.append(PosInExpr(1::Nil))) &
//                DE(p) &
//                (Dassignb(p.append(PosInExpr(1::Nil))) * (s=>getODEDim(s,p))) &
//                //@note DW after DE to keep positions easier
//                ifT(hasODEDomain, DW)(p) &
//                TacticLibrary.abstractionT(p) & QE
//              ))
//        else
//            Some((DI &
//              //@note derive before DE to keep positions easier
//              shift(PosInExpr(1::1::Nil),
//              shift(PosInExpr(1::Nil), derive) &
//                DE &
//                (shift(PosInExpr(1::Nil), Dassignb) * getODEDim) &
//                //@note DW after DE to keep positions easier
//                ifT(hasODEDomain, DW) &
//                TacticLibrary.abstractionT
//              ))(p)
//              )
//      }
//    }

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
  lazy val DS                 : DependentPositionTactic = useAt("DS& differential equation solution")
  
  /** Dassignb: [:='] Substitute a differential assignment `[x':=f]p(x')` to `p(f)` */
  lazy val Dassignb           : DependentPositionTactic = useAt("[':=] differential assign")
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
  lazy val Dpower             : DependentPositionTactic = useAt("^' derive power", PosInExpr(1::0::Nil))
  /** Dcompose: o' derives a function composition by chain rule */
  //lazy val Dcompose           : PositionTactic = ???
  /** Dconst: c()' derives a constant `c()' = 0` */
  lazy val Dconst             : DependentPositionTactic = useAt("c()' derive constant fn")
  /** Dvariable: x' derives a variable `(x)' = x'` */
  lazy val Dvariable          : DependentPositionTactic = ???
//    if (false&&INTERNAL) useAt("x' derive var", PosInExpr(0::Nil)) //useAt("x' derive variable", PosInExpr(0::0::Nil))
//    else SyntacticDerivationInContext.symbolizeDifferential

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
  /** Dless: <' derives less-than `(f(x)<g(x))'` to obtain `f(x)'<=g(x)'` */
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



  /** splitb: splits `[a](p&q)` into `[a]p & [a]q` */
  lazy val splitb             : DependentPositionTactic = useAt("[] split")
  /** splitd: splits `<a>(p|q)` into `<a>p | <a>q` */
  lazy val splitd             : DependentPositionTactic = useAt("<> split")

  // def ind


  /*******************************************************************
    * First-order logic
    *******************************************************************/

  /** vacuousAll: vacuous `\forall x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val vacuousAll          : DependentPositionTactic = useAt("vacuous all quantifier")
  /** vacuousExists: vacuous `\exists x p()` will be discarded and replaced by p() provided x does not occur in p(). */
  lazy val vacuousExists       : DependentPositionTactic = useAt("vacuous exists quantifier")

  //@todo make the other quantifier axioms accessible by useAt too

  /*******************************************************************
    * Stepping auto-tactic
    *******************************************************************/

  /**
   * Make the canonical simplifying proof step based at the indicated position
   * except when a decision needs to be made (e.g. invariants for loops or for differential equations).
   * @author Andre Platzer
   * @note Efficient source-level indexing implementation.
   */
  lazy val stepAt: DependentPositionTactic = new DependentPositionTactic("stepAt") {
    override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = {
          val sub = sequent.sub(pos)
          if (sub.isEmpty) throw new BelleUserGeneratedError("ill-positioned " + pos + " in " + sequent + "\nin " + "stepAt(" + pos + ")\n(" + sequent + ")")
          sub.get match {
            case Box(a, _) => a match {
              case _: Assign    => assignb(pos)
              case _: AssignAny => randomb(pos)
              case _: Test      => testb(pos)
//              case ode: ODESystem if ODETactics.isDiffSolvable(sub.asInstanceOf[Formula])=> Some(diffSolve)
              case _: Compose   => composeb(pos)
              case _: Choice    => choiceb(pos)
              case _: Dual      => dualb(pos)
            }
            case Diamond(a, _) => a match {
              case _: Assign    => assignd(pos)
              case _: AssignAny => randomd(pos)
              case _: Test      => testd(pos)
//              case ode:ODESystem if ODETactics.isDiffSolvable(sub.asInstanceOf[Formula])=> ???
              case _: Compose   => composed(pos)
              case _: Choice    => choiced(pos)
              case _: Dual      => duald(pos)
            }
            case DifferentialFormula(f) => f match {
              case _: Equal     => Dequal(pos)
              case _: NotEqual  => Dnotequal(pos)
              case _: Greater   => Dgreater(pos)
              case _: GreaterEqual => Dgreaterequal(pos)
              case _: Less      => Dless(pos)
              case _: LessEqual => Dlessequal(pos)
              case _: And       => Dand(pos)
              case _: Or        => Dor(pos)
              case _: Imply     => Dimply(pos)
              case _: Forall    => Dforall(pos)
              case _: Exists    => Dexists(pos)
            }
            case Differential(t) => t match {
              case _: Variable  => Dvariable(pos)
              case _: Plus      => Dplus(pos)
              case _: Neg       => Dneg(pos)
              case _: Minus     => Dminus(pos)
              case _: Times     => Dtimes(pos)
              case _: Divide    => Dquotient(pos)
              case _: Power     => Dpower(pos)
              case _: Number    => Dconst(pos)
              case FuncOf(_,Nothing) => Dconst(pos)
            }
            case Not(f)         => f match {
              case Box(_,Not(_))=> useAt("<> dual")(pos)
              case _: Box       => useAt("![]")(pos)
              case Diamond(_,Not(_))=> useAt("[] dual")(pos)
              case _: Diamond   => useAt("!<>")(pos)
              case _: Forall    => useAt("!all")(pos)
              case _: Exists    => useAt("!exists")(pos)
              case _: Equal     => useAt("! =")(pos)
              case _: NotEqual  => useAt("! !=")(pos)
              case _: Less      => useAt("! <")(pos)
              case _: LessEqual => useAt("! <=")(pos)
              case _: Greater   => useAt("! >")(pos)
              case _: GreaterEqual => useAt("! >=")(pos)
              //@note for conceptual simplicity, use propositional and Skolem sequent rules, too
              case _ if pos.isTopLevel => if (pos.isAnte) ProofRuleTactics.notL(pos) else ProofRuleTactics.notR(pos)
              case _: Not       => useAt(DerivedAxioms.doubleNegationAxiom)(pos)
              case _: And       => useAt(DerivedAxioms.notAnd)(pos)
              case _: Or        => useAt(DerivedAxioms.notOr)(pos)
              case _: Imply     => useAt(DerivedAxioms.notImply)(pos)
              case _: Equiv     => useAt(DerivedAxioms.notEquiv)(pos)
            }
            //@note for conceptual simplicity, use propositional and Skolem sequent rules, too
            case _: Not   if pos.isTopLevel => assert(assertion=false, "already above"); if(pos.isAnte) ProofRuleTactics.notL(pos) else ProofRuleTactics.notR(pos)
            case _: And   if pos.isTopLevel => if (pos.isAnte) ProofRuleTactics.andL(pos)   else ProofRuleTactics.andR(pos)
            case _: Or    if pos.isTopLevel => if (pos.isAnte) ProofRuleTactics.orL(pos)    else ProofRuleTactics.orR(pos)
            case _: Imply if pos.isTopLevel => if (pos.isAnte) ProofRuleTactics.implyL(pos) else ProofRuleTactics.implyR(pos)
            case _: Equiv if pos.isTopLevel => if (pos.isAnte) ProofRuleTactics.equivL(pos) else ProofRuleTactics.equivR(pos)
            case _: Forall if pos.isTopLevel && !pos.isAnte => TactixLibrary.allR(pos)
            case _: Exists if pos.isTopLevel &&  pos.isAnte => TactixLibrary.existsL(pos)
          }
      }
    }
  }

  /*******************************************************************
    * Derive by proof
    *******************************************************************/

  /** Derive the differential expression at the indicated position (Hilbert computation deriving the answer by proof).
    * @example When applied at 1::Nil, turns [{x'=22}](2*x+x*y>=5)' into [{x'=22}]2*x'+x'*y+x*y'>=0
    * @see [[UnifyUSCalculus.chase]]
    */
  lazy val derive: DependentPositionTactic = ???
//    new PositionTactic("derive") {
//      override def applies(s: Sequent, p: Position): Boolean = s.sub(p) match {
//        case Some(Differential(_)) => true
//        case Some(DifferentialFormula(_)) => true
//        case Some(_) => false
//        case None => println("ill-positioned " + p + " in " + s + "\nin " + "derive(" + p + ")\n(" + s + ")"); return false
//      }
//    override def apply(p: Position): Tactic = chase(p)
//    }


  /*******************************************************************
    * Internal helpers
    *******************************************************************/

  /** Computing dimension of ODE at indicated position of a sequent */
  private val getODEDim: (Sequent, Position)=>Int = (sequent,pos) => {
    def odeDim(ode: ODESystem): Int = StaticSemantics.boundVars(ode).toSymbolSet.filter(x=>x.isInstanceOf[DifferentialSymbol]).size
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => odeDim(ode)
      case Some(Diamond(ode: ODESystem, _)) => odeDim(ode)
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Whether there is a proper ODE System at the indicated position of a sequent with >=2 ODEs */
  private val isODESystem: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ODESystem(_:DifferentialProduct,_), _))     => true
      case Some(Diamond(ODESystem(_:DifferentialProduct,_), _)) => true
      case Some(e) => false
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }

  /** Whether the ODE at indicated position of a sequent has a nontrivial domain */
  private val hasODEDomain: (Sequent,Position)=>Boolean = (sequent,pos) => {
    sequent.sub(pos) match {
      case Some(Box(ode: ODESystem, _))     => ode.constraint != True
      case Some(Diamond(ode: ODESystem, _)) => ode.constraint != True
      case Some(e) => throw new IllegalArgumentException("no ODE at position " + pos + " in " + sequent + "\nFound: " + e)
      case None => throw new IllegalArgumentException("ill-positioned " + pos + " in " + sequent)
    }
  }
}