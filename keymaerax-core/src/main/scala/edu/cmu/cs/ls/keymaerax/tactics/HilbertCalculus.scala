/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.UnificationMatch

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.skolemizeT
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
 * Hilbert Calculus for differential dynamic logic.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 */
object HilbertCalculus {
  import TactixLibrary.useAt

  /** True when insisting on internal useAt technology, false when external tactic calls are okay. */
  private val INTERNAL = true

  // modalities
  /** assignb: [:=] simplify assignment by substitution or equation */
  lazy val assignb            : PositionTactic = if (INTERNAL) useAt("[:=] assign") | useAt("[:=] assign equational")
  else TacticLibrary.boxAssignT
  /** randomb: [:*] simplify nondeterministic assignment to universal quantifier */
  lazy val randomb            : PositionTactic = useAt("[:*] assign nondet")
  /** testb: [?] simplifies test to an implication */
  lazy val testb              : PositionTactic = useAt("[?] test")
  /** diffSolve: solve a differential equation */
  def diffSolve               : PositionTactic = TacticLibrary.diffSolutionT
  /** choiceb: [++] handles both cases of a nondeterministic choice separately */
  lazy val choiceb            : PositionTactic = useAt("[++] choice")
  /** composeb: [;] handle both parts of a sequential composition one at a time */
  lazy val composeb           : PositionTactic = useAt("[;] compose")
  /** iterateb: [*] prove a property of a loop by unrolling it once */
  lazy val iterateb           : PositionTactic = useAt("[*] iterate")
  /** dualb: [^d] handle dual game */
  lazy val dualb              : PositionTactic = useAt("[d] dual")

  /** assignd: <:=> simplify assignment by substitution or equation */
  lazy val assignd            : PositionTactic = useAt("<:=> assign equational") //@todo or "[:=] assign" if no clash
  /** randomd: <:*> simplify nondeterministic assignment to existential quantifier */
  lazy val randomd            : PositionTactic = useAt("<:*> assign nondet")
  /** testd: <?> simplifies test to a conjunction */
  lazy val testd              : PositionTactic = useAt("<?> test")
  /** diffSolve: solve a differential equation */
  def diffSolved              : PositionTactic = ???
  /** choiced: <++> handles both cases of a nondeterministic choice options separately */
  lazy val choiced            : PositionTactic = useAt("<++> choice")
  /** composed: <;> handle both parts of a sequential composition one at a time */
  lazy val composed           : PositionTactic = useAt("<;> compose")
  /** iterated: <*> prove a property of a loop by unrolling it once */
  lazy val iterated           : PositionTactic = useAt("<*> iterate")
  /** duald: <^d> handle dual game */
  lazy val duald              : PositionTactic = useAt("<d> dual")

//  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
//  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
//  def loop(invariant: Formula) = I(invariant)
//  /** K: modal modus ponens (hybrid systems) */
//  def K                       : PositionTactic = PropositionalTacticsImpl.kModalModusPonensT
//  /** V: vacuous box will be discarded (unless it changes values of the postcondition) (hybrid systems) */
//  def V                       : PositionTactic = HybridProgramTacticsImpl.boxVacuousT
//
//  // differential equations
  /** DW: Differential Weakening to use evolution domain constraint (equivalence form) */
  lazy val DW                 : PositionTactic = useAt("DW differential weakening")
  /** DC: Differential Cut a new invariant for a differential equation */
  def DC(invariant: Formula)  : PositionTactic = useAt("DC differential cut", PosInExpr(1::0::Nil),
    (us:Subst)=>us++RenUSubst(Seq((PredOf(Function("r",None,Real,Bool),Anything), invariant)))
  )
  /** DE: Differential Effect exposes the effect of a differential equation on its differential symbols */
  lazy val DE                 : PositionTactic = if (true || INTERNAL) (useAt("DE differential effect") | useAt("DE differential effect (system)"))
  else ODETactics.diffEffectT
  /** DI: Differential Invariant proves a formula to be an invariant of a differential equation */
  //@todo Dconstify usually needed for DI
  def DI                      : PositionTactic = useAt("DI differential invariant", PosInExpr(1::Nil))//TacticLibrary.diffInvariant
  /** DG: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b */
  def DG(y:Variable, a:Term, b:Term) : PositionTactic = useAt("DG differential ghost", PosInExpr(1::0::Nil),
    (us:Subst)=>us++RenUSubst(Seq(
      (Variable("y",None,Real), y),
      (FuncOf(Function("t",None,Real,Real),DotTerm), a),
      (FuncOf(Function("s",None,Real,Real),DotTerm), b)))
  )

  //  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
//  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
  /** DS: Differential Solution solves a differential equation */
  def DS                      : PositionTactic = useAt("DS& differential equation solution")
  /** Dassignb: Substitute a differential assignment */
  lazy val Dassignb           : PositionTactic = useAt("[':=] differential assign")
  /** Dplus: +' derives a sum */
  lazy val Dplus              : PositionTactic = useAt("+' derive sum")
  /** neg: -' derives neg */
  lazy val Dneg               : PositionTactic = useAt("-' derive neg")
  /** Dminus: -' derives a difference */
  lazy val Dminus             : PositionTactic = useAt("-' derive minus")
  /** Dtimes: *' derives a product */
  lazy val Dtimes             : PositionTactic = useAt("*' derive product")
  /** Dquotient: /' derives a quotient */
  lazy val Dquotient          : PositionTactic = useAt("/' derive quotient")
  /** Dpower: ^' derives a power */
  lazy val Dpower             : PositionTactic = useAt("^' derive power", PosInExpr(1::0::Nil))
  /** Dcompose: o' derives a function composition by chain rule */
  //lazy val Dcompose           : PositionTactic = ???
  /** Dconst: c()' derives a constant */
  lazy val Dconst             : PositionTactic = useAt("c()' derive constant fn")
  /** Dvariable: x' derives a variable */
  lazy val Dvariable          : PositionTactic = if (false&&INTERNAL) useAt("x' derive variable", PosInExpr(0::0::Nil))
  else SyntacticDerivationInContext.symbolizeDifferential

  /** Dand: &' derives a conjunction */
  lazy val Dand               : PositionTactic = useAt("&' derive and")
  /** Dor: |' derives a disjunction */
  lazy val Dor                : PositionTactic = useAt("|' derive or")
  /** Dimply: ->' derives an implication */
  lazy val Dimply             : PositionTactic = useAt("->' derive imply")
  /** Dequal: =' derives an equation */
  lazy val Dequal             : PositionTactic = useAt("=' derive =")
  /** Dnotequal: !=' derives a disequation */
  lazy val Dnotequal          : PositionTactic = useAt("!=' derive !=")
  /** Dless: <' derives less-than */
  lazy val Dless              : PositionTactic = useAt("<' derive <")
  /** Dlessequal: <=' derives a less-or-equal */
  lazy val Dlessequal         : PositionTactic = useAt("<=' derive <=")
  /** Dgreater: >' derives greater-than */
  lazy val Dgreater           : PositionTactic = useAt(">' derive >")
  /** Dgreaterequal: >=' derives a greater-or-equal */
  lazy val Dgreaterequal      : PositionTactic = useAt(">=' derive >=")
  /** Dforall: \forall' derives an all quantifier */
  lazy val Dforall            : PositionTactic = useAt("forall' derive forall")
  /** Dexists: \exists' derives an exists quantifier */
  lazy val Dexists            : PositionTactic = useAt("exists' derive exists")

  //lazy val ind

  /**
   * Make the canonical simplifying proof step based at the indicated position
   * except when a decision needs to be made (e.g. invariants for loops or for differential equations).
   * @author Andre Platzer
   * @note Efficient source-level indexing implementation.
   */
  lazy val stepAt: PositionTactic = new PositionTactic("stepAt") {
    import FormulaConverter._
    //import TactixLibrary._
    override def applies(s: Sequent, p: Position): Boolean = getTactic(s, p).isDefined

    def getTactic(s: Sequent, p: Position): Option[PositionTactic] = {
      val sub = s(p.top).at(p)
      if (sub.isEmpty) None else sub.get match {
        case Box(a, _) => a match {
          case _: Assign    => Some(assignb)
          case _: AssignAny => Some(randomb)
          case _: Test      => Some(testb)
          case ode:ODESystem if ODETactics.isDiffSolvable(sub.get.asInstanceOf[Formula])=> Some(diffSolve)
          case _: Compose   => Some(composeb)
          case _: Choice    => Some(choiceb)
          case _: Dual      => Some(dualb)
          case _ => None
        }
        case Diamond(a, _) => a match {
          case _: Assign    => Some(assignd)
          case _: AssignAny => Some(randomd)
          case _: Test      => Some(testd)
          case ode:ODESystem if ODETactics.isDiffSolvable(sub.get.asInstanceOf[Formula])=> ???
          case _: Compose   => Some(composed)
          case _: Choice    => Some(choiced)
          case _: Dual      => Some(duald)
          case _ => None
        }
        case DifferentialFormula(f) => f match {
          case _: Equal     => Some(Dequal)
          case _: NotEqual  => Some(Dnotequal)
          case _: Greater   => Some(Dgreater)
          case _: GreaterEqual => Some(Dgreaterequal)
          case _: Less      => Some(Dless)
          case _: LessEqual => Some(Dlessequal)
          case _: And       => Some(Dand)
          case _: Or        => Some(Dor)
          case _: Imply     => Some(Dimply)
          case _: Forall    => Some(Dforall)
          case _: Exists    => Some(Dexists)
        }
        case Differential(t) => t match {
          case _: Variable  => Some(Dvariable)
          case _: Plus      => Some(Dplus)
          case _: Neg       => Some(Dneg)
          case _: Minus     => Some(Dminus)
          case _: Times     => Some(Dtimes)
          case _: Divide    => Some(Dquotient)
          case _: Power     => Some(Dpower)
          case _: Number    => Some(Dconst)
          case FuncOf(_,Nothing) => Some(Dconst)
        }
        case Not(f)         => f match {
          case _: Box       => Some(useAt("![]"))
          case _: Diamond   => Some(useAt("!<>"))
          case _: Forall    => Some(useAt("!all"))
          case _: Exists    => Some(useAt("!exists"))
          case _: Equal     => ???
          case _: NotEqual  => Some(useAt("= negate"))
          case _: Less      => Some(useAt("< negate"))
          case _: LessEqual => ???
          case _: Greater   => ???
          case _: GreaterEqual => ???
          //@note for conceptual simplicity, use propositional and Skolem sequent rules, too
          case _ if p.isTopLevel => if(p.isAnte) Some(TactixLibrary.notL)   else Some(TactixLibrary.notR)
          case _: Not       => Some(useAt(DerivedAxioms.doubleNegationAxiom))
          case _: And       => Some(useAt(DerivedAxioms.notAnd))
          case _: Or        => Some(useAt(DerivedAxioms.notOr))
          case _: Imply     => Some(useAt(DerivedAxioms.notImply))
          case _: Equiv     => Some(useAt(DerivedAxioms.notEquiv))
        }
        //@note for conceptual simplicity, use propositional and Skolem sequent rules, too
        case _: Not   if p.isTopLevel => assert(false, "already above"); if(p.isAnte) Some(TactixLibrary.notL)   else Some(TactixLibrary.notR)
        case _: And   if p.isTopLevel => if(p.isAnte) Some(TactixLibrary.andL)   else Some(TactixLibrary.andR)
        case _: Or    if p.isTopLevel => if(p.isAnte) Some(TactixLibrary.orL)    else Some(TactixLibrary.orR)
        case _: Imply if p.isTopLevel => if(p.isAnte) Some(TactixLibrary.implyL) else Some(TactixLibrary.implyR)
        case _: Equiv if p.isTopLevel => if(p.isAnte) Some(TactixLibrary.equivL) else Some(TactixLibrary.equivR)
        case _: Forall if p.isTopLevel && !p.isAnte => Some(TactixLibrary.allR)
        case _: Exists if p.isTopLevel &&  p.isAnte => Some(TactixLibrary.existsL)
        case _ => None
      }
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
        getTactic(node.sequent, p) match {
          case None => None
          case Some(postac) => Some(postac(p))
        }
    }
  }

  /** Derive the differential expression at the indicated position (Hilbert computation) */
  lazy val derive: PositionTactic = new PositionTactic("derive") {
    import FormulaConverter._
    import TermConverter._
    import SequentConverter._
    import TactixLibrary._

    override def applies(s: Sequent, p: Position): Boolean = s.at(p) match {
      case Some(Differential(_)) => true
      case Some(DifferentialFormula(_)) => true
      case _ => false
    }

    override def apply(p: Position): Tactic = new ConstructionTactic(this.name) {
      override def applicable(node: ProofNode): Boolean = applies(node.sequent, p)

      override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] = {
        node.sequent.at(p).get match {
          case t: Term    => Some(useDirectAt(deriveProof(t),  PosInExpr(0::Nil))(p)
            //@todo why is the following needed? useAt doesn't optimize subst=id?
            & debugC("derived") & byUS("= reflexive"))
          case f: Formula => Some(useDirectAt(deriveProofF(f), PosInExpr(0::Nil))(p)
            & debugC("derived") & byUS("<-> reflexive"))
        }

      }

      /** Construct a proof proving the answer of the derivative of de expanded out to variables */
      private def deriveProof(de: Term): Provable = {
        val deIsDe = Sequent(Nil, IndexedSeq(), IndexedSeq(Equal(de,de)))
        val initial = DerivedAxioms.equalReflex.fact(
          deIsDe,
              UniformSubstitutionRule(USubst(SubstitutionPair(FuncOf(Function("s",None,Unit,Real),Nothing), de)::Nil), DerivedAxioms.equalReflex.fact.conclusion))
        assert(initial.isProved && initial.proved==deIsDe, "Proved reflexive start " + initial + " for " + de)
        if (DEBUG) println("derive starts at " + initial)
        val r = derive(initial, PosInExpr(1::Nil))
        if (DEBUG) println("derive(" + de.prettyString + ") = ~~> " + r + " done")
        r
      } ensuring(r => r.isProved, "derive remains proved: " + " final derive(" + de + ")")

      private def debugF(s: => Any): (Provable=>Provable)=>(Provable=>Provable) = tac => proof => {val pr = tac(proof); if (DEBUG) println("=== " + s + " === " + pr); pr}
      private def debugPF(s: => Any): (Position=>Provable=>Provable)=>(Position=>Provable=>Provable) = tac => pos => proof => {val pr = tac(pos)(proof); if (DEBUG) println("=== " + s + " === " + pr); pr}

      private def derive(de: Provable, pos: PosInExpr): Provable = {
        if (DEBUG) println("derive(" + de.conclusion.succ.head.subAt(pos).prettyString + ")")
        val r = de.conclusion.succ.head.subAt(pos) match {
          // terms
        case Differential(Neg(_)) => derive(
          useFor("-' derive neg")(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(0::Nil)))
        case Differential(Plus(_,_)) => derive(derive(
          debugPF("derive(+')")(useFor("+' derive sum"))(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(0::Nil))),
          pos.append(PosInExpr(1::Nil))
        )
        case Differential(Minus(_,_)) => derive(derive(
          useFor("-' derive minus")(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(0::Nil))),
          pos.append(PosInExpr(1::Nil))
        )
        //@note optimizations
        case Differential(Times(num,_)) if StaticSemantics.freeVars(num).isEmpty => derive(
          debugPF("derive(l')")(useFor("' linear"))(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(1::Nil))
        )
        case Differential(Times(_,num)) if StaticSemantics.freeVars(num).isEmpty => derive(
          debugPF("derive(l')")(useFor("' linear right"))(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(0::Nil))
        )
        case Differential(Times(_,_)) => derive(derive(
          debugPF("derive(*')")(useFor("*' derive product"))(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(0::0::Nil))),
          pos.append(PosInExpr(1::1::Nil))
        )
        case Differential(Divide(_,_)) => derive(derive(
          debugPF("derive(/')")(useFor("/' derive quotient"))(SuccPosition(0,pos))(de),
          pos.append(PosInExpr(0::0::0::Nil))),
          pos.append(PosInExpr(0::1::1::Nil))
        )
        case Differential(Number(_)) =>
          debugPF("c()'")(useFor("c()' derive constant fn"))(SuccPosition(0,pos))(de)
        case Differential(x:Variable) =>
          if (false&&INTERNAL) useFor("x' derive variable", PosInExpr(0::0::Nil))(SuccPosition(0,pos))(de)
          else if (true)
            debugPF("derive(x')")(useFor(Axiom.axiom("x' derive var")(
              Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x),DifferentialSymbol(x)))),
              UniformRenaming(Variable("x_",None,Real),x)),
              PosInExpr(0::Nil)
            ))(SuccPosition(0,pos))(de)
            //useFor(Axiom.axiom("x' derive var"), PosInExpr(0::Nil))(SuccPosition(0,pos))(de)
            //useFor("all eliminate")(SuccPosition(0))(Axiom.axiom("x' derive var"))
          //@todo this is convoluted and inefficient compared to a direct forward proof
          else {
            val specialDvariable = TactixLibrary.proveBy(
              Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))),
              Dvariable(SuccPosition(0,0::Nil)) ~ byUS("= reflexive"))
            assert(specialDvariable.isProved && specialDvariable.proved==Sequent(Nil,IndexedSeq(), IndexedSeq(Equal(Differential(x), DifferentialSymbol(x)))), "Proved helper")
            useFor(
              specialDvariable,
              PosInExpr(0::Nil)
            )(SuccPosition(0,1::Nil))(de)
          }
        case e => throw new MatchError("derive(" + de.conclusion.succ.head.subAt(pos).prettyString + ") don't know how to handle " + e + " at " + pos + " of " + de.conclusion)
        }
        if (DEBUG) println("derive(" + de.conclusion.succ.head.subAt(pos).prettyString + ")\n ~~> " + r)
        r
      } ensuring(r => r.isProved, "derive remains proved: " + "derive(" + de.conclusion.succ.head(pos).prettyString + ")")

      /** Construct a proof proving the answer of the derivative of de expanded out to variables */
      private def deriveProofF(de: Formula): Provable = {
        val deIsDe = Sequent(Nil, IndexedSeq(), IndexedSeq(Equiv(de,de)))
        val initial = DerivedAxioms.equivReflexiveAxiom.fact(
          deIsDe,
          UniformSubstitutionRule(USubst(SubstitutionPair(PredOf(Function("p",None,Unit,Bool),Nothing), de)::Nil), DerivedAxioms.equivReflexiveAxiom.fact.conclusion))
        assert(initial.isProved && initial.proved==deIsDe, "Proved reflexive start " + initial + " for " + de)
        if (DEBUG) println("derive starts at " + initial)
        val r = deriveF(initial, PosInExpr(1::Nil))
        if (DEBUG) println("derive(" + de.prettyString + ") = ~~> " + r + " done")
        r
      } ensuring(r => r.isProved, "derive remains proved: " + " final derive(" + de + ")")

    private def deriveF(de: Provable, pos: PosInExpr): Provable = {
      if (DEBUG) println("derive(" + de.conclusion.succ.head.subAt(pos).prettyString + ")")
      def homomorphic(short: String, axiom: String): Provable = deriveF(deriveF(
        debugPF(short)(useFor(axiom))(SuccPosition(0,pos))(de),
        pos.append(PosInExpr(0::Nil))),
        pos.append(PosInExpr(1::Nil))
      )

      def pseudoHomomorphic(short: String, axiom: String): Provable = derive(derive(
        debugPF(short)(useFor(axiom))(SuccPosition(0,pos))(de),
        pos.append(PosInExpr(0::Nil))),
        pos.append(PosInExpr(1::Nil))
      )

      val r = de.conclusion.succ.head.subAt(pos) match {
        // homomorphic formulas
        case DifferentialFormula(And(_,_))   => homomorphic("derive(&')", "&' derive and")
        case DifferentialFormula(Or(_,_))    => homomorphic("derive(|')", "|' derive or")
        case DifferentialFormula(Imply(_,_)) => homomorphic("derive(->')", "->' derive imply")
        // pseudo-homomorphic cases
        case DifferentialFormula(Equal(_,_)) => pseudoHomomorphic("derive(=')", "=' derive =")
        case DifferentialFormula(NotEqual(_,_)) => pseudoHomomorphic("derive(!=')", "!=' derive !=")
        case DifferentialFormula(Greater(_,_)) => pseudoHomomorphic("derive(>')", ">' derive >")
        case DifferentialFormula(GreaterEqual(_,_)) => pseudoHomomorphic("derive(>=')", ">=' derive >=")
        case DifferentialFormula(Less(_,_)) => pseudoHomomorphic("derive(<')", "<' derive <")
        case DifferentialFormula(LessEqual(_,_)) => pseudoHomomorphic("derive(<=')", "<=' derive <=")
        case e => throw new MatchError("derive(" + de.conclusion.succ.head.subAt(pos).prettyString + ") don't know how to handle " + e + " at " + pos + " of " + de.conclusion)
      }
      if (DEBUG) println("derive(" + de.conclusion.succ.head.subAt(pos).prettyString + ")\n ~~> " + r)
      r
    } ensuring(r => r.isProved, "derive remains proved: " + "derive(" + de.conclusion.succ.head(pos).prettyString + ")")
  }
  } // derive

  private def useFor(axiom: String): (Position => (Provable => Provable)) = useFor(axiom, PosInExpr(0::Nil))

  private def useFor(axiom: String, key: PosInExpr): (Position => (Provable => Provable)) =
    if (Axiom.axioms.contains(axiom)) useFor(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(Axiom.axioms(axiom))))(Axiom(axiom), 0), key)
    else if (DerivedAxioms.derivedAxiomFormula(axiom).isDefined) useFor(Provable.startProof(Sequent(Nil, IndexedSeq(), IndexedSeq(DerivedAxioms.derivedAxiomFormula(axiom).get)))(DerivedAxioms.derivedAxiomR(axiom), 0), key)
    else throw new IllegalArgumentException("Unknown axiom " + axiom)

  //@todo in analogy to useAt but forward proof.
  /** useFor(axiom) use the given fact forward for the selected position in the given Provable to conclude a new Provable */
  private def useFor(fact: Provable, key: PosInExpr, inst: RenUSubst=>RenUSubst = (us => us)): (Position => (Provable => Provable)) = {
    import FormulaConverter._
    import SequentConverter._
    import TactixLibrary._
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
}