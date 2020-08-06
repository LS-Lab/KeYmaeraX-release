/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
/**
  * Proof data structures for Kaisar
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.btactics.Integrator
import edu.cmu.cs.ls.keymaerax.cdgl.Metric
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.VCP
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{SubstitutionHelper, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException

object KaisarProof {
  // Identifiers for  proof-variables. Source-level variables are typically alphabetic, elaboration can introduce
  // indices  <alpha><int>
  type Ident = Variable
  // Identifiers for line labels, which are typically alphabetic
  type TimeIdent = String
  type Statements = List[Statement]
  type Subscript = Option[Int]

  // Failures in proof transformation passes (as opposed to proof checking)
  case class TransformationException(msg: String) extends Exception(msg)
  // Failures in elaboration passes. Elaboration passes validate their inputs, while transformations assume correct input
  case class ElaborationException(msg: String) extends Exception(msg)


  // Kaisar extends the syntax of expressions with located expressions  f@L.
  // Rather than extend Expression,scala, we implement this as an interpreted function symbol at(f, L()) which
  // we elaborate to the core expression syntax
  // "init" is an example label-function which can be passed for the second argument of at()
  // In concrete proofs, the label function name is generated from; the labels in the proof.
  val at: Function = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
  val init: FuncOf = FuncOf(Function("init", domain = Unit, sort = Unit, interpreted = true), Nothing)
  // Stable is the counterpart to "at", which says that at(stable(x_i), L) should always be x_i
  val stable: Function = Function("stable", domain = Real, sort = Real, interpreted = true)
  def getAt(t: Term): Option[(Term, String)] = {
    t match {
      case FuncOf(Function("at", None, Tuple(Real, Unit), Real, true), Pair(e, FuncOf(Function(label, _, _, _, _),_))) =>
        Some(e, label)
      case _ => None
    }
  }
  def getStable(t: Term): Option[Term] = {
    t match {
      case FuncOf(Function("stable", None, Real, Real, true), e) => Some(e)
      case _ => None
    }
  }

  // Special functions max, min, and abs are already used in KeYmaera X, but are often used in Kaisar proofs as well
  val max: Function = Function("max", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val min: Function = Function("min", domain = Tuple(Real, Real), sort = Real, interpreted = true)
  val abs: Function = Function("abs", domain = Real, sort = Real, interpreted = true)
  val builtin: Set[Function] = Set(min, max, abs)

  // We reuse expression syntax for patterns over expressions. We use an interpreted function wild() for the wildcard
  // patttern "*" or "_". This is elaborated before proofchecking
  val wild: FuncOf = FuncOf(Function("wild", domain = Unit, sort = Unit, interpreted = true), Nothing)

  // Proof statement Block() sequences a list of statements. [[flatten]] flattens the tree structure induced by the
  // [[Block]] constructor.
  def flatten(ss: Statements): Statements = {
    ss match {
      case Block(ss) :: sss  => flatten(ss ++ sss)
      case Triv() :: ss => flatten(ss)
      case s :: ss => s :: flatten(ss)
      case Nil => Nil
    }
  }

  // smart constructor for [[Block]] which will [[flatten]] the tree structure
  def block(ss: Statements): Statement = {
    flatten(ss) match {
      case List() => Triv()
      case List(s) => s
      case ss => Block(ss)
    }
  }

  def ghost(s: Statement): Statement = {
    s match {
      case ProveODE(ds, dc) => ProveODE(DiffGhostStatement(ds), dc)
      case _ => Ghost(s)
    }
  }

  def inverseGhost(s: Statement): Statement = {
    s match {
      case ProveODE(ds, dc) => ProveODE(InverseDiffGhostStatement(ds), DomWeak(dc))
      case _ => InverseGhost(s)
    }
  }
}

// Umbrella trait for all syntactic classes of abstract syntax tree
sealed trait ASTNode {
  // Location in source file of connective which generated AST node.
  // Populated by parser and used to reconstruct error messages.
  var location: Option[Int] = None
  def setLocation(loc: Int): Unit = { location = Some(loc)}
}

//@TODO Eliminate: redundant with Block
final case class Proof(ss: List[Statement])

// A proof-method expresses a single step of unstructured heuristic proof,
// generally as justification of a single step of some structured proof.
// @TODO: case exhaustiveness checking method
sealed trait Method extends ASTNode { val selectors: List[Selector] = Nil}
// constructive real-closed field arithmetic
case class RCF() extends Method
// general-purpose auto heuristic
case class Auto() extends Method
// propositional steps
case class Prop() extends Method
// solve differential equation (can only be used in ODE)
case class Solution() extends Method
// differential induction (can only be used in ODE)
case class DiffInduction() extends Method
// introduce an assumption used in method
case class Using(use: List[Selector], method: Method) extends Method {override val selectors: List[Selector] = use ++ method.selectors}
// discharge goal with structured proof
case class ByProof(proof: Statements) extends Method

// Forward-chaining natural deduction proof term.
sealed trait ProofTerm extends ASTNode
// Hypothesis rule. Identifier x can be either a proof variable in the current context or a built-in natural-deduction
// rule from the CdGL proof calculus.
case class ProofVar(x: Ident) extends ProofTerm {}
// Looks up all assumptions corresponding to program variable
case class ProgramVar(x: Variable) extends ProofTerm {}

// Term used to instantiatiate a universal quantifier. Should only ever appear on the right-hand side of an application,
// but parsing is simpler when terms are a standalone constructor
case class ProofInstance(e: Expression) extends ProofTerm {}
// Given proof term m, supply n as an argument. Since n can be [[ProofInstance]], the same connective
// [[ProofApp]] supports both modus ponens and universal quantifier instantiation.
case class ProofApp(m: ProofTerm, n: ProofTerm) extends ProofTerm {}

// Selectors are used in unstructured proof step heuristics to indicate which facts should be supplied as hypotheses
// @TODO: Can this be flattened into proofTerm language?
sealed trait Selector extends ASTNode
// Select the result of some proof term, often but not need be a variable
case class ForwardSelector(forward: ProofTerm) extends Selector {}
// Select [[all]] elements of the context which unify with an expression
// @TODO: probably more useful to mean "all which contain e as a subexpression"
// @TODO: Makes early elaboration passes annoying, perhaps implement this later
case class PatternSelector(e: Expression) extends Selector {}
case object DefaultSelector extends Selector {}

// Pattern language for left-hand side of assignment proofs. Expressions are used for most patterns, but assignment
// patterns are not quite expressions because each assigned variable may introduce a proof variable.
sealed trait AsgnPat extends ASTNode {
  def boundFacts: Set[Variable] = {
    this match {
      case VarPat(x, Some(p)) => Set(p)
      case TuplePat(pats) => pats.map(_.boundFacts).reduce((l,r) => l.++(r))
      case _ => Set()
    }
  }
  def boundVars: Set[Variable] = {
    this match {
      case VarPat(x, p) => Set(x)
      case TuplePat(pats) => pats.map(_.boundVars).reduce((l,r) => l.++(r))
      case _ => Set()
    }
  }
}
case class NoPat() extends AsgnPat
// Wildcard pattern for ignored assignments
case class WildPat() extends AsgnPat
// Assign to variable and optionally store equation in a proof variable
case class VarPat(x: Variable, p: Option[Ident] = None) extends AsgnPat
// Assign elements of tuple according to each component pattern
case class TuplePat(pats: List[AsgnPat]) extends AsgnPat

/* Language of structured proofs. Statements are block-structu  red, so entire proofs are single statements */
sealed trait Statement extends ASTNode
// Proves nothing
case class Triv() extends Statement
// x is a formula pattern in assume and assert
// Assume introduces assumption that f is true, with name(s) given by pattern [[pat]]
case class Assume(pat: Expression, f: Formula) extends Statement
// Assertion proves formula f to be true with method m, then introduces it with name(s) given by pattern [[pat]]
case class Assert(pat: Expression, f: Formula, m: Method) extends Statement
// Modifies the variables specified by [[pat]] by executing [[hp]]. Pattern [[pat]] optionally specifies proof variable
// where equalities induced by assignments are stored. When [[hp==Left(f)]] the assignment is deterministic to term f,
// when [[hp==Right(())]] the assignment is nondeterministic
case class Modify(pat: AsgnPat, hp: Either[Term, Unit]) extends Statement
// Introduces a line label [[st]]. Terms f@st (likewise formulas) are then equal to the value of f at the location of
// [[Label(st)]]. Labels are globally scoped with forward and backward reference, but references must be acyclic
// for well-definedness
// @TODO: Implement
case class Label(st: TimeIdent, snapshot: Option[Snapshot] = None) extends Statement
// Note checks forward [[proof]] and stores the result in proof-variable [[x]]
// In the source syntax, the [[fml]] formula is usually omitted because it can be inferred, but is populated during
// elaboration for performance reasons
// @TODO: x should be Expression for pattern fun
case class Note(x: Ident, proof: ProofTerm, var annotation: Option[Formula] = None) extends Statement
// Introduces a lexically-scoped defined function [[x]] with arguments [[args]] and body [[e]]. References to [[args]]
// in [[e]] are resolved by substituting parameters at application sites. All others take their value according to the
// definition site of the function. Scope is lexical and functions must not be recursive for soundness.
case class  LetFun(f: Ident, args: List[Ident], e: Expression) extends Statement {
  val asFunction: Function = Function(f.name, domain = args.map(_ => Real).reduceRight(Tuple), sort = Real)
}
// Unifies expression [[e]] with pattern [[pat]], binding free term and formula variables of [[pat]]
case class Match(pat: Expression, e: Expression) extends Statement
// Sequential composition of elements of [[ss]]
case class Block(ss: Statements) extends Statement
// Pattern formulas must form a constructively-exhaustive case analysis.
// To support cases where exhaustiveness is nonobvious, an optional scrutinee can be provided, in which case the branches
// of the switch must be the branches of the scrutinee formula.
// In each branch, bind a variable pattern to an assumption expression and prove the branch statement
// the conclusion is the disjunction of branches
case class Switch(scrutinee: Option[Selector], pats: List[(Expression, Expression, Statement)]) extends Statement
// Execute either branch of a program nondeterministically, with corresponding proofs
case class BoxChoice(left: Statement, right: Statement) extends Statement
// x is a pattern
// Repeat body statement [[ss]] so long as [[j]] holds, with hypotheses in pattern [[x]]
case class While(x: Expression, j: Formula, s: Statement) extends Statement
// Repeat [[s]] nondeterministically any number of times
case class BoxLoop(s: Statement, ih: Option[(Ident, Formula)] = None) extends Statement
// Statement [[s]] is introduced for use in the proof but is not exported in the conclusion.
// For example, Ghost(Modify(_)) is a discrete ghost assignment
// @TODO: Resolve scope-escaping issues
case class Ghost(s: Statement) extends Statement
// Inverse-ghost of statement [[s]], i.e., program of [[ss]] is part of the conclusion but not relevant to the proof.
// For example, InverseGhost(Assume(_)) indicates a Demonic test which is never used in the proof
case class InverseGhost(s: Statement) extends Statement
// Proof of differential equation, either angelic or demonic.
case class ProveODE(ds: DiffStatement, dc: DomainStatement) extends Statement {
  lazy val solutions: Option[List[(Variable, Term)]] = {
    // @TODO: Duration in sols
    if (timeVar.isEmpty) None
    else {
      val ode = asODESystem
      // @TODO: Support arbitrary xys?
      val xys: Set[(BaseVariable, BaseVariable)] =
        StaticSemantics(ode).bv.toSet.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable]).map(x => (x -> x))
      val solutions = Integrator(xys.toMap, timeVar.get, ode)
      Some(solutions.map({ case Equal(x: Variable, f) => (x, f) case p => throw ProofCheckException(s"Solve expected $p to have shape x=f") }))
    }
  }

  // Note we may want a default variable like "t" if timeVar is none, but freshness checks need a context, not just the ODE.
  lazy val timeVar: Option[Variable] = {
    duration match {
      case Some((x, f)) => Some(x)
      case None => ds.clocks.toList match {
        case v :: Nil => Some(v)
        case _ => None
      }
    }
  }


  lazy val asODESystem: ODESystem = {
    ODESystem(ds.asDifferentialProgram(modifier))
  }

  lazy val isAngelic: Boolean = modifier.isDefined
  lazy val modifier: Option[DomModify] = {
    dc.modifier
  }

  lazy val duration: Option[(Variable, Term)] = {
    modifier.flatMap({case DomModify(VarPat(x, _), f) => Some(x, f) case _ => None})
  }

  lazy val conclusion: Formula = {
    val odeSystem = asODESystem
    val odeBV = StaticSemantics(odeSystem).bv
    modifier.foreach(dm =>
      if(!odeBV.contains(dm.x.boundVars.toList.head))
        throw ProofCheckException("ODE duration variable must be bound in ODE"))
    val hp = modifier.map(dm => Compose(odeSystem, Test(dm.asEquals))).getOrElse(odeSystem)
    if (modifier.nonEmpty) {
      Box(Dual(hp), True)
    } else {
      Box(hp, True)
    }
  }
} //de: DifferentialProgram

// Statements which "just" attach metadata to their underlying nodes and don't change computational meaning
sealed trait MetaNode extends Statement {
  val children: List[Statement] = Nil
}

// Debugging functionality: print [[msg]] with proof context
case class PrintGoal(msg: String) extends MetaNode {
  override val children: List[Statement] = Nil
}
// Debugging feature. Equivalent to "now" in all respects, annotated with the fact that it was once "was"
// before transformation by the proof checker
case class Was(now: Statement, was: Statement) extends MetaNode {
  override val children: List[Statement] = List(now)
}

// A sequence of assignments used as phi-node in static single assignment form
case class Phi(asgns: Statement) extends MetaNode {
  override val children: List[Statement] = List(asgns)
  private def toMap(s: Statement, reverse: Boolean): Map[Variable, Variable] = {
    s match {
      case Block(ss) => ss.map(toMap(_, reverse)).foldLeft[Map[Variable, Variable]](Map())(_ ++ _)
      case Modify(VarPat(x1, _), Left(x2: Variable)) => if (reverse) Map(x2 -> x1) else Map(x1 -> x2)
    }
  }
  def forwardMap:Map[Variable, Variable] = toMap(asgns, reverse = false)
  def reverseMap:Map[Variable, Variable] = toMap(asgns, reverse = true)
}

// This is a meta node because it's only used in contexts while checking the interior of a loop.
// It helps us handle variable admissibility/renaming for loops, especially for accessing the IH.
// boxLoop is the entire loop, progress contains the prefix of the body checked so far, and IH is the name of
// the inductive hypothesis
case class BoxLoopProgress(boxLoop: BoxLoop, progress: Statement) extends MetaNode {
  override val children: List[Statement] = List(block(boxLoop :: progress :: Nil))
}

final case class DomCollection(assumptions: Set[DomAssume], assertions: Set[DomAssert],  weakens: Set[DomainStatement], modifiers: Set[DomModify])
final case class DiffCollection(atoms: Set[AtomicODEStatement], ghosts: Set[AtomicODEStatement], inverseGhosts: Set[AtomicODEStatement])

// Proof steps regarding the differential program, such as ghosts and inverse ghosts used in solutions.
sealed trait DiffStatement extends ASTNode {
  private def getDifferentialProgram(mod: Option[DomModify]): Option[DifferentialProgram] = {
    this match {
      case AtomicODEStatement(dp) =>
        (mod, dp.e) match {
          case (Some(DomModify(VarPat(durvar, _), _)), Number(n)) if (dp.xp.x == durvar && n.toInt == 1) => ()
          case (Some(DomModify(VarPat(durvar, _), _)), rhs) if (dp.xp.x == durvar) =>
            throw ProofCheckException(s"ODE duration variable/clock $durvar must change at rate 1, got $rhs")
          case _ => ()
        }
        Some(dp)
      case DiffProductStatement(l, r) =>
        (l.getDifferentialProgram(mod), r.getDifferentialProgram(mod)) match {
          case (Some(l), Some(r)) => Some(DifferentialProduct(l, r))
          case (None, r) => r
          case (l, None) => l
        }
      case InverseDiffGhostStatement(ds) => ds.getDifferentialProgram(mod)
      case DiffGhostStatement(ds) => None
    }
  }

  def asDifferentialProgram(mod: Option[DomModify]): DifferentialProgram = {
    val x = DifferentialSymbol(BaseVariable("dummy"))
    getDifferentialProgram(mod).getOrElse(AtomicODE(x, Number(0)))
  }

  lazy val clocks: Set[Variable] = {
    this match {
      case AtomicODEStatement(AtomicODE(DifferentialSymbol(x), rhs: Number)) if rhs.value.toInt == 1 => Set(x)
      case _: AtomicODEStatement => Set()
      case DiffProductStatement(l, r) => l.clocks ++ r.clocks
      // since it's common to ghost in clock variables, we probably want this.
      case DiffGhostStatement(ds) => ds.clocks
      case InverseDiffGhostStatement(ds) => Set()
    }
  }

  def atoms: Set[AtomicODEStatement] = collect.atoms

  /** @return collection (nonGhosts, forwardGhosts, inverseGhosts) of statements in [[statement]]*/
  lazy val collect: DiffCollection = {
    this match {
      case st: AtomicODEStatement => DiffCollection(Set(st), Set(), Set())
      case DiffProductStatement(l, r) =>
        val DiffCollection(a1, b1, c1) = l.collect
        val DiffCollection(a2, b2, c2) = r.collect
        DiffCollection(a1.++(a2), b1.++(b2), c1.++(c2))
      case DiffGhostStatement(ds) =>
        val DiffCollection(a, b, c) = ds.collect
        DiffCollection(Set(), a.++(b).++(c), Set())
      case InverseDiffGhostStatement(ds) =>
        val DiffCollection(a, b, c) = ds.collect
        DiffCollection(Set(), Set(), a.++(b).++(c))
    }
  }
}

// Specifies a single ODE being proved
case class AtomicODEStatement(dp: AtomicODE) extends DiffStatement
// Corresponding proofs for each conjunct of differential product
case class DiffProductStatement(l: DiffStatement, r: DiffStatement) extends DiffStatement
// Proof for ghost ODE introduced for sake of proof but not in conclusion
case class DiffGhostStatement(ds: DiffStatement) extends DiffStatement
// Proof for inverse ghost ODE which appears in conclusion but not proof. Used in solution reasoning.
case class InverseDiffGhostStatement(ds: DiffStatement) extends DiffStatement

//Proof steps regarding the domain, for example differential cuts and weakening of domain constraints.
// Angelic solutions require witnesses for duration, also given here
sealed trait DomainStatement extends ASTNode {
  def asFormula(isAngelic: Boolean): Option[Formula] = {
    this match {
      case DomAssume(x, f) => Some(f)
      case DomAssert(x, f, child) if (isAngelic) => Some(f)
      case DomAssert(x, f, child) => None
      case DomModify(x, f) => None
      case DomWeak(dc) => dc.asFormula(isAngelic)
      case DomAnd(l, r) =>
        (l.asFormula(isAngelic), r.asFormula(isAngelic)) match {
          case (Some(l), Some(r)) => Some(And(l, r))
          case (None, r) => r
          case (l, None) => l
        }
    }
  }

  def isAssertive: Boolean = {
    this match {
      case DomAssert(x, f, child) => true
      case DomAnd(l, r) => l.isAssertive && r.isAssertive
      case _ => false
    }
  }

  def modifier: Option[DomModify] = {
    this match {
      case dm: DomModify =>Some(dm)
      case DomAnd(l, r) =>
        (l.modifier, r.modifier) match {
          case (Some(x), Some(y)) => throw ProofCheckException("ODE should only have one duration statement")
          case (None, r) => r
          case (l, None) => l
        }
      case _: DomWeak | _: DomAssume | _: DomAssert => None
    }
  }

  lazy val collect: DomCollection = {
    this match {
      case da: DomAssume => DomCollection(Set(da), Set(), Set(), Set())
      case da: DomAssert => DomCollection(Set(), Set(da), Set(), Set())
      case DomWeak(dw) =>
        val DomCollection(a, b, c, d) = dw.collect
        DomCollection(Set(), Set(), a.++(b).++(c), d)
      case dm: DomModify => DomCollection(Set(), Set(), Set(), Set(dm))
      case DomAnd(l, r) =>
        val DomCollection(a1, b1, c1, d1) = l.collect
        val DomCollection(a2, b2, c2, d2) = r.collect
        DomCollection(a1.++(a2), b1.++(b2), c1.++(c2), d1.++(d2))
    }
  }

  lazy val demonFormula: Option[Formula] = asFormula(isAngelic = false)
  lazy val angelFormula: Option[Formula] = asFormula(isAngelic = true)
}
// x is formula pattern in assume and assert
// Introduces assumption in domain, i.e., a domain formula which appears in the conclusion and can be accessed
// by differential weakening
case class DomAssume(x: Expression, f:Formula) extends DomainStatement
// Differential assertion which is proved with differential cut and then possibly used in proof
case class DomAssert(x: Expression, f:Formula, child: Method) extends DomainStatement
// Distinct from "differential weakening" rule, meaning a domain constraint which is in the conclusion but not the
// proof, which is weakened before continuing proof
case class DomWeak(dc: DomainStatement) extends DomainStatement
// Assignment to a variable. Only allowable use is to specify the duration of an angelic solution
case class DomModify(x: AsgnPat, f: Term) extends DomainStatement {
  lazy val asEquals: Equal = {
    val (DomModify(VarPat(x, _), e)) = this
    Equal(x, e)
  }
}
// Conjunction of domain constraints with proofs for each conjunct
case class DomAnd(l: DomainStatement, r: DomainStatement) extends DomainStatement