/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Proof data structures for Kaisar
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import KaisarProof._
import edu.cmu.cs.ls.keymaerax.btactics.Integrator
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, FormulaTools, PosInExpr}
import fastparse.Parsed.{Failure, TracedFailure}
import StandardLibrary._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols

object KaisarProof {
  // Identifiers for  proof-variables. Source-level variables are typically alphabetic, elaboration can introduce
  // indices  <alpha><int>
  type Ident = Variable
  // Identifiers for line labels, which are typically alphabetic
  type TimeIdent = String
  // Terms are used as patterns for left-hand sides of bindings:
  //   Nothing -> no binding
  //   Variable/Ident -> Bind one fact
  //   Pair(v1, ... Pair(vn, Nothing)) -> pattern-match fact (p1 & ... pn) and bind vi -> pi
  //   FuncOf(id: Real -> Real, (arg: Real)) -> represents a universally quantified fact which can be instantiated by plugging in different args
  type IdentPat = Term
  type Statements = List[Statement]
  type Subscript = Option[Int]

  object IdentPat {
    def apply(v: Option[Variable]): IdentPat = v.getOrElse(Nothing)
  }

  case class LabelDef(label: TimeIdent, args: List[Variable] = Nil)
  case class LabelRef(label: TimeIdent, args: List[Term] = Nil) {
    def prettyString: String = label + (if (args.isEmpty) "" else "(" + args.mkString(",") + ")")
  }

  abstract class LocatedException(val msg: String = "", val cause: Throwable = null) extends Exception(msg, cause) {
    def location: Option[Int]
  }

  class NodeException(override val msg: String = "", override val cause: Throwable = null)
      extends LocatedException(msg, cause) {
    val node: ASTNode = Triv()
    def location: Option[Int] = node.location
    override def toString: String =
      if (cause == null) { s"NodeException($msg)" }
      else { s"NodeException($msg), cause ${cause}" }
  }
  case class ProofCheckException(
      override val msg: String,
      override val cause: Throwable = null,
      override val node: ASTNode = Triv(),
  ) extends NodeException(msg, cause) {
    override def toString: String = msg
  }

  // Failures in proof transformation passes (as opposed to proof checking)
  case class TransformationException(override val msg: String, override val node: ASTNode = Triv())
      extends NodeException(msg)
  // Failures in elaboration passes. Elaboration passes validate their inputs, while transformations assume correct input
  case class ElaborationException(override val msg: String, override val node: ASTNode = Triv())
      extends NodeException(msg)
  case class ODEAdmissibilityException(vars: Set[Variable], override val node: ASTNode = Triv())
      extends NodeException(s"Differential equation proof must be in SSA form, else variables ($vars) escape scope")
  case class KaisarParseException(
      override val msg: String = "",
      trace: Option[TracedFailure] = None,
      override val location: Option[Int],
      source: String,
  ) extends LocatedException(
        if (trace.isEmpty) "KaisarParseException" else KaisarProgramParser.recoverErrorMessage(trace.get)
      ) {
    override def toString: String = {
      val msgMsg = trace
        .map(tr => {
          val expectation = KaisarProgramParser.expectation(tr)
          // note: if statement may not be strictly necessary, written this way to match fastparse code as closely as possible
          val input = if (tr.label == "") tr.failure.extra.input else tr.input
          "Found " + Failure.formatTrailing(input, tr.index) + " at position " +
            tr.failure.extra.input.prettyIndex(tr.index) + s"(${tr.index})" + "\nExpected " + expectation
        })
        .getOrElse("")
      s"Parse error: $msgMsg"
    }
  }

  // Kaisar extends the syntax of expressions with located expressions  f@L.
  // Rather than extend Expression,scala, we implement this as an interpreted function symbol at(f, L()) which
  // we elaborate to the core expression syntax
  // "init" is an example label-function which can be passed for the second argument of at()
  // In concrete proofs, the label function name is generated from; the labels in the proof.
  val at: Function = Function("at", domain = Tuple(Real, Unit), sort = Real, interp = None)
  val init: FuncOf = FuncOf(Function("init", domain = Unit, sort = Unit, interp = None), Nothing)
  // Stable is the counterpart to "at", which says that at(stable(x_i), L) should always be x_i
  val stable: Function = Function("stable", domain = Real, sort = Real, interp = None)

  // Construct a located term f@L
  def makeAt(f: Term, lr: LabelRef): Term = {
    val labelFun = FuncOf(Function(lr.label, None, rN(lr.args.length), Unit, interp = None), termsToTuple(lr.args))
    FuncOf(at, Pair(f, labelFun))
  }

  def makeAt(f: Formula, lr: LabelRef): Formula = {
    val labelFml = PredOf(Function(lr.label, None, rN(lr.args.length), Bool, interp = None), termsToTuple(lr.args))
    PredicationalOf(Function("at", None, Bool, Bool), And(f, labelFml))
  }

  // Pattern match a located term  f@L
  def getAt(t: Term, node: ASTNode = Triv()): Option[(Term, LabelRef)] = {
    t match {
      case FuncOf(
            Function("at", _index, _domain, _sort, interp @ None),
            Pair(e, FuncOf(Function(label, _, _, _, _), args)),
          ) => Some(e, LabelRef(label, tupleToTerms(args, node)))
      case _ => None
    }
  }

  def getAt(t: Formula, node: ASTNode): Option[(Formula, LabelRef)] = {
    t match {
      // predicationals always uninterpreted
      // TODO: ???^
      case PredicationalOf(
            Function("at", _index, _domain, _sort, interp @ None),
            And(e, PredOf(Function(label, _, _, _, _), args)),
          ) => Some(e, LabelRef(label, tupleToTerms(args, node)))
      case _ => None
    }
  }

  private val forgetTF = new ExpressionTraversalFunction {
    override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = {
      getAt(e, Triv()) match {
        case Some((f, _)) => Right(f)
        case None => Left(None)
      }
    }
    override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = {
      getAt(e) match {
        case Some((f, _)) => Right(f)
        case None => Left(None)
      }
    }
  }

  // This is usually not what you want. Totally forgets @ exists, rather than expanding @.
  def forgetAt(e: Term): Term = ExpressionTraversal.traverse(forgetTF, e).getOrElse(e)
  def forgetAt(e: Formula): Formula = ExpressionTraversal.traverse(forgetTF, e) match {
    case Some(z) => z
    case None => e
  }

  // Pattern match a stabilized term stable(f)
  def getStable(t: Term): Option[Term] = {
    t match {
      case FuncOf(f, e) if f == stable => Some(e)
      case _ => None
    }
  }

  // Special functions max, min, and abs are already used in KeYmaera X, but are often used in Kaisar proofs as well
  val max: Function = InterpretedSymbols.maxF
  val min: Function = InterpretedSymbols.minF
  val abs: Function = InterpretedSymbols.absF

  // We reuse expression syntax for patterns over expressions. We use an interpreted function wild() for the wildcard
  // patttern "*" or "_". This is elaborated before proofchecking
  val wild: FuncOf = FuncOf(Function("wild", domain = Unit, sort = Unit, interp = None), Nothing)

  /**
   * [[askLaterT]] is strictly used in the internal representation. If a term cannot be elaborated until a later
   * proof-checking pass, then symbol [[askLaterT]] is used to represent a dummy term
   */
  val askLaterTF: Function = Function("askLater", domain = Unit, sort = Real, interp = None)
  val askLaterPF: Function = Function("askLater", domain = Unit, sort = Bool, interp = None)
  val askLaterT: FuncOf = FuncOf(askLaterTF, Nothing)
  val askLaterP: PredOf = PredOf(askLaterPF, Nothing)
  val builtin: Set[Function] = Set(min, max, abs, askLaterTF, askLaterPF, wild.func, init.func, stable, at)

  def isBuiltinFunction(f: Function): Boolean = builtin.contains(f)
  def getBuiltin(f: String): Option[Function] = builtin.find(func => func.name == f)

  // Proof statement Block() sequences a list of statements. [[flatten]] flattens the tree structure induced by the
  // [[Block]] constructor.
  def flatten(ss: Statements): Statements = {
    ss match {
      case Block(ss) :: sss => flatten(ss ++ sss)
      case Triv() :: ss => flatten(ss)
      case s :: ss => s :: flatten(ss)
      case Nil => Nil
    }
  }

  // smart constructor for [[Block]] which will [[flatten]] the tree structure
  def block(ss: Statements): Statement = {
    val flat = flatten(ss)
    val located = flat.find(_.location.isDefined).getOrElse(Triv())
    flat match {
      case List() => Triv()
      case List(s) => s
      case ss => ASTNode.locate(Block(ss), located)
    }
  }

  // Smart constructor for ghosts: ODE vs discrete ghosts
  def ghost(s: Statement): Statement = {
    s match {
      case ProveODE(ds, dc) => ProveODE(DiffGhostStatement(ds), dc)
      case _ => Ghost(s)
    }
  }

  // Smart constructor for inverse ghosts: ODE vs discrete ghosts
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
  def setLocation(loc: Int): Unit = { location = Some(loc) }
}
object ASTNode {
  def locate[T <: ASTNode](x: T, other: ASTNode): T = {
    val theLocation: Option[Int] = if (x.location.isDefined) x.location else other.location
    if (theLocation.isDefined) x.setLocation(theLocation.get)
    x
  }
}

// A proof-method expresses a single step of unstructured heuristic proof,
// generally as justification of a single step of some structured proof.
sealed trait Method extends ASTNode {
  val selectors: List[Selector] = Nil
  val atom: Method = this
}
// constructive real-closed field arithmetic
case class RCF() extends Method
// general-purpose auto heuristic
case class Auto() extends Method
// propositional steps
case class Prop() extends Method
// solve differential equation (can only be used in ODE)
case class Solution() extends Method
// Hypothesis rule looks up in context
case class Hypothesis() extends Method
// differential induction (can only be used in ODE)
case class DiffInduction() extends Method
// check whether conclusion is an exhaustive disjunction for case analysis
case class Exhaustive() extends Method
// introduce an assumption used in method
case class Using(use: List[Selector], method: Method) extends Method {
  override val selectors: List[Selector] = use ++ method.selectors
  override val atom: Method = method.atom
}
// discharge goal with structured proof
case class ByProof(proof: Statements) extends Method
// for loop guard termination facts. delta is the comparison delta
case class GuardDone(delta: Option[Term]) extends Method

// Forward-chaining natural deduction proof term.
sealed trait ProofTerm extends ASTNode {
  def freeProofVars: List[Ident] = {
    this match {
      case ProofVar(id) => List(id)
      case ProofApp(m, n) => m.freeProofVars ++ n.freeProofVars
      case _ => List()
    }
  }
}
// Hypothesis rule. Identifier x can be either a proof variable in the current context or a built-in natural-deduction
// rule from the CdGL proof calculus.
case class ProofVar(x: Ident) extends ProofTerm {}
// Looks up all assumptions corresponding to program variable
case class ProgramVar(x: Variable) extends ProofTerm {}
// Looks up assignments corresponding to a program variable
case class ProgramAssignments(x: Variable, onlySSA: Boolean = false) extends ProofTerm {}

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
case class PatternSelector(e: Term) extends Selector {}
// Heuristically selects assumptions which mention variables that the goal also mentions.
case object DefaultSelector extends Selector {}
case object DefaultAssignmentSelector extends Selector {}

// Pattern language for left-hand side of assignment proofs. Expressions are used for most patterns, but assignment
// patterns are not quite expressions because each assigned variable may introduce a proof variable.
sealed trait AsgnPat extends ASTNode {
  def boundFacts: Set[Variable] = {
    this match {
      case VarPat(x, Some(p)) => Set(p)
      case TuplePat(pats) => pats.map(_.boundFacts).reduce((l, r) => l.++(r))
      case _ => Set()
    }
  }
  def boundVars: Set[Variable] = {
    this match {
      case VarPat(x, p) => Set(x)
      case TuplePat(pats) => pats.map(_.boundVars).reduce((l, r) => l.++(r))
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
// Pat: IdentPat is pattern that binds zero, one, or many facts
// Assume introduces assumption that f is true, with name(s) given by pattern [[pat]]
case class Assume(pat: IdentPat, f: Formula) extends Statement
// Assertion proves formula f to be true with method m, then introduces it with name(s) given by pattern [[pat]]
case class Assert(pat: IdentPat, f: Formula, m: Method) extends Statement
// Modifies the variables specified by [[ids]] by executing [[mods]]. List [[ids]] optionally specifies proof variable(s)
// where equalities induced by assignments are stored. When [[mod==Some(f)]] the assignment is deterministic to term f,
// when [[mod==None]] the assignment is nondeterministic
case class Modify(ids: List[Ident], mods: List[(Variable, Option[Term])]) extends Statement {
  val mod = this
  if (ids.length > 1 && ids.length != mods.length) throw new NodeException(
    "Modify statement should have one fact name for each assignment or one fact name for the entire block"
  ) {
    override val node: ASTNode = mod
  }

  def boundVars: Set[Variable] = mods.map(_._1).toSet
  def freeVars: Set[Variable] = mods.map({ case (x, f) => StaticSemantics(f.getOrElse(Nothing)).toSet }).reduce(_ ++ _)

  def asgns: List[(Option[Ident], Variable, Option[Term])] = ids match {
    case Nil => mods.map({ case (x, f) => (None, x, f) })
    case id :: Nil => mods.map({ case (x, f) => (Some(id), x, f) })
    case _ => zip3(ids.map(Some(_)), mods.map(_._1), mods.map(_._2), this)
  }
}
object Modify {
  def apply(dm: DomModify): Modify = {
    val ids = dm.id match {
      case Nothing => Nil
      case x: Variable => List(x)
      case _ => throw ProofCheckException("DomModify has unexpected identifier: " + dm.id)
    }
    Modify(ids, (dm.x, Some(dm.f)) :: Nil)
  }
  def apply(lst: List[(Option[Ident], Variable, Option[Term])]): Modify = {
    val (a, b, c) = unzip3(lst)
    Modify(a.filter(_.isDefined).map(_.get), b.zip(c))
  }
}

// Introduces a line label [[st]]. Terms f@st (likewise formulas) are then equal to the value of f at the location of
// [[Label(st)]]. Labels are globally scoped with forward and backward reference, but references must be acyclic
// for well-definedness
case class Label(st: LabelDef, snapshot: Option[Snapshot] = None) extends Statement
// Note checks forward [[proof]] and stores the result in proof-variable [[x]]
// In the source syntax, the [[fml]] formula is usually omitted because it can be inferred, but is populated during
// elaboration for performance reasons
// @TODO: x should be Expression for pattern fun
case class Note(x: Ident, proof: ProofTerm, var annotation: Option[Formula] = None) extends Statement
// Introduces a lexically-scoped defined function or predicate [[x]] with arguments [[args]] and body [[e]]. References to [[args]]
// in [[e]] are resolved by substituting parameters at application sites. All others take their value according to the
// definition site of the function/predicate. Scope is lexical and functions/predicates must not be recursive for soundness.
case class LetSym(f: Ident, args: List[Ident], e: Expression) extends Statement {
  val isFunction: Boolean = e.isInstanceOf[Term]
  val isPredicate: Boolean = !isFunction
  val returnSort: Sort = if (isFunction) Real else Bool
  private def nsort(sorts: List[Sort]): Sort = sorts match {
    case Nil => Unit
    case _ => sorts.reduceRight[Sort](Tuple)
  }
  val asFunction: Function = Function(f.name, domain = nsort(args.map(_ => Real)), sort = returnSort)
}
// Unifies expression [[e]] with pattern [[pat]], binding free term and formula variables of [[pat]]
case class Match(pat: Term, e: Expression) extends Statement
// Sequential composition of elements of [[ss]]
case class Block(ss: Statements) extends Statement
// Pattern formulas must form a constructively-exhaustive case analysis.
// To support cases where exhaustiveness is nonobvious, an optional scrutinee can be provided, in which case the branches
// of the switch must be the branches of the scrutinee formula.
// In each branch, bind a variable pattern to an assumption expression and prove the branch statement
// the conclusion is the disjunction of branches
case class Switch(scrutinee: Option[Selector], pats: List[(IdentPat, Formula, Statement)]) extends Statement
// Execute either branch of a program nondeterministically, with corresponding proofs
case class BoxChoice(left: Statement, right: Statement) extends Statement
/* Canonical usage of for loops has form

   for(metX := met0; !conv; ?(met <cmp> metFinal)); metX := metIncr) {
     body
   }
   where body also ends with  !conv;
   and where metX is not bound in body.
   @TODO: allow ghosting metX away with syntax  /-- metX := metF --/
   For loops encode Angelic loop convergence proofs.
   Every for loop has initial value, guard, and increment, but convergence predicate is optional.
   @TODO: Decide whether conv option needed, whether it should contain elaborated fml, whether  constructors can be further combined + simplified
   = or := syntax
 */

sealed trait Metric {

  /** Optional formula which must be proved for soundness in order for metric to be well-founded */
  def sideCondition: Option[Formula] = None

  /** Whether loop makes its progress by increasing value */
  def isIncreasing: Boolean

  /** Amount which metric increases each iteration. Positive for increasing loop, negative for decreasing loop */
  def delta: Term

  /** Value at which metric terminates */
  def bound: Term

  /** Formula which holds once the loop has terminated, in term of the changing loop index variable */
}

object Metric {
  def weakNegation(guard: Formula, delta: Term): Formula = {
    guard match {
      case And(l, r) => Or(weakNegation(l, delta), weakNegation(r, delta))
      case Or(l, r) => And(weakNegation(l, delta), weakNegation(r, delta))
      case Less(l, r) => Greater(l, Minus(r, delta))
      case LessEqual(l, r) => GreaterEqual(l, Minus(r, delta))
      case Greater(l, r) => Less(l, Plus(r, delta))
      case GreaterEqual(l, r) => LessEqual(l, Plus(r, delta))
    }
  }

  /**
   * @return
   *   A termination bound and flag indicating whether loop increases vs decreases
   * @throws MatchError
   *   If this conjunct is not a loop bound
   */
  private def conjunctBound(mvar: Variable): PartialFunction[Formula, (Term, Boolean)] = {
    case (Greater(x, lim)) if x == mvar => ((lim, false))
    case (GreaterEqual(x, lim)) if x == mvar => ((lim, false))
    case (Less(lim, x)) if x == mvar => ((lim, false))
    case (LessEqual(lim, x)) if x == mvar => ((lim, false))
    case (Greater(lim, x)) if x == mvar => ((lim, true))
    case (GreaterEqual(lim, x)) if x == mvar => ((lim, true))
    case (Less(x, lim)) if x == mvar => ((lim, true))
    case (LessEqual(x, lim)) if x == mvar => ((lim, true))
  }

  /**
   * @param guard
   *   can be a conjunction of guard conditions, only one has to be the bound
   * @return
   *   termination bound and flag to indicate whether loop index increases or decreases. None if guard is not found.
   */
  def guardBound(mvar: Variable, guard: Formula): Option[(Term, Boolean)] = {
    val cnjs = FormulaTools.conjuncts(guard)
    cnjs.collectFirst(conjunctBound(mvar))
  }

  /**
   * @param mvar
   *   loop index variable
   * @param increment
   *   term which increments/decrements index variable at each iteration
   * @param guard
   *   guard formula of loop termination condition
   * @param taboos
   *   variables bound during loop body which are taboo in loop init, increment
   * @return
   *   Loop termination metric if well-founded
   * @throws ProofCheckException
   *   if termination metric ill-founded
   */
  def apply(mvar: Variable, increment: Term, guard: Formula, taboos: Set[Variable]): Metric = {
    (increment, guardBound(mvar, guard)) match {
      case (_, None) => throw ProofCheckException(
          "Could not construct metric, guard " + guard +
            " did not mention index variable or did not indicate loop bound"
        )
      case (Plus(y, ny: Number), Some((bnd: Number, true))) if ny.value != 0 && y == mvar => LiteralMetric(ny, bnd)
      case (Minus(y, ny: Number), Some((bnd: Number, false))) if ny.value != 0 && y == mvar =>
        LiteralMetric(Number(-ny.value), bnd)
      case (Plus(y, ny: Number), Some((bnd: Number, _))) => throw ProofCheckException(
          "Could not construct metric, direction of guard condition and increment statement disagree"
        )
      case (Minus(y, ny: Number), Some((bnd: Number, _))) => throw ProofCheckException(
          "Could not construct metric, direction of guard condition and increment statement disagree"
        )
      case (Plus(y, ey), Some((bnd, dir)))
          if StaticSemantics(ey).intersect(taboos).isEmpty => // constant throughout loop
        ProvablyConstantMetric(ey, bnd, dir, taboos)
      case _ => throw ProofCheckException(
          "For loop only supports loops which increment by provably constant value metric := metric + c; non-literal increments must be positive"
        )
    }
  }
}

// @TODO: [low priority] Allow lexicographic metrics or other fancy metrics
case class LiteralMetric(override val delta: Number, override val bound: Number) extends Metric {
  if (delta.value == 0) throw ProofCheckException("Ill-founded metric with increment of 0")
  override def isIncreasing: Boolean = delta.value > 0
}

case class ProvablyConstantMetric(
    override val delta: Term,
    override val bound: Term,
    override val isIncreasing: Boolean,
    taboos: Set[Variable],
) extends Metric {
  if (!StaticSemantics(delta).intersect(taboos).isEmpty)
    throw ProofCheckException(s"Termination metric increment $delta not guaranteed to be constant")
  if (!StaticSemantics(bound).intersect(taboos).isEmpty)
    throw ProofCheckException(s"Termination metric bound $bound not guaranteed to be constant")
  override def sideCondition: Option[Formula] = {
    Some(if (isIncreasing) Greater(delta, Number(0)) else Less(delta, Number(0)))
  }
}

// guardDelta is the precision used for the comparison in the guard.
// Can be explicitly specified immediately after loop, in an assert
//   !(foo >= bar) by guard(delta);  else can try to infer with ... by guard;.
//   guardEpsilon is None initially
// and should not be changed once set to Some(delta)
case class For(
    metX: Ident,
    met0: Term,
    metIncr: Term,
    conv: Option[Assert],
    guard: Assume,
    body: Statement,
    var guardDelta: Option[Term] = None,
) extends Statement
// @TODO: Possibly delete once for loops are supported.
// x is an identifier  pattern
// Repeat body statement [[ss]] so long as [[j]] holds, with hypotheses in pattern [[x]]
case class While(x: IdentPat, j: Formula, s: Statement) extends Statement

// Repeat [[s]] nondeterministically any number of times
case class BoxLoop(s: Statement, ih: Option[(IdentPat, Formula, Option[Formula])] = None) extends Statement
// Statement [[s]] is introduced for use in the proof but is not exported in the conclusion.
// For example, Ghost(Modify(_)) is a discrete ghost assignment
case class Ghost(s: Statement) extends Statement
// Inverse-ghost of statement [[s]], i.e., program of [[ss]] is part of the conclusion but not relevant to the proof.
// For example, InverseGhost(Assume(_)) indicates a Demonic test which is never used in the proof
case class InverseGhost(s: Statement) extends Statement
// Proof of differential equation, either angelic or demonic.
case class ProveODE(ds: DiffStatement, dc: DomainStatement) extends Statement {
  // get predecessor of SSA variable. If there is no subscript, assume it's not an SSA variable so doesn't need pred.
  private def initOf(x: BaseVariable): BaseVariable = x match {
    case BaseVariable(x, None, s) => BaseVariable(x, None, s)
    case BaseVariable(x, Some(0), s) => BaseVariable(x, None, s)
    case BaseVariable(x, Some(i), s) => BaseVariable(x, Some(i - 1), s)
  }

  def solutionsFrom(xys: Map[Variable, Term], forProof: Boolean): Option[List[(Variable, Term)]] = {
    if (timeVar.isEmpty) None
    else {
      val ode = getODESystem(forProof)
      try {
        val result = Integrator(xys.toMap, timeVar.get, ode)
        val resultAlist = result.map({
          case Equal(x: Variable, f) => (x, f)
          case p => throw ProofCheckException(s"Solve expected $p to have shape x=f", node = this)
        })
        val resultMap = resultAlist.toMap
        val theTimeVar: Variable =
          if (result.size < xys.size) { xys.filter({ case (x, f) => !resultMap.contains(x) }).head._1 }
          else timeVar.get
        val (timeX, timeF) = duration match {
          case Some((x, f)) => (x -> f)
          case None => (theTimeVar -> theTimeVar)
        }
        Some((timeX, timeF) :: resultAlist)
      } catch {
        // Integrator raises Exception if it can't solve. Unfortunately, it does not raise any more specific type.
        case _: Exception => None
      }
    }
  }

  // Real [[solutions]] function assumes ODE is already in SSA form. Sometimes we need to check
  // "whether solutions exist" before SSA pass, so use silly initial values so that the integrator can run.
  private lazy val dummySolutions: Option[List[(Variable, Term)]] = {
    val dummyXys: Set[(Variable, Term)] = StaticSemantics(asODESystem)
      .bv
      .toSet
      .filter(_.isInstanceOf[BaseVariable])
      .map(_.asInstanceOf[BaseVariable])
      .map(x => (x -> Number(0)))
    try { solutionsFrom(dummyXys.toMap, false) }
    catch { case (m: MatchError) => None }
  }

  def hasDummySolution: Boolean = dummySolutions.isDefined
  def hasTrueSolution: Boolean = solutions.isDefined

  private def getSolutions(forProof: Boolean = false): Option[List[(Variable, Term)]] = {
    val ode = getODESystem(forProof)
    val bvs = StaticSemantics(ode).bv.toSet
    val xys: Set[(Variable, Term)] = bvs
      .filter(_.isInstanceOf[BaseVariable])
      .map(_.asInstanceOf[BaseVariable])
      .map(x => (x -> initOf(x)))
    try {
      val sols = solutionsFrom(xys.toMap, forProof)
      sols
    } catch { case (m: MatchError) => None } // Throws if not in SSA form
  }

  /** Get true solution of ODE. Only works if proof is in SSA form */
  lazy val solutions = getSolutions(forProof = false)
  lazy val proofSolutions = getSolutions(forProof = true)

  /** Get best avaiable solutions: true solutions if SSA has been performed, else dummy solutions */
  lazy val bestSolutions: Option[List[(Variable, Term)]] = if (solutions.isDefined) solutions else dummySolutions

  // Note we may want a default variable like "t" if timeVar is none, but freshness checks need a context, not just the ODE.
  private lazy val inferredTimeVar: Option[Variable] = {
    duration match {
      case Some((x, f)) => Some(x)
      case None => ds.clocks.toList match {
          case v :: Nil => Some(v)
          case _ => None
        }
    }
  }

  var explicitTimeVar: Option[Variable] = None
  def timeVar: Option[Variable] = if (explicitTimeVar.isDefined) explicitTimeVar else inferredTimeVar
  def overrideTimeVar(v: Variable): Unit = (explicitTimeVar = Some(v))

  private def getODESystem(forProof: Boolean = false): ODESystem = {
    ODESystem(ds.asDifferentialProgram(modifier, forProof), dc.asFormula(isAngelic, forProof).getOrElse(True))
  }

  lazy val asODESystem: ODESystem = getODESystem(false)

  lazy val isAngelic: Boolean = modifier.isDefined
  lazy val modifier: Option[DomModify] = { dc.modifier }

  lazy val duration: Option[(Variable, Term)] = {
    modifier.flatMap({
      case DomModify(id, x, f) => Some(x, f)
      case _ => None
    })
  }

  lazy val conclusion: Formula = {
    val odeSystem = asODESystem
    val odeBV = StaticSemantics(odeSystem).bv
    modifier.foreach(dm =>
      if (!odeBV.contains(dm.x)) throw ProofCheckException("ODE duration variable must be bound in ODE", node = this)
    )
    val hp = modifier.map(dm => Compose(odeSystem, Test(dm.asEquals))).getOrElse(odeSystem)
    if (modifier.nonEmpty) { Box(Dual(hp), True) }
    else { Box(hp, True) }
  }
}
object ProveODE {
  val defaultTimeVariable: Variable = Variable("t")
}

// Statements which "just" attach metadata to their underlying nodes and don't change computational meaning
sealed trait MetaNode extends Statement {
  val children: List[Statement] = Nil
}

// Debugging functionality: print [[msg]] with proof context
sealed trait Printable
case class PrintString(msg: String) extends Printable
case class PrintExpr(e: Expression) extends Printable

case class PrintGoal(printable: Printable) extends MetaNode {
  override val children: List[Statement] = Nil
}

/**
 * Note this is not for comments parsed from source files since the parser strips out comments. This is used for the
 * insertion of machine-generated comments in machine-generated Kaisar files
 */
case class Comment(str: String) extends MetaNode {
  override val children: List[Statement] = Nil
}

/**
 * Used for features which are not fundamentally part of the language, but more convenience features of the
 * implementation. Used for setting options including those useful for debugging or profiling
 */
case class Pragma(ps: PragmaSpec) extends MetaNode {
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
      case mod: Modify => mod
          .mods
          .foldLeft[Map[Variable, Variable]](Map())({ case (acc, (x, Some(f: Variable))) =>
            if (reverse) acc.+(f -> x) else acc.+(x -> f)
          })
    }
  }
  def forwardMap: Map[Variable, Variable] = toMap(asgns, reverse = false)
  def reverseMap: Map[Variable, Variable] = toMap(asgns, reverse = true)
}

// This is a meta node because it's only used in contexts while checking the interior of a loop.
// It helps us handle variable admissibility/renaming for loops, especially for accessing the IH.
// boxLoop is the entire loop, progress contains the prefix of the body checked so far, and IH is the name of
// the inductive hypothesis
case class BoxLoopProgress(boxLoop: BoxLoop, progress: Statement) extends MetaNode {
  override val children: List[Statement] = List(block(boxLoop :: progress :: Nil))
}

// meta node for in-progress while loop.
case class WhileProgress(whilst: While, progress: Statement) extends MetaNode {
  override val children: List[Statement] = List(progress)
}

// meta node for in-progress for loop.
case class ForProgress(forth: For, progress: Statement) extends MetaNode {
  override val children: List[Statement] = List(progress)
}

// Meta node for switch in progress. onBranch indicates which branch was taken, 0-indexed
case class SwitchProgress(switch: Switch, onBranch: Int, progress: Statement) extends MetaNode {
  override val children: List[Statement] = List(progress)
}
// Meta node for box choice in progress. onBranch indicates which branch was taken, 0-indexed
case class BoxChoiceProgress(bc: BoxChoice, onBranch: Int, progress: Statement) extends MetaNode {
  override val children: List[Statement] = List(progress)
}

/**
 * Note: assertions are a list because it matters what order assertions are proved in. Order does not matter for the
 * others.
 */
final case class DomCollection(
    assumptions: Set[DomAssume],
    assertions: List[DomAssert],
    weakens: Set[DomainStatement],
    modifiers: Set[DomModify],
) {
  def constraints: Context = {
    val assume = assumptions.foldLeft(Context.empty)({ case (acc, DomAssume(x, f)) => acc.:+(Assume(x, f)) })
    assertions.foldLeft(assume)({ case (acc, DomAssert(x, f, m)) => acc.:+(Assert(x, f, m)) })
  }
}
final case class DiffCollection(
    atoms: Set[AtomicODEStatement],
    ghosts: Set[AtomicODEStatement],
    inverseGhosts: Set[AtomicODEStatement],
)

// Proof steps regarding the differential program, such as ghosts and inverse ghosts used in solutions.
sealed trait DiffStatement extends ASTNode {
  private def getDifferentialProgram(mod: Option[DomModify], forProof: Boolean = false): Option[DifferentialProgram] = {
    this match {
      case AtomicODEStatement(dp, _solIdent) =>
        (mod, dp.e) match {
          case (Some(DomModify(id, durvar, _)), Number(n)) if (dp.xp.x == durvar && n.toInt == 1) => ()
          case (Some(DomModify(id, durvar, _)), rhs) if (dp.xp.x == durvar) =>
            throw ProofCheckException(
              s"ODE duration variable/clock $durvar must change at rate 1, got $rhs",
              node = this,
            )
          case _ => ()
        }
        Some(dp)
      case DiffProductStatement(l, r) =>
        (l.getDifferentialProgram(mod, forProof), r.getDifferentialProgram(mod, forProof)) match {
          case (Some(l), Some(r)) => Some(DifferentialProduct(l, r))
          case (None, r) => r
          case (l, None) => l
        }
      case InverseDiffGhostStatement(ds) if forProof => None
      case InverseDiffGhostStatement(ds) => ds.getDifferentialProgram(mod, forProof)
      case DiffGhostStatement(ds) if forProof => ds.getDifferentialProgram(mod, forProof)
      case DiffGhostStatement(ds) => None
    }
  }

  def hasDifferentialProgram(mod: Option[DomModify]): Boolean = getDifferentialProgram(mod).isDefined

  def asDifferentialProgram(mod: Option[DomModify], forProof: Boolean = false): DifferentialProgram = {
    val x = DifferentialSymbol(BaseVariable("dummy"))
    getDifferentialProgram(mod, forProof).getOrElse(AtomicODE(x, Number(0)))
  }
  lazy val clocks: Set[Variable] = {
    this match {
      case AtomicODEStatement(AtomicODE(DifferentialSymbol(x), rhs: Number), _solIdent) if rhs.value.toInt == 1 =>
        Set(x)
      case _: AtomicODEStatement => Set()
      case DiffProductStatement(l, r) => l.clocks ++ r.clocks
      // since it's common to ghost in clock variables, we probably want this.
      case DiffGhostStatement(ds) => ds.clocks
      case InverseDiffGhostStatement(ds) => Set()
    }
  }

  def atoms: Set[AtomicODEStatement] = collect.atoms
  def allAtoms: Set[AtomicODEStatement] = collect.atoms ++ collect.ghosts ++ collect.inverseGhosts

  /** @return collection (nonGhosts, forwardGhosts, inverseGhosts) of statements in [[statement]] */
  def doCollect(kc: Context): DiffCollection = {
    this match {
      case st: AtomicODEStatement => DiffCollection(Set(st), Set(), Set())
      case DiffProductStatement(l, r) =>
        val DiffCollection(a1, b1, c1) = l.doCollect(kc)
        val DiffCollection(a2, b2, c2) = r.doCollect(kc)
        DiffCollection(a1.++(a2), b1.++(b2), c1.++(c2))
      case DiffGhostStatement(ds) =>
        if (kc.isInverseGhost) throw ProofCheckException("Forward ODE ghost not allowed inside inverse ghost")
        val DiffCollection(a, b, c) = ds.doCollect(kc.withGhost)
        DiffCollection(Set(), a.++(b).++(c), Set())
      case InverseDiffGhostStatement(ds) =>
        if (kc.isGhost) throw ProofCheckException("Inverse ODE ghost not allowed inside forward ghost")
        val DiffCollection(a, b, c) = ds.doCollect(kc.withInverseGhost)
        DiffCollection(Set(), Set(), a.++(b).++(c))
    }
  }

  /** @return collection (nonGhosts, forwardGhosts, inverseGhosts) of statements in [[statement]] */
  lazy val collect: DiffCollection = { doCollect(Context.empty) }
}

// Specifies a single ODE being proved
case class AtomicODEStatement(dp: AtomicODE, solFact: IdentPat = Nothing) extends DiffStatement
// Corresponding proofs for each conjunct of differential product
case class DiffProductStatement(l: DiffStatement, r: DiffStatement) extends DiffStatement
// Proof for ghost ODE introduced for sake of proof but not in conclusion
case class DiffGhostStatement(ds: DiffStatement) extends DiffStatement
// Proof for inverse ghost ODE which appears in conclusion but not proof. Used in solution reasoning.
case class InverseDiffGhostStatement(ds: DiffStatement) extends DiffStatement

//Proof steps regarding the domain, for example differential cuts and weakening of domain constraints.
// Angelic solutions require witnesses for duration, also given here
sealed trait DomainStatement extends ASTNode {
  def asFormula(isAngelic: Boolean, forProof: Boolean = false): Option[Formula] = {
    this match {
      case DomAssume(x, f) => Some(f)
      case DomAssert(x, f, child) if isAngelic || forProof => Some(f)
      case DomAssert(x, f, child) => None
      case DomModify(id, x, f) => None
      case DomWeak(dc) if forProof => None
      case DomWeak(dc) => dc.asFormula(isAngelic, forProof)
      case DomAnd(l, r) => (l.asFormula(isAngelic), r.asFormula(isAngelic)) match {
          case (Some(l), Some(r)) => Some(And(l, r))
          case (None, r) => r
          case (l, None) => l
        }
    }
  }

  // Does the ODE contain an assertion?
  def isAssertive: Boolean = {
    this match {
      case DomAssert(x, f, child) => true
      case DomAnd(l, r) => l.isAssertive && r.isAssertive
      case _ => false
    }
  }

  def modifier: Option[DomModify] = {
    this match {
      case dm: DomModify => Some(dm)
      case DomAnd(l, r) => (l.modifier, r.modifier) match {
          case (Some(x), Some(y)) =>
            throw ProofCheckException("ODE should only have one duration statement", node = this)
          case (None, r) => r
          case (l, None) => l
        }
      case _: DomWeak | _: DomAssume | _: DomAssert => None
    }
  }

  lazy val collect: DomCollection = {
    this match {
      case da: DomAssume => DomCollection(Set(da), List(), Set(), Set())
      case da: DomAssert => DomCollection(Set(), List(da), Set(), Set())
      case DomWeak(dw) =>
        val DomCollection(a, b, c, d) = dw.collect
        DomCollection(Set(), List(), a.++(b).++(c), d)
      case dm: DomModify => DomCollection(Set(), List(), Set(), Set(dm))
      case DomAnd(l, r) =>
        val DomCollection(a1, b1, c1, d1) = l.collect
        val DomCollection(a2, b2, c2, d2) = r.collect
        DomCollection(a1.++(a2), b1.++(b2), c1.++(c2), d1.++(d2))
    }
  }

  lazy val demonFormula: Option[Formula] = asFormula(isAngelic = false)
  lazy val angelFormula: Option[Formula] = asFormula(isAngelic = true)
}

object DomainStatement {
  def ofStatement(ds: Statement): Option[DomainStatement] = ds match {
    case _: Triv => None
    case Block(ss) =>
      val dss = ss.map(ofStatement).filter(_.isDefined).map(_.get)
      if (dss.isEmpty) None else Some(dss.reduceRight(DomAnd))
    case Assume(x, f) => Some(DomAssume(x, f))
    case Assert(x, f, m) => Some(DomAssert(x, f, m))
  }
}

sealed trait DomainFact extends DomainStatement {
  def asStatement: Statement = {
    this match {
      case (DomAssume(x, f)) => Assume(x, f)
      case (DomAssert(x, f, m)) => Assert(x, f, m)
    }
  }

  def mapF(f: Formula => Formula): DomainFact = {
    this match {
      case DomAssume(x, fml) => DomAssume(x, f(fml))
      case DomAssert(x, fml, m) => DomAssert(x, f(fml), m)
    }
  }
}

// x is an identifier pattern in assume and assert
// Introduces assumption in domain, i.e., a domain formula which appears in the conclusion and can be accessed
// by differential weakening
case class DomAssume(x: IdentPat, f: Formula) extends DomainFact
// Differential assertion which is proved with differential cut and then possibly used in proof
case class DomAssert(x: IdentPat, f: Formula, child: Method) extends DomainFact
// Distinct from "differential weakening" rule, meaning a domain constraint which is in the conclusion but not the
// proof, which is weakened before continuing proof
case class DomWeak(dc: DomainStatement) extends DomainStatement
// Assignment to a variable. Only allowable use is to specify the duration of an angelic solution
case class DomModify(id: IdentPat, x: Variable, f: Term) extends DomainStatement {
  lazy val asEquals: Equal = { Equal(x, f) }
}
// Conjunction of domain constraints with proofs for each conjunct
case class DomAnd(l: DomainStatement, r: DomainStatement) extends DomainStatement
