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
  type Snapshot = Map[String, Subscript]

  // Kaisar extends the syntax of expressions with located expressions  f@L.
  // Rather than extend Expression,scala, we implement this as an interpreted function symbol at(f, L()) which
  // we elaborate to the core expression syntax
  // "init" is an example label-function which can be passed for the second argument of at()
  // In concrete proofs, the label function name is generated from; the labels in the proof.
  val at: Function = Function("at", domain = Tuple(Real, Unit), sort = Real, interpreted = true)
  val init: FuncOf = FuncOf(Function("init", domain = Unit, sort = Unit, interpreted = true), Nothing)

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
sealed trait Method extends ASTNode
// constructive real-closed field arithmetic
case class RCF() extends Method {}
// general-purpose auto heuristic
case class Auto() extends Method {}
// propositional steps
case class Prop() extends Method {}
// introduce an assumption used in method
case class Using(use: List[Selector], method: Method) extends Method {}
// discharge goal with structured proof
case class ByProof(proof: Proof) extends Method {}

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
sealed trait Statement extends ASTNode {
}
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
case class BoxLoop(s: Statement) extends Statement
// Statement [[s]] is introduced for use in the proof but is not exported in the conclusion.
// For example, Ghost(Modify(_)) is a discrete ghost assignment
// @TODO: Resolve scope-escaping issues
case class Ghost(s: Statement) extends Statement
// Inverse-ghost of statement [[s]], i.e., program of [[ss]] is part of the conclusion but not relevant to the proof.
// For example, InverseGhost(Assume(_)) indicates a Demonic test which is never used in the proof
case class InverseGhost(s: Statement) extends Statement
// Proof of differential equation, either angelic or demonic.
case class ProveODE(ds: DiffStatement, dc: DomainStatement) extends Statement //de: DifferentialProgram

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
case class BoxLoopProgress(boxLoop: BoxLoop, progress: Statement, ihVar: Ident, ihFml: Formula) extends MetaNode {
  override val children: List[Statement] = List(block(boxLoop :: progress :: Nil))
}

// Proof steps regarding the differential program, such as ghosts and inverse ghosts used in solutions.
sealed trait DiffStatement extends ASTNode
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
sealed trait DomainStatement extends ASTNode
// x is formula pattern in assume and assert
// Introduces assumption in domain, i.e., a domain formula which appears in the conclusion and can be accessed
// by differential weakening
case class DomAssume(x: Expression, f:Formula) extends DomainStatement
// Differential assertion which is proved with differential cut and then possibly used in proof
case class DomAssert(x: Expression, f:Formula, child: Method) extends DomainStatement
// Distinct from "differential weakening" rule, meaning a domain constraint which is in the conclusion but not the
// proof, which is weakened before continuing prof
case class DomWeak(dc: DomainStatement) extends DomainStatement
// Assignment to a variable. Only allowable use is to specify the duration of an angelic solution
case class DomModify(x: AsgnPat, f: Term) extends DomainStatement
// Conjunction of domain constraints with proofs for each conjunct
case class DomAnd(l: DomainStatement, r: DomainStatement) extends DomainStatement



// Proof variable information includes program variables [[xs]] and proof variables [[ps]]
case class ProofVars(xs: VCP, ps: SetLattice[String])

object Context {
  // Contexts are proof statements showing what game has been played thus far
  type Context = Statement
  // fact identifier, fact formula, whether fact is from an assignment
  type Finder = ((Ident, Formula, Boolean)) => Boolean
  def empty: Context = Triv()
  def :+(con: Context, s: Statement): Context = {
    con match {
      case _: Triv  => s
      case BoxLoopProgress(bl, pr, ihv, ihf) => BoxLoopProgress(bl, :+(pr, s), ihv, ihf)
      case Block(ss) => Block(ss.:+(s))
      case sl => Block(List(sl, s))
    }
  }

  //def theorem(con: Context): Formula = con.conclusion

  def add(con: Context, x: Ident, fml: Formula): Context = {
    :+(con, Assume(x, fml))
  }

  def sameHead(e: Expression, f: Expression): Boolean = {
    (e, f) match {
      case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
        bcf1.reapply(bcf2.left, bcf2.right) == bcf2
      case (ucf1: UnaryCompositeFormula, ucf2: UnaryCompositeFormula) =>
        ucf1.reapply(ucf2.child) == ucf2
      // No matching in quantified vars or program, so reapply to q1/m1
      case (q1: Quantified, q2: Quantified) => q1.reapply(q1.vars, q2.child) == q2
      case (m1: Modal, m2: Modal) => m1.reapply(m1.program, m2.child) == m2
    }
  }

  // @TODO: generalize to all expressions.
  def matchAssume(e: Expression, f: Formula): Map[Ident, Formula] = {
      e match {
        case BaseVariable(x, _, _) => Map(Variable(x) -> f)
        case _ =>
          if (!sameHead(e, f))
            throw ProofCheckException(s"Pattern $e does not match formula $f")
          (e, f) match {
            case (bcf1: BinaryCompositeFormula, bcf2: BinaryCompositeFormula) =>
              matchAssume(bcf1.left, bcf2.left) ++ matchAssume(bcf1.right, bcf2.right)
            case (ucf1: BinaryCompositeFormula, ucf2: BinaryCompositeFormula) =>
              matchAssume(ucf1.left, ucf2.left)
            case (q1: Quantified, q2: Quantified) => matchAssume(q1.child, q2.child)
            case (m1: Modal, m2: Modal) =>matchAssume(m1.child, m2.child)
          }
      }
  }

  // find most recent element first
  def findAll(mod: Modify, finder: Finder, isGhost: Boolean): List[(Ident, Formula)] = {
    mod match {
      case Modify(TuplePat(pat :: pats), Left(Pair(l, r))) =>
        val left = findAll(Modify(pat, Left(l)), finder, isGhost)
        val right = findAll(Modify(TuplePat(pats), Left(r)), finder, isGhost)
        left ++ right
      case Modify(VarPat(x, Some(p)), Left(f)) if(finder(p, Equal(x, f), true)) =>
        // @TODO: Proper variable renaming
        List((p, Equal(x, f)))
      // default: proof variable name = program variable name
      case Modify(VarPat(x, None), Left(f)) if(finder(x, Equal(x, f), true)) =>
        if (isGhost) {
          List()
          // @TODO: Do we ever want to throw error
          //throw ProofCheckException(s"Ghost variable $x inaccessible because it would escape its scope")
        } else
          List((x, Equal(x, f)))
      case Modify(VarPat(x, Some(_)), Right(())) =>
        throw ProofCheckException("Nondeterministic assignment pattern should not bind proof variable")
      case Modify(_, _) => List()
    }
  }

  def findAll(dc: DomainStatement, f: Finder): List[(Ident, Formula)] = {
    dc match {
      case DomAssume(x, fml) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList//collectFirst({case (mx, mf) if mx == id => mf})
      case DomAssert(x, fml, _ ) => matchAssume(x, fml).filter({case (x,y) => f(x, y, false)}).toList//collectFirst({case (mx, mf) if mx == id => mf})
      case DomAnd(l, r) => findAll(l, f) ++ findAll(r, f)
      case DomWeak(dc) =>
        findAll(dc, f) match {
          case fml :: _ => throw ProofCheckException(s"Weakened domain constraint $dc binds formula $fml, should not be selected")
          case Nil => Nil
        }
      case DomModify(ap, term) => findAll(Modify(ap, Left(term)), f)
    }
  }

  def signature(con: Context): Set[Function] = {
    con match {
      case lf: LetFun => Set(lf.asFunction)
      case Block(ss) => ss.flatMap(signature).toSet
      case BoxChoice(l, r) => signature(l) ++ signature (r)
      case Switch(sel, pats) => pats.map(_._3).flatMap(signature).toSet
      case Ghost(s) => signature(s)
      case Was(now, was) => signature(now)
      // @TODO: These loop cases probably work, but subtle
      case While(_, _, body) => signature(body)
      case BoxLoop(body) => signature(body)
      case _: Triv | _: Assume | _: Assert | _: Note | _: PrintGoal | _: InverseGhost | _: ProveODE | _: Modify
         | _: Label | _: Match => Set()
    }
  }

  // @TODO: unsound
  def getAssignments(con: Context, x: Variable): List[Formula] =
    searchAll(con,
      {case (v@BaseVariable(xx, idx, _), Equal(BaseVariable(xxx, idxx,_), f), true) if x.name == xx && xx == xxx && idx == idxx => true
        case _ => false
      }, isGhost = false).map(_._2)

  // Look up latest definition of proof variable
  // @TODO: Does this handle state change properly?, Probably only works right for SSA form, or Blocks() needs to check for
  // free variable binding after reference for admissibility
  def searchAll(con: Context, f: Finder, isGhost: Boolean): List[(Ident, Formula)] = {
    con match {
      case _: Triv => Nil
      case Assume(x, g) => matchAssume(x, g).filter({ case (x, y) => f(x, y, false) }).toList
      case Assert(x, g, _) => matchAssume(x, g).filter({ case (x, y) => f(x, y, false) }).toList
      case Note(x, _, Some(g)) => if (f(x, g, false)) List((x, g)) else Nil
      case Note(x, _, None) => throw ProofCheckException("Note in context needs formula annotation") //if (f(x, True)) List((x, True)) else Nil
      //throw ProofCheckException("Note in context needs formula annotation")
      case mod: Modify => findAll(mod, f, isGhost)
      case Block(ss) =>
        def iter(ss: List[Statement], f: Finder): List[(Ident, Formula)] = {
          ss match {
            case Nil => Nil
            case (s: Phi) :: ss =>
              val ff: Finder = ({
                case ((x: Ident, fml: Formula, b: Boolean)) => f(x, substPhi(s, fml), b)
              })
              iter(ss, ff)
            case s :: ss =>
              val left =
                searchAll(s, f, isGhost) match {
                  case ((yx, yf)) :: _ =>
                    val surrounding = Block(ss.reverse)
                    val t = Context.taboos(surrounding)
                    val inter = t.tabooVars.intersect(StaticSemantics(yf).fv.toSet)
                    if (inter.nonEmpty) {
                      throw ProofCheckException(s"Fact $yx inaccessible because ghost variable(s) $inter would escape their scope")
                    }
                    List((yx, yf))
                  case Nil => Nil
                }
              left ++ iter(ss, f)
          }
        }

        iter(ss.reverse, f)
      case BoxChoice(l, r) =>
        val and: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            if (k1 != k2) throw ProofCheckException("recursive call found formula twice with different names")
            else (k1, And(v1, v2))
        }
        searchAll(l, f, isGhost) ++ searchAll(r, f, isGhost)
      // @TODO
      case Switch(sel, pats) =>
        val or: ((Ident, Formula), (Ident, Formula)) => (Ident, Formula) = {
          case ((k1, v1), (k2, v2)) =>
            if (k1 != k2) throw ProofCheckException("recursive call found formula twice with different names")
            else (k1, Or(v1, v2))
        }
        val fmls = pats.flatMap({ case (v, e, s) => searchAll(s, f, isGhost) })
        if (fmls.isEmpty) Nil
        else List(fmls.reduceRight(or))
      case Ghost(s) => searchAll(s, f, isGhost = true)
      case Phi(s) => searchAll(s, f, isGhost = true)
      case InverseGhost(s) => Nil
      /*val xs = Context.taboos(InverseGhost(s)).vars
        search(s, f, isGhost) match {
          case Some(ml) =>
            // @TODO: distinguished exception
            throw ProofCheckException(s"Formula $f should not be selected from statement $s which is an inverse ghost")
          case None => None
        }*/
      case po: ProveODE => findAll(po.dc, f) // @TODO: Needs ghost arg?
      case Was(now, was) => searchAll(now, f, isGhost)
      case _: Label | _: LetFun | _: Match | _: PrintGoal => Nil
      // @TODO: These loop cases probably work, but subtle
      case While(_, _, body) => searchAll(body, f, isGhost)
      case BoxLoop(body) => searchAll(body, f, isGhost)
      case BoxLoopProgress(boxLoop, progress, ihVar, ihFml) =>
        val ihMatch = if(f(ihVar, ihFml, false)) List((ihVar, ihFml)) else List()
        ihMatch ++ searchAll(progress, f, isGhost)
    }
  }

  def findAll(con: Context, f: Finder): List[(Ident, Formula)] = {
    searchAll(con, f, isGhost = false)
  }
  def find(con: Context, f: Finder): Option[(Ident, Formula)] = {
    findAll(con, f).headOption
  }
  def getAll(con: Context, id: Ident): List[Formula] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, v: Formula, false) => x == id case _ => false}
    searchAll(con, f, isGhost = false).map(_._2)
  }
  def get(con: Context, id: Ident): Option[Formula] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, v: Formula, false) => x == id case _ => false}
    searchAll(con, f, isGhost = false).map(_._2).headOption
  }

  private def substPhi(phi: Phi, fml: Formula): Formula = {
    val mapping = phi.reverseMap
    val res = SubstitutionHelper.replacesFree(fml)({case v: Variable => mapping.get(v) case f => None})
    res
  }

  def lastFact(con: Context): Option[(Ident, Formula)] = {
    con match {
      case Assume(x: Variable, f) => Some((x, f))
      case Assert(x: Variable, f, _) => Some((x,f))
      case Note(x: Variable, pt, opt) => opt.map((x, _))
      case Modify(VarPat(x, Some(p)), Left(f)) => Some((p, Equal(x, f)))
      case Modify(VarPat(x, _), Left(f)) => Some((x, Equal(x, f)))
      case BoxChoice(l, r) =>
        (lastFact(l), lastFact(r)) match {
          case (Some(resL), Some(resR)) if resL == resR => Some(resL)
          case _ => None
        }
      case BoxLoop(body) => lastFact(body)
      case While(_, _, body) => lastFact(body)
      // Note: After SSA, last statement is phi node, so keep looking to find "real" node
      case Block(ss) =>
        // @TODO: Need a more general way to handle phi assignments
        ss.reverse match {
          case (phi: Phi) :: rest =>
            val fact = rest.map(lastFact).filter(_.isDefined).head
            fact.map({case (x, fml) => (x, substPhi(phi, fml))})
          case ss =>
            ss.map(lastFact).filter(_.isDefined).head
        }
      case Was(now, was) => lastFact(now)
      case Ghost(s) => lastFact(s)
      // Skips all meta nodes and inverse ghosts, for example
      case _ => None
    }
  }

  def contains(con: Context, id: Ident): Boolean = get(con, id).isDefined

  def unifyAll(con: Context, pat: Expression): List[(Ident, Formula)] = {
    val f: ((Ident, Formula, Boolean)) => Boolean = {case (x: Ident, fml: Formula, false) =>
      try {
        UnificationMatch(pat, fml)
        true
      } catch {
        case _: ProverException => false
      }
    case _ => false}
    searchAll(con, f, isGhost = false)
  }
  def unify(con: Context, pat: Expression): Option[(Ident, Formula)] = unifyAll(con, pat).headOption

  // Base name used for fresh variables generated during proof when no better variable name is available.
  val ghostVar: String = "ghost"
  // Extend context with a named assumption
  //def add(ident: String, f: Formula): Context = Context(proofVars.+((ident, f)))

  // @TODO: implement freshProgramVar too

  // A proof variable name which is not bound in the context.
  def fresh(con: Context, ident: String = ghostVar): Ident = {
    var i = 0
    while(contains(con, Variable(ident + i))) {
      i = i + 1
    }
    Variable(ident + i)
  }

  // Define the next gHost variable to be f
  def ghost(con: Context, f: Formula): Context = add(con, fresh(con), f)

  case class Taboos(boundVars: Set[Variable], tabooVars: Set[Variable], functions: Set[Ident], facts: Set[Ident]) {
    def addTabooVars(v: Set[Variable]): Taboos = Taboos(boundVars,tabooVars.++(v), functions, facts)
    def addTabooFuncs(f: Set[Ident]): Taboos = Taboos(boundVars, tabooVars, functions.++(f), facts)
    def addTabooFacts(p: Set[Ident]): Taboos = Taboos(boundVars, tabooVars, functions, facts.++(p))
    def ++(other: Taboos): Taboos = Taboos(boundVars.++(other.boundVars), tabooVars.++(other.tabooVars), functions.++(other.functions), facts.++(other.facts))
  }
  object Taboos { val empty: Taboos = Taboos(Set(), Set(), Set(), Set())}

  def taboos(con: Context, isGhost: Boolean = false, isInverseGhost: Boolean = false): Taboos = con match {
    case Triv() | Label(_, _) => Taboos.empty
    case Ghost(s) => taboos(s, isGhost = true, isInverseGhost = false)
    case InverseGhost(s) => taboos(s, isGhost = false, isInverseGhost = true)
    case Assume(pat: Term, f) => Taboos(boundVars = Set(), tabooVars = Set(), functions = Set(), facts = if (isInverseGhost) StaticSemantics(pat).toSet else Set())
    case Assert(pat: Term, f, m) => Taboos(boundVars = Set(), tabooVars = Set(), functions = Set(), facts = if (isInverseGhost) StaticSemantics(pat).toSet else Set())
    case Modify(pat: AsgnPat, _) => Taboos(boundVars = pat.boundVars, tabooVars = if (isGhost) pat.boundVars else Set(), functions = Set(), facts = if (isInverseGhost) pat.boundFacts else Set())
    case Note(x, proof, ann) => Taboos(boundVars = Set(), tabooVars = Set(), functions = Set(), facts = if (isInverseGhost) Set(x) else Set())
    case LetFun(f, args, e) => Taboos(boundVars = Set(), tabooVars = Set(), functions = if (isInverseGhost) Set(f) else Set(), facts = Set())
    case Match(pat: Term, e) => Taboos(boundVars = StaticSemantics(pat).toSet, tabooVars = if (isGhost) StaticSemantics(pat).toSet else Set(), functions = Set(), facts = Set())
    case Block(ss) => ss.map(taboos(_, isGhost, isInverseGhost)).foldLeft(Taboos.empty)((l, r) => l.++(r))
    case Switch(scrutinee, pats) =>
      pats.map({ case (x: Term, fml, s) => {
        val t = taboos(s, isGhost, isInverseGhost)
        if (isInverseGhost) t.addTabooFacts(StaticSemantics(x).toSet) else t
      }
      }).reduce((l, r) => l.++(r))
    case BoxChoice(left, right) => taboos(left, isGhost, isInverseGhost).++(taboos(right, isGhost, isInverseGhost))
    case While(x: Term, j, s) =>taboos(s, isGhost, isInverseGhost).addTabooFacts(StaticSemantics(x).toSet)
    case BoxLoop(s) => taboos(s, isGhost, isInverseGhost)
    case ProveODE(ds, dc) => taboos(ds, isGhost, isInverseGhost).++(taboos(dc, isGhost, isInverseGhost))
    case m: MetaNode => m.children.map(taboos(_, isGhost, isInverseGhost)).foldLeft(Taboos.empty)(_.++(_))

  }
  def taboos(con: DiffStatement, isGhost: Boolean, isInverseGhost: Boolean): Taboos = con match {
    case AtomicODEStatement(dp) => Taboos(boundVars = Set(dp.xp.x), tabooVars = if(isGhost) Set(dp.xp.x) else Set(), Set(), Set())
    case DiffProductStatement(l, r) => taboos(l, isGhost, isInverseGhost).++(taboos(r, isGhost, isInverseGhost))
    case DiffGhostStatement(ds) => taboos(ds, isGhost = true, isInverseGhost = false)
    case InverseDiffGhostStatement(ds) => taboos(ds, isGhost = false, isInverseGhost = true)
  }
  def taboos(con: DomainStatement, isGhost: Boolean, isInverseGhost: Boolean): Taboos = con match {
    case DomAssume(x: Term, f) => Taboos(Set(), Set(), Set(), if(isInverseGhost) StaticSemantics(x).toSet else Set())
    case DomAssert(x: Term, f, child) => Taboos(Set(), if(isGhost) StaticSemantics(x).toSet else Set(), Set(), Set())
    case DomWeak(dc: DomainStatement) => taboos(dc, isGhost = false, isInverseGhost = true)
    case DomModify(x: AsgnPat, f: Term) => Taboos(Set(), if(isGhost) x.boundVars else Set(), Set(), if(isInverseGhost) x.boundFacts else Set())
    case DomAnd(l, r) => taboos(l, isGhost, isInverseGhost).++(taboos(r, isGhost, isInverseGhost))
  }
}

// superceded by proofs as contexts
// Structured context for checking Kaisar proofs
/*sealed trait Context
case class CEmpty() extends Context
case class COne(id: Ident, fml: Formula) extends Context
case class CLabel(label: Ident) extends Context
case class COr(l: Context, r: Context) extends Context
case class CAnd(l: Context, r: Context) extends Context
case class CThen(l: Context, r: Context) extends Context
case class CAssign(p: Option[Ident], x: Variable, f: Option[Term]) extends Context*/

//object Context {
/*case class Context (proofVars: Map[String, Formula]) {
  */

//}