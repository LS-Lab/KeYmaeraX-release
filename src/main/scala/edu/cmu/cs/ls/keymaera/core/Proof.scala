package edu.cmu.cs.ls.keymaera.core

import scala.annotation.elidable
import scala.annotation.elidable._
import scala.collection.immutable.HashMap
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{FTPG, TraverseToPosition, StopTraversal, ExpressionTraversalFunction}

/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

  sealed abstract class Rule(val name: String) extends (Sequent => List[Sequent]) {
    override def toString: String = name
  }

  trait OracleRule extends Rule

  sealed abstract class Status
    case object Success       extends Status
    case object Failed        extends Status // counterexample found
    case object Unfinished    extends Status
    case object LimitExceeded extends Status
    case object Pruned        extends Status
    case object ParentClosed  extends Status

  /**
   * Proof Tree
   *============
   */

  sealed case class ProofStep(rule : Rule, subgoals : List[ProofNode])
  sealed class ProofNode protected (val sequent : Sequent, val parent : ProofNode) {

    @volatile private[this] var alternatives : List[ProofStep] = Nil

    def children: List[ProofStep] = alternatives

    /* must not be invoked when there is no alternative */
    def getStep : ProofStep = alternatives match {
      case List(h, t) => h
      case Nil        => throw new IllegalArgumentException("getStep can only be invoked when there is at least one alternative.")
    }

    private def prepend(r : Rule, s : List[ProofNode]) {
      this.synchronized {
        alternatives = ProofStep(r, s) :: alternatives;
      }
    }

    def prune(n : Int) {
      this.synchronized {
        if (n < alternatives.length)
          alternatives = alternatives.take(n-1) ++ alternatives.drop(n)
        else
          throw new IllegalArgumentException("Pruning an alternative from a proof tree requires this alternative to exists.")
      }
    }

    def apply(rule : Rule) : List[ProofNode] = {
      val result = rule(sequent).map(new ProofNode(_, this))
      prepend(rule, result)
      result
    }

    @volatile private[this] var closed : Boolean = false
    @volatile var status               : Status  = Unfinished

    def isLocalClosed: Boolean = closed

    def closeNode(s : Status) =
      this.synchronized {
        if (!closed) {
          closed = true
          status = s
        }
      }

    def checkParentClosed() : Boolean = {
      var node = this
      while (node != null && !node.isLocalClosed) node = node.parent
      if (node == null) {
        return false
      } else {
        node = this
        while (node != null && !node.isLocalClosed) {
          node.closeNode(ParentClosed)
          node = node.parent
        }
        return true
      }
    }
  }

  class RootNode(sequent : Sequent) extends ProofNode(sequent, null) {

  }

  /*********************************************************************************
   * Proof Rules
   *********************************************************************************
   */

abstract class PositionRule(name: String, val pos: Position) extends Rule(name)

abstract class AssumptionRule(name: String, val aPos: Position, pos: Position) extends PositionRule(name, pos)

abstract class TwoPositionRule(name: String, val pos1: Position, val pos2: Position) extends Rule(name)

abstract class PosInExpr {
  def first:  PosInExpr = FirstP(this)
  def second: PosInExpr = SecondP(this)
  def third:  PosInExpr = ThirdP(this)

  def isPrefixOf(p: PosInExpr): Boolean
}

case object HereP extends PosInExpr {
  def isPrefixOf(p: PosInExpr) = true
}

case class FirstP(val sub: PosInExpr) extends PosInExpr {
  def isPrefixOf(p: PosInExpr) = p match {
    case FirstP(s) => s.isPrefixOf(sub)
    case _ => false
  }
}
case class SecondP(val sub: PosInExpr) extends PosInExpr {
  def isPrefixOf(p: PosInExpr) = p match {
    case SecondP(s) => s.isPrefixOf(sub)
    case _ => false
  }
}
case class ThirdP(val sub: PosInExpr) extends PosInExpr {
  def isPrefixOf(p: PosInExpr) = p match {
    case ThirdP(s) => s.isPrefixOf(sub)
    case _ => false
  }
}

class Position(val ante: Boolean, val index: Int, val inExpr: PosInExpr = HereP) {
  def isAnte = ante
  def getIndex: Int = index

  def isDefined(s: Sequent): Boolean =
    if(isAnte)
      s.ante.length > getIndex
    else
      s.succ.length > getIndex
}

abstract class Signature

// proof rules:

// reorder antecedent
object AnteSwitch {
  def apply(p1: Position, p2: Position): Rule = new AnteSwitchRule(p1, p2)

  private class AnteSwitchRule(p1: Position, p2: Position) extends Rule("AnteSwitch") {
    def apply(s: Sequent): List[Sequent] = if(p1.isAnte && p1.inExpr == HereP && p2.isAnte && p2.inExpr == HereP )
      List(Sequent(s.pref, s.ante.updated(p1.getIndex, s.ante(p2.getIndex)).updated(p2.getIndex, s.ante(p1.getIndex)), s.succ))
    else
      throw new IllegalArgumentException("This rule is only applicable to two positions in the antecedent")
  }
}

// reorder succedent
object SuccSwitch {
  def apply(p1: Position, p2: Position): Rule = new SuccSwitchRule(p1, p2)

  private class SuccSwitchRule(p1: Position, p2: Position) extends Rule("SuccSwitch") {
    def apply(s: Sequent): List[Sequent] = if(!p1.isAnte && p1.inExpr == HereP && !p2.isAnte && p2.inExpr == HereP )
      List(Sequent(s.pref, s.ante, s.succ.updated(p1.getIndex, s.succ(p2.getIndex)).updated(p2.getIndex, s.succ(p1.getIndex))))
    else
      throw new IllegalArgumentException("This rule is only applicable to two positions in the succedent")
  }
}

object Axiom {
  val axioms: Map[String, Formula] = getAxioms

  private def getAxioms: Map[String, Formula] = {
    var m = new HashMap[String, Formula]
    val a = ProgramConstant("$a")
    val b = ProgramConstant("$b")
    val p = PredicateConstant("$p")
    val pair = ("Choice", Equiv(BoxModality(Choice(a, b), p),And(BoxModality(a, p), BoxModality(b, p))))
    m = m + pair
    m
  }

  def apply(id: String): Rule = new Rule("Axiom " + id) {
    def apply(s: Sequent): List[Sequent] = {
      axioms.get(id) match {
        case Some(f) => List(new Sequent(s.pref, s.ante :+ f, s.succ))
        case _ => List(s)
      }
    }
  }
}

object Oracle {
  def mathematicaReduce: Rule = new Rule("Oracle Mathematica") with OracleRule {
    def apply(s: Sequent): List[Sequent] = {
      //TODO: implement
      List(s)
    }
  }
}

// cut
object Cut {
  def apply(f: Formula) : Rule = new Cut(f)
  private class Cut(f: Formula) extends Rule("cut") {
    def apply(s: Sequent): List[Sequent] = {
      val l = new Sequent(s.pref, s.ante :+ f, s.succ)
      val r = new Sequent(s.pref, s.ante, s.succ :+ f)
      List(l, r)
    }

    def parameter: Formula = f
  }
}

// equality/equivalence rewriting
class EqualityRewriting(ass: Position, p: Position) extends AssumptionRule("Equality Rewriting", ass, p) {
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    require(ass.isAnte && ass.inExpr == HereP)
    val (blacklist, fn) = s.ante(ass.getIndex) match {
      case Equals(d, a, b) =>
        (variables(a) ++ variables(b),
        new ExpressionTraversalFunction {
          override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term]  =
            if(e == a) Right(b)
            else if(e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
        })
      case ProgramEquals(a, b) =>
        (variables(a) ++ variables(b),
        new ExpressionTraversalFunction {
          override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program]  =
            if(e == a) Right(b)
            else if(e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
        })
      case Equiv(a, b) =>
        (variables(a) ++ variables(b),
        new ExpressionTraversalFunction {
          override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  = {
            if (e == a) Right(b)
            else if (e == b) Right(a)
            else throw new IllegalArgumentException("Equality Rewriting not applicable")
          }
        })
      case _ => throw new IllegalArgumentException("Equality Rewriting not applicable")
    }
    val trav = TraverseToPosition(p.inExpr, fn, blacklist)
    ExpressionTraversal.traverse(trav, if(p.isAnte) s.ante(p.getIndex) else s.succ(p.getIndex)) match {
      case Some(x: Formula) => if(p.isAnte) List(Sequent(s.pref, s.ante :+ x, s.succ)) else List(Sequent(s.pref, s.ante, s.succ :+ x))
      case a => throw new IllegalArgumentException("Equality Rewriting not applicable. Result is " + a + " " + a.getClass)
    }
  }
}

/**
 * Representation of a substitution replacing n with t.
 *
 * @param n the expression to be replaced. n can have one of the following forms:
 *          - Variable
 *          - Predicate
 *          - ApplyPredicate(Function, Expr)
 *          - Apply(Function, Expr)
 *          - ProgramConstant
 *          - Derivative(...)
 * @param t the expression to be used in place of n
 *@TODO Assert that n is of the above form only
 */
class SubstitutionPair (val n: Expr, val t: Expr) {
  applicable

  @elidable(ASSERTION) def applicable = require(n.sort == t.sort, "Sorts have to match in substitution pairs: "
    + n.sort + " != " + t.sort)
}

/**
 * A Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 */
class Substitution(l: Seq[SubstitutionPair]) {
    //@TODO assert unique left hand side in l

  /**
   *
   * @param source should be a tuple of substitutable things
   * @param target should be a tuple of the same dimension donating the right sides
   * @return
   */
  private def constructSubst(source: Expr, target: Expr): Substitution = new Substitution(collectSubstPairs(source, target))

  private def collectSubstPairs(source: Expr, target: Expr): List[SubstitutionPair] = source match {
    case Pair(dom, a, b) => target match {
      case Pair(dom2, c, d) => collectSubstPairs(a, c) ++ collectSubstPairs(b, d)
      case _ => throw new IllegalArgumentException("A pair: " + source + " must not be replaced by a non pair: " + target)
    }
    case _: Variable => List(new SubstitutionPair(source, target))
    case _: PredicateConstant => List(new SubstitutionPair(source, target))
    case _: ProgramConstant => List(new SubstitutionPair(source, target))
    case _ => throw new IllegalArgumentException("Unknown base case " + source + " of sort " + source.sort)
  }

  def names(pairs: Seq[SubstitutionPair]): Seq[NamedSymbol] = (for(p <- pairs) yield names(p)).flatten.distinct
  def names(pair: SubstitutionPair): Seq[NamedSymbol] = (names(pair.n) ++ names(pair.t)).filter(!boundNames(pair.n).contains(_))

  /**
   * This method returns the names that are bound in the source of a substitution
   * @param n the source of a substitution
   * @return the names bound on the source side of a substitution
   * @TODO namesToBeBound or something like this for uniform substitution purposes could be a better name? Because it's not just the bound variables of a formula.
   */
  def boundNames(n: Expr): Seq[NamedSymbol] = n match {
    case ApplyPredicate(_, args) => names(args)
    case Apply(_, args) => names(args)
    case _ => Nil
  }

  /**
   * Return all the named elements in a sequent
   * @param e
   * @return
   * @TODO maybe rename to freeNames, but make naming compatible with boundNames
   */
  def names(e: Expr): Seq[NamedSymbol] = e match {
    case x: NamedSymbol => Vector(x)
    case x: Unary => names(x.child)
    case x: Binary => names(x.left) ++ names(x.right)
    case x: Ternary => names(x.fst) ++ names(x.snd) ++ names(x.thd)
    case x: NFContEvolve => x.vars ++ names(x.x) ++ names(x.theta) ++ names(x.f)
    case x: Atom => Nil
  }

  // uniform substitution on formulas
  def apply(f: Formula): Formula = f match {
      // homomorphic cases
    case Not(c) => Not(this(c))
    case And(l, r) => And(this(l), this(r))
    case Or(l, r) => Or(this(l), this(r))
    case Imply(l, r) => Imply(this(l), this(r))
    case Equiv(l, r) => Equiv(this(l), this(r))

    // binding cases
    /*
     * For quantifiers just check that there is no name clash, throw an exception if there is
     */
    case Forall(vars, form) => if(vars.intersect(names(l)).isEmpty) Forall(vars, this(form))
    else throw new IllegalArgumentException("There is a name clash in uniform substitution " + vars + " and " + l + " applied on " + f)

    case Exists(vars, form) => if(vars.intersect(names(l)).isEmpty) Exists(vars, this(form))
    else throw new IllegalArgumentException("There is a name clash in uniform substitution " + vars + " and " + l + " applied on " + f)

    case x: Modality => if(x.writes.intersect(names(l)).isEmpty) x match {
      case BoxModality(p, f) => BoxModality(this(p), this(f))
      case DiamondModality(p, f) => DiamondModality(this(p), this(f))
      case _ => ???
    } else throw new IllegalArgumentException("There is a name clash in a substitution " + x.writes + " and " + l + " applied on " + f)

    //@TODO Concise way of asserting that there can be only one
    case _: PredicateConstant => for(p <- l) { if(f == p.n) return p.t.asInstanceOf[Formula]}; return f

    // if we find a match, we bind the arguments of our match to what is in the current term
    // then we apply it to the codomain of the substitution
    case ApplyPredicate(func, arg) => for(p <- l) {
      p.n match {
        case ApplyPredicate(pf, parg) if(func == pf) => return constructSubst(parg, arg)(p.t.asInstanceOf[Formula])
        case _ =>
      }
    }; return ApplyPredicate(func, this(arg))

    // homomorphic cases
    case Equals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => Equals(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case " + f)
    }
    case NotEquals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => NotEquals(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case ProgramEquals(l, r) => (l,r) match {
      case (a: Program,b: Program) => ProgramEquals(this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case ProgramNotEquals(l, r) => (l,r) match {
      case (a: Program,b: Program) => ProgramNotEquals(this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case GreaterThan(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => GreaterThan(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case GreaterEquals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => GreaterEquals(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case LessEquals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => LessEquals(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case LessThan(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => LessThan(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case x: Atom => x
    case _ => throw new UnsupportedOperationException("Not implemented yet")
  }
  
  // uniform substitution on terms
  def apply(t: Term): Term = t match {
      // homomorphic cases
    case Neg(s, c) => Neg(s, this(c))
    case Add(s, l, r) => Add(s, this(l), this(r))
    case Subtract(s, l, r) => Subtract(s, this(l), this(r))
    case Multiply(s, l, r) => Multiply(s, this(l), this(r))
    case Divide(s, l, r) => Divide(s, this(l), this(r))
    case Exp(s, l, r) => Exp(s, this(l), this(r))
    case Pair(dom, l, r) => Pair(dom, this(l), this(r))
    // applying uniform substitutions
    case Derivative(_, _) => for(p <- l) { if(t == p.n) return p.t.asInstanceOf[Term]}; return this(t)
    case Variable(_, _, _) => for(p <- l) { if(t == p.n) return p.t.asInstanceOf[Term]}; return t
    // if we find a match, we bind the arguments of our match to what is in the current term
    // then we apply it to the codomain of the substitution
    case Apply(func, arg) => for(p <- l) {
      p.n match {
        case Apply(pf, parg) if(func == pf) => return constructSubst(parg, arg)(p.t.asInstanceOf[Term])
        case _ =>
      }
    }; return Apply(func, this(arg))
    case x: Atom => require(!x.isInstanceOf[Variable], "variables have been substituted already"); x
    case _ => throw new UnsupportedOperationException("Not implemented yet")
  }

  // uniform substitution on programs
  def apply(p: Program): Program = {
      require(p.writes.intersect(names(l)).isEmpty);
      p match {
        case Loop(c) => Loop(this(c))
        case Sequence(a, b) => Sequence(this(a), this(b))
        case Choice(a, b) => Choice(this(a), this(b))
        case Parallel(a, b) => Parallel(this(a), this(b))
        case IfThen(a, b) => IfThen(this(a), this(b))
        case IfThenElse(a, b, c) => IfThenElse(this(a), this(b), this(c))
        case Assign(a, b) => Assign(a, this(b))  //@TODO assert that a is a variable (so far) and assert that a not in names(l)
        case NDetAssign(a) => p
        case Test(a) => Test(this(a))
        case ContEvolve(a) => ContEvolve(this(a))
        case NFContEvolve(v, x, t, f) => if(v.intersect(names(l)).isEmpty) NFContEvolve(v, x, this(t), this(f))
          else throw new IllegalArgumentException("There is a name clash in uniform substitution " + l + " applied on " + p + " because of quantified disturbance " + v)
        case x: ProgramConstant => for(pair <- l) { if(p == pair.n) return pair.t.asInstanceOf[Program]}; return p
        case _ => throw new UnsupportedOperationException("Not implemented yet")
     }
  }
}

/**
 * Uniform Substitution Rule.
 * Applies a given uniform substitution to the given original premise (origin).
 * Pseudo application in sequent calculus to conclusion that fits to the Hilbert calculus application (origin->conclusion).
 * This rule interfaces forward Hilbert calculus rule application with backward sequent calculus pseudo-application
 * @param substitution the uniform substitution to be applied to origin.
 * @param origin the original premise, to which the uniform substitution will be applied. Thus, origin is the result of pseudo-applying this UniformSubstitution rule in sequent calculus.
 */
// uniform substitution
// this rule performs a backward substitution step. That is the substitution applied to the conclusion yields the premise
object UniformSubstitution {
  def apply(substitution: Substitution, origin: Sequent) : Rule = new UniformSubstitution(substitution, origin)

  private class UniformSubstitution(subst: Substitution, origin: Sequent) extends Rule("Uniform Substitution") {
    /**
     * check that s is indeed derived from origin via subst (note that no reordering is allowed since those operations
     * require explicit rule applications)
     * @param conclusion the conclusion in sequent calculus to which the uniform substitution rule will be pseudo-applied, resulting in the premise origin that was supplied to UniformSubstituion.
     */
    def apply(conclusion: Sequent): List[Sequent] = {
      val singleSideMatch = ((acc: Boolean, p: (Formula, Formula)) => {val a = subst(p._1); println(KeYmaeraPrettyPrinter.stringify(a)); println(KeYmaeraPrettyPrinter.stringify(p._2)); a == p._2})
      if(conclusion.pref == origin.pref // universal prefix is identical
        && origin.ante.length == conclusion.ante.length && origin.succ.length == conclusion.succ.length  // same length makes sure zip is exhaustive
        && (origin.ante.zip(conclusion.ante)).foldLeft(true)(singleSideMatch)  // formulas in ante results from substitution
        && (origin.succ.zip(conclusion.succ)).foldLeft(true)(singleSideMatch)) // formulas in succ results from substitution
        List(origin)
      else
        throw new IllegalStateException("Substitution did not yield the expected result")
    }
  }
}


// AX close
object AxiomClose extends ((Position, Position) => Rule) {
  def apply(ass: Position, p: Position): Rule = new AxiomClose(ass, p)
}


class AxiomClose(ass: Position, p: Position) extends AssumptionRule("Axiom", ass, p) {
  require(p.isAnte != ass.isAnte, "Axiom close can only be applied to one formula in the antecedent and one in the succedent")
  require(p.inExpr == HereP && ass.inExpr == HereP, "Axiom close can only be applied to top level formulas")

  def apply(s: Sequent): List[Sequent] = {
    if(ass.isAnte) {
      if(s.ante(ass.getIndex) == s.succ(p.getIndex)) {
        // close
        Nil
      } else {
        throw new IllegalArgumentException("The referenced formulas are not identical. Thus the current goal cannot be closed. " + s.ante(ass.getIndex) + " not the same as " + s.succ(p.getIndex))
      }
    } else {
      if(s.succ(ass.getIndex) == s.ante(p.getIndex)) {
        // close
        Nil
      } else {
        throw new IllegalArgumentException("The referenced formulas are not identical. Thus the current goal cannot be closed. " + s.succ(ass.getIndex) + " not the same as " + s.ante(p.getIndex))
      }
    }
  }
}

// Impl right
object ImplyRight extends (Position => Rule) {
  def apply(p: Position): Rule = new ImplyRight(p)
}

class ImplyRight(p: Position) extends PositionRule("Imply Right", p) {
  assert(!p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case Imply(a, b) => List(Sequent(s.pref, s.ante :+ a, s.succ.updated(p.getIndex, b)))
      case _ => throw new IllegalArgumentException("Implies-Right can only be applied to implications. Tried to apply to: " + f)
    }
  }
}

// Impl left
object ImplyLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new ImplLeft(p)
}
class ImplLeft(p: Position) extends PositionRule("Imply Left", p) {
  assert(p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case Imply(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a), s.succ), Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
      case _ => throw new IllegalArgumentException("Implies-Left can only be applied to implications. Tried to apply to: " + f)
    }
  }
}

// Not right
object NotRight extends (Position => Rule) {
  def apply(p: Position): Rule = {
    new NotRight(p)
  }
}

class NotRight(p: Position) extends PositionRule("Not Right", p) {
  assert(!p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case Not(a) => List(Sequent(s.pref, s.ante :+ a, s.succ.patch(p.getIndex, Nil, 1)))
      case _ => throw new IllegalArgumentException("Not-Right can only be applied to negation. Tried to apply to: " + f)
    }
  }
}

// Not left
object NotLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new NotLeft(p)
}

class NotLeft(p: Position) extends PositionRule("Not Left", p) {
  assert(p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case Not(a) => List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
      case _ => throw new IllegalArgumentException("Not-Left can only be applied to negation. Tried to apply to: " + f)
    }
  }
}

// And right
object AndRight extends (Position => Rule) {
  def apply(p: Position): Rule = new AndRight(p)
}
class AndRight(p: Position) extends PositionRule("And Right", p) {
  assert(!p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case And(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex,a)), Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, b)))
      case _ => throw new IllegalArgumentException("And-Right can only be applied to conjunctions. Tried to apply to: " + f)
    }
  }
}

// And left
object AndLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new AndLeft(p)
}

class AndLeft(p: Position) extends PositionRule("And Left", p) {
  assert(p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case And(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a) :+ b, s.succ))
      case _ => throw new IllegalArgumentException("And-Left can only be applied to conjunctions. Tried to apply to: " + f)
    }
  }
}

// Or right
object OrRight extends (Position => Rule) {
  def apply(p: Position): Rule = new OrRight(p)
}
class OrRight(p: Position) extends PositionRule("Or Right", p) {
  assert(!p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.succ(p.getIndex)
    f match {
      case Or(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, a) :+ b))
      case _ => throw new IllegalArgumentException("Or-Right can only be applied to disjunctions. Tried to apply to: " + f)
    }
  }
}

// Or left
object OrLeft extends (Position => Rule) {
  def apply(p: Position): Rule = new OrLeft(p)
}

class OrLeft(p: Position) extends PositionRule("Or Left", p) {
  assert(p.isAnte && p.inExpr == HereP)
  def apply(s: Sequent): List[Sequent] = {
    val f = s.ante(p.getIndex)
    f match {
      case Or(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex,a), s.succ), Sequent(s.pref, s.ante.updated(p.getIndex, b), s.succ))
      case _ => throw new IllegalArgumentException("Or-Left can only be applied to disjunctions. Tried to apply to: " + f)
    }
  }
}

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)

// remove duplicate antecedent (this should be a tactic)
// remove duplicate succedent (this should be a tactic)
// hide
object HideLeft extends (Position => Rule) {
  def apply(p: Position): Rule = {
    assert(p.isAnte && p.inExpr == HereP)
    new Hide(p)
  }
}
object HideRight extends (Position => Rule) {
  def apply(p: Position): Rule = {
    assert(!p.isAnte && p.inExpr == HereP)
    new Hide(p)
  }
}
class Hide(p: Position) extends PositionRule("Hide", p) {
  def apply(s: Sequent): List[Sequent] = {
    assert(p.inExpr == HereP)
    if (p.isAnte)
      List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ))
    else
      List(Sequent(s.pref, s.ante, s.succ.patch(p.getIndex, Nil, 1)))
  }
}

// alpha conversion

/**
 * Alpha conversion works on exactly four positions:
 * (1) Forall(v, phi)
 * (2) Exists(v, phi)
 * (3) Modality(BoxModality(Assign(x, e)), phi)
 * (4) Modality(DiamondModality(Assign(x, e)), phi)
 *
 * It always replaces _every_ occurrence of the name in phi
 * @param tPos
 * @param name
 * @param idx
 * @param target
 * @param tIdx
 */
class AlphaConversion(tPos: Position, name: String, idx: Option[Int], target: String, tIdx: Option[Int]) extends Rule("Alpha Conversion") {
  def apply(s: Sequent): List[Sequent] = {
    val f = if(tPos.isAnte) s.ante(tPos.getIndex) else s.succ(tPos.getIndex)
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  =
        if(tPos.inExpr == p) {
          e match {
            case Forall(v, phi) => require(v.map((x: NamedSymbol) => x.name).contains(name), "Symbol to be renamed must be bound in " + e)
            case Exists(v, phi) => require(v.map((x: NamedSymbol) => x.name).contains(name), "Symbol to be renamed must be bound in " + e)
            case BoxModality(Assign(a, b), c) => require((a match {
              case Variable(n, _, _) => n
              case Apply(Function(n, _, _, _), _) => n
              case _ => throw new IllegalArgumentException("Unknown Assignment structure: " + e)
            }) == name, "Symbol to be renamed must be bound in " + e)
            case DiamondModality(Assign(a, b), c) => require((a match {
              case Variable(n, _, _) => n
              case Apply(Function(n, _, _, _), _) => n
              case _ => throw new IllegalArgumentException("Unknown Assignment structure: " + e)
            }) == name, "Symbol to be renamed must be bound in " + e)
            case _ => throw new IllegalArgumentException("We expect either a quantifier or a modality with a " +
              "single assignment at this position " + e + " " + p)
          }
          Left(None)
        } else (e match {
          case x: PredicateConstant => renamePred(x)
          case x: ProgramConstant => renameProg(x)
          case Apply(a, b) => Apply(renameFunc(a), b)
          case ApplyPredicate(a, b) => ApplyPredicate(renameFunc(a), b)
          case _ => return Left(None)
        }) match {
          case x: Formula => Right(x)
          case a => throw new IllegalArgumentException("Expected a formula. Got " + a)
        }
      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  = e match {
        case Forall(v, phi) => Right(Forall(for(i <- v) yield rename(i), phi))
        case Exists(v, phi) => Right(Forall(for(i <- v) yield rename(i), phi))
        case BoxModality(Assign(a, b), c) => Right(BoxModality(Assign(a match {
          case Variable(n, i, d) => if(n == name && i == idx) Variable(target, tIdx, d) else a
          case Apply(Function(n, i, d, s), phi) => if(n == name && i == idx) Apply(Function(target, tIdx, d, s), phi) else a
          case _ => throw new IllegalArgumentException("Unknown Assignment structure: " + e)
        }, b), c))
        case DiamondModality(Assign(a, b), c) => Right(DiamondModality(Assign(a match {
          case Variable(n, i, d) => if(n == name && i == idx) Variable(target, tIdx, d) else a
          case Apply(Function(n, i, d, s), phi) => if(n == name && i == idx) Apply(Function(target, tIdx, d, s), phi) else a
          case _ => throw new IllegalArgumentException("Unknown Assignment structure: " + e)
        }, b), c))
        case _ => Left(None)
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(tPos.inExpr, fn), f) match {
      case Some(x: Formula) => if(tPos.isAnte) List(Sequent(s.pref, s.ante :+ x, s.succ)) else List(Sequent(s.pref, s.ante, s.succ :+ x))
      case _ => throw new IllegalStateException("No alpha renaming possible in " + f)
    }
  }

  def renameVar(e: Variable): Variable = if(e.name == name && e.index == idx) Variable(target, tIdx, e.domain) else e

  def renamePred(e: PredicateConstant): PredicateConstant = if(e.name == name && e.index == idx) PredicateConstant(target, tIdx) else e

  def renameProg(e: ProgramConstant): ProgramConstant = if(e.name == name && e.index == idx) ProgramConstant(target, tIdx) else e

  def renameFunc(e: Function): Function = if(e.name == name && e.index == idx) Function(target, tIdx, e.domain, e.sort) else e

  def rename(e: NamedSymbol): NamedSymbol = e match {
    case v: Variable => renameVar(v)
    case p: PredicateConstant => renamePred(p)
    case p: ProgramConstant => renameProg(p)
    case f: Function => renameFunc(f)
  }
}

// skolemize
/**
 * Skolemization assumes that the names of the quantified variables to be skolemized are unique within the sequent.
 * This can be ensured by finding a unique name and renaming the bound variable through alpha conversion.
 */
class Skolemize(p: Position) extends PositionRule("Skolemize", p) {
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    require(p.inExpr == HereP, "We can only skolemize top level formulas");
    val vars = variablesWithout(s, p)
    val (v,phi) = if(p.isAnte) {
      val form = s.ante(p.getIndex)
      form match {
        case Exists(v, phi) => if(vars.map(v.contains).foldLeft(false)(_||_)) (v, phi) else
          throw new IllegalArgumentException("Variables to be skolemized should not appear anywhere in the sequent")
        case _ => throw new IllegalArgumentException("Skolemization is only applicable to existential quantifiers in the antecedent")
      }
    } else {
      val form = s.succ(p.getIndex)
      form match {
        case Forall(v, phi) => if(vars.map(v.contains).foldLeft(false)(_||_)) (v, phi) else
          throw new IllegalArgumentException("Variables to be skolemized should not appear anywhere in the sequent")
        case _ => throw new IllegalArgumentException("Skolemization is only applicable to universal quantifiers in the succedent")
      }
    }
    List(if(p.isAnte) Sequent(s.pref ++ v, s.ante.updated(p.index, phi), s.succ) else Sequent(s.pref ++ v, s.ante, s.succ.updated(p.index, phi)))
  }
}

/**
 * Assignment as equation
 * Assumptions: We assume that the variable has been made unique through alpha conversion first. That way, we can just
 * replace the assignment by an equation without further checking
 */
class AssignmentRule(p: Position) extends PositionRule("AssignmentRule", p) {
  import Helper._
  override def apply(s: Sequent): List[Sequent] = {
    // we need to make sure that the variable does not occur in any other formula in the sequent
    val vars = variablesWithout(s, p)
    // TODO: we have to make sure that the variable does not occur in the formula itself
    // if we want to have positions different from HereP
    require(p.inExpr == HereP, "we can only deal with assignments on the top-level for now")
    val f = if(p.isAnte)  s.ante(p.getIndex)  else s.succ(p.getIndex)
    val (exp, res, rhs) = f match {
      case BoxModality(Assign(l, r), post) => (l, Imply(Equals(l.sort, l, r), post), r)
      case DiamondModality(Assign(l, r), post) => (l, Imply(Equals(l.sort, l, r), post), r)
      case _ => throw new IllegalArgumentException("The assigment rule is only applicable to box and diamond modalities" +
        "containing a single assignment")
    }
    // check that v is not contained in any other formula
    val rhsVars = variables(rhs)
    val v = exp match {
      case x: Variable if(!vars.contains(x) && !rhsVars.contains(x)) => x
      case x: Variable if(vars.contains(x) || rhsVars.contains(x)) => throw new IllegalArgumentException("Varible " + x + " is not unique in the sequent")
      case _ => throw new IllegalStateException("Assignment handling is only implemented for varibles right now, not for " + exp.toString()) //?
    }

    List(if(p.isAnte) Sequent(s.pref :+ v, s.ante.updated(p.index, res), s.succ) else Sequent(s.pref :+ v, s.ante, s.succ.updated(p.index, res)))
  }
}

class AbstractionRule(pos: Position) extends PositionRule("AbstractionRule", pos) {
  override def apply(s: Sequent): List[Sequent] = {
    val f = if(pos.isAnte) s.ante(pos.getIndex) else s.succ(pos.getIndex)
    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula]  = e match {
            case BoxModality(p, f) => Right(Forall(p.writes, f))
            case DiamondModality(p, f) => Right(Forall(p.writes, f))
            case _ => throw new IllegalStateException("The abstraction rule is not applicable to " + e)
      }
    }
    ExpressionTraversal.traverse(TraverseToPosition(pos.inExpr, fn), f) match {
      case Some(x: Formula) => if(pos.isAnte) List(Sequent(s.pref, s.ante :+ x, s.succ)) else List(Sequent(s.pref, s.ante, s.succ :+ x))
      case _ => throw new IllegalStateException("No abstraction possible of " + f)
    }

  }
}

// maybe:

// close by true (do we need this or is this derived?)

// quantifier instantiation

// remove known

// unskolemize

// forall-I

// forall-E

// merge sequent (or is this derived?)


object Helper {
 def variables(s: Sequent): Set[NamedSymbol] = {
   val a = for(f <- s.ante) yield variables(f)
   val b = for(f <- s.succ) yield variables(f)
   Set() ++ a.flatten ++ b.flatten
  }

  def variables[A: FTPG](a: A): Set[NamedSymbol] = {
    var vars: Set[NamedSymbol] = Set.empty
    val fn = new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case x: Variable => vars += x
          case x: ProgramConstant => vars += x
          case Apply(f, _) => vars += f
          case _ =>
        };
        Left(None)
      }

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        e match {
          case x: PredicateConstant => vars += x
          case ApplyPredicate(f, _) => vars += f
          case _ =>
        };
        Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, a)
    vars
  }

  def variablesWithout(s: Sequent, p: Position): Set[NamedSymbol] = {
    var vars: Set[NamedSymbol] = Set.empty
    for(i <- 0 to s.ante.length) {
      if(!p.isAnte || i != p.getIndex) {
        vars ++= variables(s.ante(i))
      }
    }
    for(i <- 0 to s.succ.length) {
      if(p.isAnte || i != p.getIndex) {
        vars ++= variables(s.ante(i))
      }
    }
    vars
  }

}

// vim: set ts=4 sw=4 et:
