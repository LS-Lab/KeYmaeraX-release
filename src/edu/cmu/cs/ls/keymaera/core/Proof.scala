package edu.cmu.cs.ls.keymaera.core

import scala.annotation.elidable
import scala.annotation.elidable._

/*--------------------------------------------------------------------------------*/
/*--------------------------------------------------------------------------------*/

  sealed abstract class Rule extends (Sequent => List[Sequent])

  /**
   * Proof Tree
   *============
   */

  sealed class ProofNode protected (val sequent : Sequent, val parent : ProofNode) {

    case class ProofStep(rule : Rule, subgoals : List[ProofNode])

    @volatile private[this] var alternatives : List[ProofStep] = Nil

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

    def apply(rule: PositionRule, pos: Position) : List[ProofNode] = {
      val result = rule(pos)(sequent).map(new ProofNode(_, this))
      prepend(rule(pos), result)
      result
    }

    def apply(rule: AssumptionRule, aPos: Position, pos: Position) : List[ProofNode] = {
      val result = rule(aPos)(pos)(sequent).map(new ProofNode(_, this))
      prepend(rule(aPos)(pos), result)
      result
    }
  }

  class RootNode(sequent : Sequent) extends ProofNode(sequent, null) {

  }

  /*********************************************************************************
   * Proof Rules
   *********************************************************************************
   */

abstract class PositionRule extends (Position => Rule)

abstract class AssumptionRule extends (Position => PositionRule)

abstract class TwoPositionRule extends ((Position,Position) => Rule)

class Position(val ante: Boolean, val index: Int) {
  def isAnte = ante
  def getIndex: Int = index
}

abstract class Signature

// proof rules:

// reorder antecedent
object AnteSwitch {
  def apply(p1: Position, p2: Position): Rule = new AnteSwitchRule(p1, p2)

  private class AnteSwitchRule(p1: Position, p2: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = if(p1.isAnte && p2.isAnte)
      List(Sequent(s.pref, s.ante.updated(p1.getIndex, s.ante(p2.getIndex)).updated(p2.getIndex, s.ante(p1.getIndex)), s.succ))
    else
      throw new IllegalArgumentException("This rule is only applicable to two positions in the antecedent")
  }
}

// reorder succedent
object SuccSwitch {
  def apply(p1: Position, p2: Position): Rule = new SuccSwitchRule(p1, p2)

  private class SuccSwitchRule(p1: Position, p2: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = if(!p1.isAnte && !p2.isAnte)
      List(Sequent(s.pref, s.ante, s.succ.updated(p1.getIndex, s.succ(p2.getIndex)).updated(p2.getIndex, s.succ(p1.getIndex))))
    else
      throw new IllegalArgumentException("This rule is only applicable to two positions in the succedent")
  }
}

// cut
object Cut {
  def apply(f: Formula) : Rule = new Cut(f)
  private class Cut(f: Formula) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val l = new Sequent(s.pref, s.ante :+ f, s.succ)
      val r = new Sequent(s.pref, s.ante, s.succ :+ f)
      List(l, r)
    }

    def name: String = "cut"

    def parameter: Formula = f
  }
}

// equality/equivalence rewriting

/**
 * specific interpretation for variables that start and end with _
 * these are used for binding
 *
 * @param n can have one of the following forms:
 *          - Variable
 *          - Predicate
 *          - ApplyPredicate(Function, Expr)
 *          - Apply(Function, Expr)
 *          - ProgramConstant
 *          - Derivative(...)
 *  TODO: - deal with modalities (similar to quantifers)
 *        - walk through programs
 */
class SubstitutionPair (val n: Expr, val t: Expr) {
  applicable

  @elidable(ASSERTION) def applicable = require(n.sort == t.sort, "Sorts have to match in substitution pairs: "
    + n.sort + " != " + t.sort)
}

class Substitution(l: Seq[SubstitutionPair]) {

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
   */
  def names(e: Expr): Seq[NamedSymbol] = e match {
    case x: NamedSymbol => Vector(x)
    case x: Unary => names(x.child)
    case x: Binary => names(x.left) ++ names(x.right)
    case x: Ternary => names(x.fst) ++ names(x.snd) ++ names(x.thd)
    case x: NFContEvolve => x.vars ++ names(x.x) ++ names(x.theta) ++ names(x.f)
    case x: Atom => Nil
  }

  def apply(f: Formula): Formula = f match {
    case Not(c) => Not(this(c))
    case And(l, r) => And(this(l), this(r))
    case Or(l, r) => Or(this(l), this(r))
    case Imply(l, r) => Imply(this(l), this(r))
    case Equiv(l, r) => Equiv(this(l), this(r))

    /*
     * For quantifiers just check that there is no name clash, throw an exception if there is
     */
    case Forall(vars, form) => if(vars.intersect(names(l)).isEmpty) Forall(vars, this(form))
    else throw new IllegalArgumentException("There is a name class in a substitution " + vars + " and " + l)

    case Exists(vars, form) => if(vars.intersect(names(l)).isEmpty) Exists(vars, this(form))
    else throw new IllegalArgumentException("There is a name class in a substitution " + vars + " and " + l)

    case x: Modality => if(x.writes.intersect(names(l)).isEmpty) x match {
      case BoxModality(p, f) => BoxModality(this(p), this(f))
      case DiamondModality(p, f) => DiamondModality(this(p), this(f))
      case _ => ???
    } else throw new IllegalArgumentException("There is a name class in a substitution " + x.writes + " and " + l)

    case _: PredicateConstant => for(p <- l) { if(f == p.n) return p.t.asInstanceOf[Formula]}; return f

    // if we find a match, we bind the arguments of our match to what is in the current term
    // then we apply it to the codomain of the substitution
    case ApplyPredicate(func, arg) => for(p <- l) {
      p.n match {
        case ApplyPredicate(pf, parg) => if(func == pf) return constructSubst(parg, arg)(p.t.asInstanceOf[Formula])
        case _ =>
      }
    }; return ApplyPredicate(func, this(arg))

    case Equals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => Equals(d, this(a), this(b))
      case (a: Program,b: Program) => Equals(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case NotEquals(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => NotEquals(d, this(a), this(b))
      case (a: Program,b: Program) => NotEquals(d, this(a), this(b))
      case _ => throw new IllegalArgumentException("Don't know how to handle case" + f)
    }
    case GreaterThan(d, l, r) => (l,r) match {
      case (a: Term,b: Term) => GreaterEquals(d, this(a), this(b))
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
  def apply(t: Term): Term = t match {
    case Neg(s, c) => Neg(s, this(c))
    case Add(s, l, r) => Add(s, this(l), this(r))
    case Subtract(s, l, r) => Subtract(s, this(l), this(r))
    case Multiply(s, l, r) => Multiply(s, this(l), this(r))
    case Divide(s, l, r) => Divide(s, this(l), this(r))
    case Exp(s, l, r) => Exp(s, this(l), this(r))
    case Pair(dom, l, r) => Pair(dom, this(l), this(r))
    case Derivative(_, _) => for(p <- l) { if(t == p.n) return p.t.asInstanceOf[Term]}; return t
    case Variable(_, _, _) => for(p <- l) { if(t == p.n) return p.t.asInstanceOf[Term]}; return t
    // if we find a match, we bind the arguments of our match to what is in the current term
    // then we apply it to the codomain of the substitution
    case Apply(func, arg) => for(p <- l) {
      p.n match {
        case Apply(pf, parg) => if(func == pf) return constructSubst(parg, arg)(p.t.asInstanceOf[Term])
        case _ =>
      }
    }; return Apply(func, this(arg))
    case x: Atom => x
    case _ => throw new UnsupportedOperationException("Not implemented yet")
  }

  def apply(p: Program): Program = p match {
    case Loop(c) => Loop(this(c))
    case Sequence(a, b) => Sequence(this(a), this(b))
    case Choice(a, b) => Choice(this(a), this(b))
    case Parallel(a, b) => Parallel(this(a), this(b))
    case IfThen(a, b) => IfThen(this(a), this(b))
    case IfThenElse(a, b, c) => IfThenElse(this(a), this(b), this(c))
    case x: ProgramConstant => for(pair <- l) { if(p == pair.n) return pair.t.asInstanceOf[Program]}; return p
    case _ => throw new UnsupportedOperationException("Not implemented yet")
  }

}

// uniform substitution
// this rule performs a backward substitution step. That is the substitution applied to the conclusion yields the premise
object UniformSubstition {
  def apply(substitution: Substitution, origin: Sequent) : Rule = new UniformSubstition(substitution, origin)

  private class UniformSubstition(subst: Substitution, origin: Sequent) extends Rule {
    // check that s is indeed derived from origin via subst (note that no reordering is allowed since those operations
    // require explicit rule applications)
    def apply(s: Sequent): List[Sequent] = {
      val eqt = ((acc: Boolean, p: (Formula, Formula)) => subst(p._1) == p._2) // TODO: do we need to allow renaming of bounded variables?
      if(s.pref == origin.pref // universal prefix is identical
        && origin.ante.length == s.ante.length && origin.succ.length == s.succ.length
        && (origin.ante.zip(s.ante)).foldLeft(true)(eqt)  // formulas in ante results from substitution
        && (origin.succ.zip(s.succ)).foldLeft(true)(eqt)) // formulas in succ results from substitution
        List(origin)
      else
        throw new IllegalStateException("Substitution did not yield the expected result")
    }

  }
}


// AX close
object AxiomClose extends AssumptionRule {
  def apply(ass: Position): PositionRule = new AxiomClosePos(ass)

  private class AxiomClosePos(ass: Position) extends PositionRule {
    def apply(p: Position): Rule = {
      require(p.isAnte != ass.isAnte, "Axiom close can only be applied to one formula in the antecedent and one in the succedent")
      new AxiomClose(ass, p)
    }
  }

  private class AxiomClose(ass: Position, p: Position) extends Rule {

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
}

// Impl right

object ImplRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new ImplRight(p)
  }
  private class ImplRight(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case Imply(a, b) => List(Sequent(s.pref, s.ante :+ a, s.succ.updated(p.getIndex, b)))
        case _ => throw new IllegalArgumentException("Implies-Right can only be applied to implications. Tried to apply to: " + f)
      }
    }
  }
}

// Impl left
object ImplLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new ImplLeft(p)
  }
  private class ImplLeft(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case Imply(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a), s.succ), Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
        case _ => throw new IllegalArgumentException("Implies-Left can only be applied to implications. Tried to apply to: " + f)
      }
    }
  }
}

// Not right
object NotRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new NotRight(p)
  }
  private class NotRight(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case Not(a) => List(Sequent(s.pref, s.ante :+ a, s.succ.patch(p.getIndex, Nil, 1)))
        case _ => throw new IllegalArgumentException("Not-Right can only be applied to negation. Tried to apply to: " + f)
      }
    }
  }
}

// Not left
object NotLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new NotLeft(p)
  }
  private class NotLeft(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case Not(a) => List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ :+ a))
        case _ => throw new IllegalArgumentException("Not-Left can only be applied to negation. Tried to apply to: " + f)
      }
    }
  }
}

// And right
object AndRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new AndRight(p)
  }
  private class AndRight(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case And(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex,a)), Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, b)))
        case _ => throw new IllegalArgumentException("And-Right can only be applied to conjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// And left
object AndLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new AndLeft(p)
  }
  private class AndLeft(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case And(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex, a) :+ b, s.succ))
        case _ => throw new IllegalArgumentException("And-Left can only be applied to conjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// Or right
object OrRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new OrRight(p)
  }
  private class OrRight(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.succ(p.getIndex)
      f match {
        case Or(a, b) => List(Sequent(s.pref, s.ante, s.succ.updated(p.getIndex, a) :+ b))
        case _ => throw new IllegalArgumentException("Or-Right can only be applied to disjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// Or left
object OrLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new OrLeft(p)
  }
  private class OrLeft(p: Position) extends Rule {
    def apply(s: Sequent): List[Sequent] = {
      val f = s.ante(p.getIndex)
      f match {
        case Or(a, b) => List(Sequent(s.pref, s.ante.updated(p.getIndex,a), s.succ), Sequent(s.pref, s.ante.updated(p.getIndex, b), s.succ))
        case _ => throw new IllegalArgumentException("Or-Left can only be applied to disjunctions. Tried to apply to: " + f)
      }
    }
  }
}

// Lookup Lemma (different justifications: Axiom, Lemma with proof, Oracle Lemma)

// remove duplicate antecedent (this should be a tactic)
// remove duplicate succedent (this should be a tactic)
// hide
object HideLeft extends PositionRule {
  def apply(p: Position): Rule = {
    assert(p.isAnte)
    new Hide(p)
  }
}
object HideRight extends PositionRule {
  def apply(p: Position): Rule = {
    assert(!p.isAnte)
    new Hide(p)
  }
}
class Hide(p: Position) extends Rule {
  def apply(s: Sequent): List[Sequent] =
    if(p.isAnte)
      List(Sequent(s.pref, s.ante.patch(p.getIndex, Nil, 1), s.succ))
    else
      List(Sequent(s.pref, s.ante, s.succ.patch(p.getIndex, Nil, 1)))
}


// maybe:

// close by true (do we need this or is this derived?)

// alpha conversion

// quantifier instantiation

// remove known

// skolemize

// unskolemize

// forall-I

// forall-E

// merge sequent (or is this derived?)



// vim: set ts=4 sw=4 et:
