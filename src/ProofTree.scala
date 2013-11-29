
/* external / helpers */
class Sequence

abstract class Rule {
  abstract def evaluate(sequence : Sequence) : List[Sequence]
}

class Pair[L, R](val left : L, val right : R)

/* class Option */
/* List (apply(n); length) */


/* ??? How to react to append; prepend completing */





/* ================================================================================ */

import scala.concurrent._


/**
 * Proof Tree
 *============
 *
 * Data structure for tracking the goals of a proof. The sequence and parent fields are
 * immutable. Alternatives is an append only read-side lockfree list of alternative rule
 * applications to this goal. Close finalizes this goal by picking one alternative and
 * setting rule and subgoals. All close attempts except the first fail (returning false).
 * Rule and subgoals can be read in this sequence without acquiring locks. Reading subgoals
 * before rule is invalid and may result in goals being set while rule is still invalid.
 *
 * The proof checker is allowed to acces only closed goals and only the variables rule
 * and subgoals via getRule and getSubgoals and the immutable fields sequence and parent.
 */
class ProofTree(val sequence : Sequence, val parent : Option[ProofTree]) {

/* private */
/*---------*/
  @volatile private var rule         : Rule            = Null
  @volatile private var subgoals     : List[ProofTree] = Nil
  @volatile private var alternatives : List[Pair[Rule, List[ProofTree]]]

  /**
   * prepend the result of rule application as one alternative to the proof tree
   *
   * (sequential / synchronized)
   */
  synchronized 
  private def prepend(subgoal : Pair[Rule, List[ProofTree]]) : ProofTree {
    alternatives = subgoal ++ alternatives
    return this
  }

/* public */
/*--------*/

  /**
   * list of alternative rule applications
   */
  getAlternatives : List[Pair[Rule, List[ProofTree]]] = alternatives

  /**
   * the rule closing this goal or Null if the goal has not yet been closed
   */
  getRule : Rule = rule

  /**
   * the list of subgoals if this goal is closed (i.e., getRule != Null). undefined otherwise
   * [while closing the goal, there is a short window during which subgoals is already set while
   *  rule is still Null]
   */
  getSubgoals : List[ProofTree] = subgoals

  /**
   * true iff the goal has been closed (i.e., getRule != Null)
   */
  isClosed : Boolean = (rule != Null)

  /**
   * apply rule to obtain a new alternative deduction for this sequence
   */
  def apply(rule : Rule) : Future[ProofTree] = {
    alternative = new Pair(rule, rule.evaluate(sequence).map[ProofTree](new ProofTree(_, this)))
    /* !!! dispatch prepend */
    prepend(rule, alternative)
  }

  /**
   * close the goal by selecting one alternative
   */
  synchronized
  def close(n : Int) : Boolean = {
    if (! n < length(alternatives)) throw new IllegalArgumentException

    if (isClosed) {
      return false
    } else {
      alternative = alternatives.apply(n)
      subgoals    = alternative.right
      rule        = alternative.left
      return true
    }
  }

}
