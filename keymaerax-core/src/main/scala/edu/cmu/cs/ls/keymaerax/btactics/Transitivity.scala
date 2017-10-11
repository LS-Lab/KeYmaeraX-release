/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleUserGeneratedError}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
  * Proves goals of the form a>=b,b>=c |- a >= c with arbitrarily many intermediate (in)equalities.
  *
  * These goals ought to close by QE, but often don't (e.g., when function symbols are involved).
  *
  * @todo There's a bug -- this function might find the string of inequalities a >= b >= c and claim it's a proof for a>c.
  *       The fix for this bug is to check in search() that the result contains at least one strict inequalities if the goal()
  *       has form a > c.
  * @author Nathan Fulton
  */
object Transitivity {
  val closeTransitive = "closeTransitive" by ((s: Sequent) => {

    val transitiveInequalities = search(s) match {
      case Some(fs) => fs
      case None => throw new BelleUserGeneratedError(s"Could not find a set of transitive inequalities that imply the postcondition of ${s}")
    }

    DebuggingTactics.debug(s"[closeTransitive] formulas: ${transitiveInequalities.map(_.prettyString).reduce(_ + "," + _)}", true)
    TactixLibrary.cut(transitivityLemma(transitiveInequalities)) <(
      instantiations(transitiveInequalities).map(variableAndTerm => {
        val instantiateTactic : BelleExpr = TactixLibrary.allL(variableAndTerm._1, variableAndTerm._2)('Llast)
        instantiateTactic
      }).reduce(_ & _) & TactixLibrary.implyL('Llast) <(
        closeIds(transitiveInequalities)
        ,
        TactixLibrary.closeId
      )
      ,
      TactixLibrary.cohideR('Rlast) & TactixLibrary.QE
    )

  })

  def closeIds(formulas: List[Formula]) : BelleExpr = formulas match {
    case e :: Nil => TactixLibrary.closeId
    case e :: es => TactixLibrary.andR('Rlast) <(closeIds(es),TactixLibrary.closeId)
  }

  /** Computes the sequence of variable ~> term instantiations for the transitivity lemma.
    * @todo rewrite this code so it's even remotely readable... */
  def instantiations(formulas: List[Formula]) : List[(Variable, Term)] = {
    val inequalities = formulas.map(decomposeInequality(_).get)
    ("TRANS0".asVariable, inequalities.head._2) :: inequalities.map(_._3).zipWithIndex.map(x => (s"TRANS${x._2 + 1}".asVariable, x._1))
  }

  def transitivityLemma(formulas: List[Formula]) = {
    assert(formulas.length >= 2)
    val inequalities =
      formulas.zipWithIndex.map(fi => {
        val (f,i) = fi
        getConstructor(f)(s"TRANS$i".asTerm, s"TRANS${i+1}".asTerm)
      }).reduce(And)

    val formula = Imply(inequalities, s"TRANS0 >= TRANS${formulas.length}".asFormula)

    Range(0, formulas.length + 1).foldRight[Formula](formula)((i, f) => Forall(immutable.Seq(s"TRANS$i".asVariable), f))
  } ensuring(f => StaticSemantics.freeVars(f).isEmpty)

  /** Translates a [[search]] result into an ordered list of positions of the formulas in the antecedent. */
  def searchResultToPositionList(s : Sequent, fs : List[Formula]) = fs.map(f => s.ante.zipWithIndex.find(_._1 == f).get._2).map(x => -x - 1)

  /** Searches for a chain on inequalities a_1 ~ a_2 ~ ... ~ a_n where ~ are all in the same TransitivtyDirection. */
  def search(s: Sequent) : Option[List[Formula]] = {
    assert(s.succ.length == 1, s"[closeTransitive] Expected a succcedent with len == 1 but found ${s.succ}")

    val (direction, start, end) = decomposeInequality(s.succ.head) match {
      case Some(x) => x
      case None => throw new BelleUserGeneratedError(s"[closeTransitive] Expected succedent of form a ~ b but found ${s.succ(0).prettyString}")
    }

    val startingPrefixes = initialSearchSet(s,direction,start).map(f => List(f)).toSet[List[Formula]]
    searchHelper(s, direction, end, startingPrefixes)
  }

  private def decomposeInequality(inequality: Formula) : Option[(TransitivityDirection, Term, Term)] = inequality match {
    case GreaterEqual(left, right) => Some((GreaterDir, left, right))
    case Greater(left, right) => Some((GreaterDir, left, right))
    case LessEqual(left, right) => Some((LesserDir, left, right))
    case Less(left, right) => Some((LesserDir, left, right))
    case Equal(left, right) => Some((EqualDir, left, right))
    case _ => None
  }

  private def getConstructor(inequality: Formula) : (Term, Term) => Formula = inequality match {
    case GreaterEqual(left, right) => (a:Term,b:Term) => GreaterEqual(a,b)
    case Greater(left, right) => (a:Term,b:Term) => Greater(a,b)
    case LessEqual(left, right) => (a:Term,b:Term) => LessEqual(a,b)
    case Less(left, right) => (a:Term,b:Term) => Less(a,b)
    case Equal(left, right) => (a:Term,b:Term) => Equal(a,b)
  }

  private def initialSearchSet(s:Sequent, direction: TransitivityDirection, start: Term) = s.ante.filter(f => {
    decomposeInequality(f) match {
      case Some(x) if((x._1 == EqualDir || x._1 == direction) && x._2 == start) => true
      case _ => false
    }
  })

  private def searchHelper(s: Sequent, direction: TransitivityDirection, end: Term, prefixes: Set[List[Formula]]) : Option[List[Formula]] = {
    //Extends a1 ~ a2 ~ .. ~ a_k with all a_n s.t. a_n ~ a_k occurs in the antecedent and all ~'s have the same direction.
    val prefixExtensions : Set[List[Formula]] = prefixes.map(prefix => {
      val prefixEndTerm = decomposeInequality(prefix.last).get._3

      val extensions : IndexedSeq[Formula] = s.ante.filter(anteF => anteF match {
        case Less(al, ar) if(al == prefixEndTerm && direction == LesserDir) => true
        case LessEqual(al, ar) if(al == prefixEndTerm && direction == LesserDir) => true
        case Greater(al, ar) if(al == prefixEndTerm && direction == GreaterDir) => true
        case GreaterEqual(al,ar) if(al == prefixEndTerm && direction == GreaterDir) => true
        case Equal(al, ar) if(al == prefixEndTerm) => true
        case _ => false
      })

      if(extensions.isEmpty) Set() //We've reached the end of this prefix and did not find the goal.
      else extensions.map(prefix :+ _).toSet
    }).flatten

    val cycleFreePrefixes = filterCycles(prefixExtensions)

    cycleFreePrefixes.find(prefix => decomposeInequality(prefix.last).get._3 == end) match {
      case Some(completedPrefix) => Some(completedPrefix)
      case None if(cycleFreePrefixes.size > 0) => searchHelper(s, direction, end, cycleFreePrefixes)
      case None if(cycleFreePrefixes.size == 0) => None
    }
  }

  /** Filters out the prefixes with cyclical inequalities; e.g., a >= b >= a. */
  private def filterCycles(prefixes: Set[List[Formula]]) = prefixes.filter(prefix => !hasTermCycle(prefix))

  /** Returns true iff the prefix has form a >= b :: ... :: b >= a :: Nil */
  private def hasTermCycle(prefix: List[Formula], termsSoFar : Set[Term] = Set()) : Boolean = prefix match {
    case Nil => false
    case e :: es => {
      val Some((direction, left, right)) = decomposeInequality(e)
      if(termsSoFar.contains(right)) true else hasTermCycle(es, termsSoFar.union(Set(right)))
    }
  }

  /** Used to indicate the "direction" of an inequality a ~ b.
    * E.g., by mapping (a >= b) and (a > b) to (GreaterDir, a, b) */
  private trait TransitivityDirection
  private object EqualDir extends TransitivityDirection
  private object GreaterDir extends TransitivityDirection
  private object LesserDir extends TransitivityDirection
}
