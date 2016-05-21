/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import scala.util.Random
import scala.collection.immutable._

/**
 * Random formula generator and random term generator and random program generator
 * for testing purposes.
 * Each use of RandomFormula will print a random seed with which the same random tests can be repeated.
 * {{{
 *   val rand = RandomFormula()
 *   // will print something like RandomFormula(-4317240407825764493L) on screen
 *   // The same sequence of pseudo-random formulas can, thus, be regenerated again from
 *   val sameRand = RandomFormula(-4317240407825764493L)
 * }}}
  *
  * @author Andre Platzer
 * @param seed the random seed, for repeatable random testing purposes.
 */
class RandomFormula(val seed: Long = new Random().nextLong()) {
  println("RandomFormula(" + seed + "L) seed will regenerate the same random sequence\n\n")
  val rand: Random = new Random(seed)
  private val shortProbability = 0.10
  private val randomReps = 500

  def nextTerm(size : Int) = nextT(nextNames("z", size / 3 + 1), size)

  def nextFormula(size : Int) = nextF(nextNames("z", size / 3 + 1), size)

  def nextProgram(size : Int) = nextP(nextNames("z", size / 3 + 1), size)

  // dot generators default to no diffs
  def nextDotTerm(size : Int) = nextT(nextNames("z", size / 3 + 1), size, true)

  def nextDotFormula(size : Int) = nextF(nextNames("z", size / 3 + 1), size, true, true)

  def nextDotProgram(size : Int) = nextP(nextNames("z", size / 3 + 1), size, true, false)

  def nextFormulaContext(size : Int): Context[Formula] = {
    import Augmentors._
    val fml = nextF(nextNames("z", size / 3 + 1), 2*size, true, false, false, false)
    for (j <- 1 to randomReps) {
      //@todo min(size, fml.size)
      val pos = nextPosition(size).inExpr
      try { return fml.at(pos)._1 }
      catch {case _: IllegalArgumentException => }
    }
    throw new IllegalStateException("Monte Carlo generation of context failed despite " + randomReps + " rounds for " + fml)
  }

  def nextSequent(size : Int): Sequent = {
    val vars = nextNames("z", size / 3 + 1)
    Sequent(Nil, Range(0,rand.nextInt(size/2)).map(i => nextF(vars, size-1)), Range(0,rand.nextInt(size/2)).map(i => nextF(vars, size-1)))
  }

  /** Generate a random proof of a random tautological sequents */
  def nextProvable(size: Int): Provable = nextPr(nextNames("z", size / 3 + 1), size)

  /** Generate a random (propositionally) provable formula */
  //def nextProved(size: Int): Sequent = nextProvable(size).conclusion

  /** weaken p1 and p2 such that they have the same context except at position `pos` */
  private def weakenRight(p1: Provable, p2: Provable, pos: SuccPos): (Provable,Provable) = {
    require(pos.getIndex==0, "currently only implemented for first succedent position")
    ???
  }

  /** Apply Rule Forward: like Provable.apply(Sequent,Rule) except for two premises */
  private def prolong(p1: Provable, p2: Provable, newConsequence: Sequent, rule: Rule): Provable = {
    Provable.startProof(newConsequence)(rule, 0)(p1, 0)(p2, 1)
  }

  /** padding such that at least lefts many formula in antecedent of pr by weakening */
  private def padLeft(vars : IndexedSeq[Variable], n : Int, pr: Provable, lefts: Int): Provable = {
    require(lefts>=0)
    if (pr.conclusion.ante.length >= lefts) pr
    else {
      val fml = nextF(vars, n)
      padLeft(vars, n, pr(pr.conclusion.glue(Sequent(Nil, IndexedSeq(fml), IndexedSeq())), HideLeft(AntePos(pr.conclusion.ante.length))), lefts)
    }
  }

  /** padding such that at least rights many formula in succedent of pr by weakening */
  private def padRight(vars : IndexedSeq[Variable], n : Int, pr: Provable, rights: Int): Provable = {
    require(rights>=0)
    if (pr.conclusion.succ.length >= rights) pr
    else {
      val fml = nextF(vars, n)
      padRight(vars, n, pr(pr.conclusion.glue(Sequent(Nil, IndexedSeq(), IndexedSeq(fml))), HideRight(SuccPos(pr.conclusion.succ.length))), rights)
    }
  }

  // closer to implementation-specific

  def nextPosition(size : Int): Position = if (rand.nextBoolean())
    AntePosition.base0(rand.nextInt(size), PosInExpr(nextPos(size)))
  else
    SuccPosition.base0(rand.nextInt(size), PosInExpr(nextPos(size)))

  def unfoldRight[A, B](seed: B)(f: B => Option[(A,B)]): List[A] = f(seed) match {
    case Some((a,b)) => a :: unfoldRight(b)(f)
    case None => Nil
  }
  
  def nextNames(name: String, n : Int) : IndexedSeq[Variable] = unfoldRight(n) { n =>
    if (n==0)
      None
    else
      Some((Variable(name + n, None, Real), n-1))
      //Some(("x" + (rand.alphanumeric take 5).fold("")((s:String,t:String)=>s+t), n-1))
  }.to[IndexedSeq]

  private def nextPos(n : Int) : List[Int] = {
    require(n >= 0)
    if (n == 0 || rand.nextFloat() <= shortProbability) return Nil
    (if (rand.nextBoolean()) 1 else 0) :: nextPos(n - 1)
  }

  // random generator implementations

  def nextT(vars : IndexedSeq[Variable], n : Int, dots: Boolean = false) : Term = nextT(vars, n, dots, !dots)

  def nextT(vars : IndexedSeq[Variable], n : Int, dots: Boolean, diffs: Boolean) : Term = {
    require(n>=0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return if (dots && rand.nextInt(100)>=50) {assert(dots); DotTerm} else Number(BigDecimal(0))
    // TODO IfThenElseTerm not yet supported
    val r = rand.nextInt(if (dots) 98 else 88/*+1*/)
    r match {
      case 0 => Number(BigDecimal(0))
      case it if 1 until 10 contains it => if (rand.nextBoolean()) Number(BigDecimal(rand.nextInt(100))) else Number(BigDecimal(-rand.nextInt(100)))
      case it if 10 until 20 contains it => vars(rand.nextInt(vars.length))
      case it if 20 until 30 contains it => Plus(nextT(vars, n-1, dots, diffs), nextT(vars, n-1, dots, diffs))
      case it if 30 until 40 contains it => Minus(nextT(vars, n-1, dots, diffs), nextT(vars, n-1, dots, diffs))
      case it if 40 until 50 contains it => Times(nextT(vars, n-1, dots, diffs), nextT(vars, n-1, dots, diffs))
      case it if 50 until 55 contains it => Divide(nextT(vars, n-1, dots, diffs), nextT(vars, n-1, dots, diffs))
      case it if 55 until 60 contains it => Power(nextT(vars, n-1, dots, diffs), Number(BigDecimal(rand.nextInt(6))))
      case it if 60 until 70 contains it => if (diffs) DifferentialSymbol(vars(rand.nextInt(vars.length))) else Number(BigDecimal(rand.nextInt(100)))
      case it if 70 until 80 contains it => if (diffs) Differential(nextT(vars, n-1, dots, false)) else Number(BigDecimal(rand.nextInt(100)))
      case it if 80 until 84 contains it => FuncOf(Function("gg",None,Unit,Real),Nothing)
      case it if 84 until 88 contains it => FuncOf(Function("ff",None,Real,Real), nextT(vars, n-1, dots, diffs))
      case it if 88 until 200 contains it => assert(dots); DotTerm
      // TODO IfThenElseTerm not yet supported
      //        case it if 60 until 62 contains it => IfThenElseTerm(nextF(vars, n-1), nextT(vars, n-1), nextT(vars, n-1))
      case _ => throw new IllegalStateException("random number generator range for term generation produces the right range " + r)
    }
  }


  def nextF(vars : IndexedSeq[Variable], n : Int, modals: Boolean = true, dotTs: Boolean = false, dotFs: Boolean = false) : Formula = nextF(vars, n, modals, dotTs, dotFs, !(dotTs||dotFs))
  def nextF(vars : IndexedSeq[Variable], n : Int, modals: Boolean, dotTs: Boolean, dotFs: Boolean, diffs: Boolean) : Formula = {
	  require(n>=0)
	  if (n == 0 || rand.nextFloat()<=shortProbability) return if (dotFs && rand.nextInt(100)>=70) {assert(dotFs);DotFormula} else True
      val r = rand.nextInt(if (dotFs) 320 else 310)
      r match {
        case 0 => False
        case 1 => True
        case it if 2 until 10 contains it => Equal(nextT(vars, n-1, dotTs, diffs), nextT(vars, n-1, dotTs, diffs))
        case it if 10 until 20 contains it => Not(nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 20 until 30 contains it => And(nextF(vars, n-1, modals, dotTs, dotFs, diffs), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 30 until 40 contains it => Or(nextF(vars, n-1, modals, dotTs, dotFs, diffs), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 40 until 50 contains it => Imply(nextF(vars, n-1, modals, dotTs, dotFs, diffs), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 50 until 60 contains it => Equiv(nextF(vars, n-1, modals, dotTs, dotFs, diffs), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
          //@todo Predicate, Predicational
        case it if 60 until 70 contains it => NotEqual(nextT(vars, n-1, dotTs, diffs), nextT(vars, n-1, dotTs, diffs))
        case it if 70 until 80 contains it => GreaterEqual(nextT(vars, n-1, dotTs, diffs), nextT(vars, n-1, dotTs, diffs))
        case it if 80 until 90 contains it => LessEqual(nextT(vars, n-1, dotTs, diffs), nextT(vars, n-1, dotTs, diffs))
        case it if 90 until 100 contains it => Greater(nextT(vars, n-1, dotTs, diffs), nextT(vars, n-1, dotTs, diffs))
        case it if 100 until 110 contains it => Less(nextT(vars, n-1, dotTs, diffs), nextT(vars, n-1, dotTs, diffs))
        case it if 110 until 140 contains it => Forall(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 140 until 170 contains it => Exists(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
//case it if 110 until 170 contains it => True
        case it if 170 until 230 contains it => Box(nextP(vars, n-1, dotTs, dotFs, diffs), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 230 until 290 contains it => Diamond(nextP(vars, n-1, dotTs, dotFs, diffs), nextF(vars, n-1, modals, dotTs, dotFs, diffs))
        case it if 290 until 300 contains it => if (diffs) DifferentialFormula(nextF(vars, n-1, false, false, false, false)) else False
        case it if 300 until 304 contains it => PredOf(Function("qq",None,Unit,Bool),Nothing)
        case it if 304 until 308 contains it => PredOf(Function("pp",None,Real,Bool), nextT(vars, n-1, dotTs, diffs))
        case it if 308 until 310 contains it => PredicationalOf(Function("PP",None,Bool,Bool), nextF(vars, n-1, modals, false, false, diffs))
        case it if 310 until 400 contains it => assert(dotFs); DotFormula
        case _ => throw new IllegalStateException("random number generator range for formula generation produces the right range " + r)
      }
  }

  /** whether games are currently allowed */
  private val game: Boolean = try {Dual(AssignAny(Variable("x"))); true} catch {case ignore: IllegalArgumentException => false }

  def nextP(vars : IndexedSeq[Variable], n : Int, dotTs: Boolean = false, dotFs: Boolean = false) : Program = nextP(vars, n, dotTs, dotFs, !(dotTs || dotFs))
  def nextP(vars : IndexedSeq[Variable], n : Int, dotTs: Boolean, dotFs: Boolean, diffs: Boolean) : Program = {
    require(n>=0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return Test(True)
    val r = rand.nextInt(200)
    r match {
      case 0 => Test(False)
      case 1 => Test(True)
      case it if 2 until 10 contains it => val v = vars(rand.nextInt(vars.length)); Assign(v, v)
      case it if 10 until 20 contains it => Test(nextF(vars, n-1, true, dotTs, dotFs, diffs))
      case it if 20 until 30 contains it => Assign(vars(rand.nextInt(vars.length)), nextT(vars, n-1, dotTs, diffs))
      case it if 30 until 40 contains it => AssignAny(vars(rand.nextInt(vars.length)))
      case it if 40 until 50 contains it => ODESystem(nextODE(vars, n, 0, vars.length, dotTs), nextF(vars, n-1, true, dotTs, dotFs, diffs))
      case it if 50 until 100 contains it => Choice(nextP(vars, n-1, dotTs, dotFs, diffs), nextP(vars, n-1, dotTs, dotFs, diffs))
      case it if 100 until 150 contains it => Compose(nextP(vars, n-1, dotTs, dotFs, diffs), nextP(vars, n-1, dotTs, dotFs, diffs))
      case it if (190 until 220 contains it) && game => Dual(nextP(vars, n-1, dotTs, dotFs, diffs))
      case it if 150 until 200 contains it => Loop(nextP(vars, n-1, dotTs, dotFs, diffs))
      case _ => throw new IllegalStateException("random number generator range for program generation produces the right range " + r)
    }
  }

  /**
   * randomly generate an ODE paying attention to avoid duplicates.
   * This algorithm is merg-sort-esque and only generates ODEs for differential equations of
   * vars[lower..upper)
   * It just watches that both subintervals remain nonempty
   */
  def nextODE(vars : IndexedSeq[Variable], n : Int, lower: Int, upper: Int, dotTs: Boolean = false) : DifferentialProgram = {
    require(n>=0)
    require(0<=lower && lower<upper && upper<=vars.length)
    if (lower == upper-1) return AtomicODE(DifferentialSymbol(vars(lower)), nextT(vars, 0, dotTs, false))
    val v = lower + rand.nextInt(upper-lower)
    assert(lower <= v && v < upper)
    if (n == 0 || rand.nextFloat()<=shortProbability
      || lower==v || v == upper-1) return AtomicODE(DifferentialSymbol(vars(v)), nextT(vars, 0, dotTs, false))
    val r = rand.nextInt(20)
    r match {
      case it if 0 until 10 contains it => AtomicODE(DifferentialSymbol(vars(v)), nextT(vars, n-1, dotTs, false))
      case it if 10 until 20 contains it =>
        DifferentialProduct(nextODE(vars, n-1, lower, v, dotTs), nextODE(vars, n-1, v, upper, dotTs))
      case _ => throw new IllegalStateException("random number generator range for ODE generation produces the right range " + r)
    }
  }

  /** Generate a random proof of a random tautological sequent, basically via an external forward sequent calculus */
  def nextPr(vars : IndexedSeq[Variable], n : Int): Provable = {
    require(n>=0)
    if (n == 0 || rand.nextFloat()<=shortProbability) return Provable.startProof(True)(CloseTrue(SuccPos(0)), 0)
    val r = rand.nextInt(70)
    r match {
      case 0 => Provable.startProof(True)(CloseTrue(SuccPos(0)), 0)
      case it if 1 until 10 contains it => val fml = nextF(vars, n - 1); Provable.startProof(Sequent(Nil, IndexedSeq(fml), IndexedSeq(fml)))(Close(AntePos(0),SuccPos(0)), 0)
      case it if 10 until 20 contains it => val p1 = nextPr(vars, n-1); val fml = nextF(vars, n-1);
        p1(p1.conclusion.glue(Sequent(Nil, IndexedSeq(), IndexedSeq(fml))), HideRight(SuccPos(p1.conclusion.succ.length)))
      case it if 20 until 30 contains it => val p1 = nextPr(vars, n-1); val fml = nextF(vars, n-1);
        p1(p1.conclusion.glue(Sequent(Nil, IndexedSeq(fml), IndexedSeq())), HideLeft(AntePos(p1.conclusion.ante.length)))
      case it if 30 until 40 contains it => val p1 = padLeft(vars, n, nextPr(vars, n-1), 2);
        val pos1 = if (p1.conclusion.ante.length<=2) AntePos(0) else AntePos(rand.nextInt(p1.conclusion.ante.length-2))
        p1(Sequent(Nil, p1.conclusion.ante.dropRight(2).patch(pos1.getIndex, And(p1.conclusion.ante.dropRight(1).last, p1.conclusion.ante.last)::Nil, 0),
          p1.conclusion.succ), AndLeft(pos1))
      case it if 40 until 50 contains it => val p1 = padRight(vars, n, nextPr(vars, n-1), 2);
        val pos1 = if (p1.conclusion.succ.length<=2) SuccPos(0) else SuccPos(rand.nextInt(p1.conclusion.succ.length-2))
        p1(Sequent(Nil, p1.conclusion.ante,
          p1.conclusion.succ.dropRight(2).patch(pos1.getIndex, Or(p1.conclusion.succ.dropRight(1).last, p1.conclusion.succ.last)::Nil, 0)),
          OrRight(pos1))
      case it if 50 until 60 contains it => val p1 = padLeft(vars, n, padRight(vars, n, nextPr(vars, n-1), 1), 1);
        val posi1 = rand.nextInt(p1.conclusion.succ.length)
        val pos1 = SuccPos(posi1)
        p1(Sequent(Nil, p1.conclusion.ante.patch(p1.conclusion.ante.length-1,Nil,1),
          p1.conclusion.succ.patch(p1.conclusion.succ.length-1,Nil,1).patch(posi1,
            Imply(p1.conclusion.ante.last, p1.conclusion.succ.last)::Nil
            , 0)), ImplyRight(pos1))
      case it if 60 until 65 contains it => val p1 = padLeft(vars, n, nextPr(vars, n-1), 1);
        val pos1 = if (p1.conclusion.succ.isEmpty) 0 else rand.nextInt(p1.conclusion.succ.length)
        p1(Sequent(Nil,
          p1.conclusion.ante.dropRight(1),
          p1.conclusion.succ.patch(pos1, Not(p1.conclusion(AntePos(p1.conclusion.ante.length-1)))::Nil, 0)),
          NotRight(SuccPos(pos1)))
      case it if 65 until 70 contains it => val p1 = padRight(vars, n, nextPr(vars, n-1), 1);
        val pos1 = if (p1.conclusion.ante.isEmpty) 0 else rand.nextInt(p1.conclusion.ante.length)
        p1(Sequent(Nil,
          p1.conclusion.ante.patch(pos1, Not(p1.conclusion(SuccPos(p1.conclusion.succ.length-1)))::Nil, 0),
          p1.conclusion.succ.dropRight(1)), NotLeft(AntePos(pos1)))
      case it if 70 until 75 contains it => val p1 = padRight(vars, n, nextPr(vars, n-1), 1); val p2 = padRight(vars, n, nextPr(vars, n-1), 1);
        val pos1 = SuccPos(0) //@todo could do other positions if using ExchangeRight: SuccPos(rand.nextInt(Math.min(p1.conclusion.succ.length, p2.conclusion.succ.length)))
        val (pp1, pp2) = weakenRight(p1, p2, pos1)
        prolong(pp1, pp2, pp1.conclusion.updated(pos1, And(pp1.conclusion(pos1),pp2.conclusion(pos1))), AndRight(pos1))
      //@todo more rules such as AndRight
    }
  }

}