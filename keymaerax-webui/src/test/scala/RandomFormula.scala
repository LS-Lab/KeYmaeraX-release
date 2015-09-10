/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
package test

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import scala.util.Random
import scala.collection.immutable._

/**
 * Random formula generator and random term generator and random program generator
 * for testing purposes.
 * @author Andre Platzer
 * @param seed the random seed, for repeatable random testing purposes.
 */
class RandomFormula(val seed: Long = new Random().nextLong()) {
  println("RandomFormula(" + seed + ") seed to regenerate\n\n")
  val rand: Random = new Random(seed)
  private val shortProbability = 0.10
  private val randomReps = 500

  def nextTerm(size : Int) = nextT(nextNames("z", size / 3 + 1), size)

  def nextFormula(size : Int) = nextF(nextNames("z", size / 3 + 1), size)

  def nextProgram(size : Int) = nextP(nextNames("z", size / 3 + 1), size)

  def nextDotTerm(size : Int) = nextT(nextNames("z", size / 3 + 1), size, true)

  def nextDotFormula(size : Int) = nextF(nextNames("z", size / 3 + 1), size, true, true)

  def nextDotProgram(size : Int) = nextP(nextNames("z", size / 3 + 1), size, true, false)

  def nextFormulaContext(size : Int): Context[Formula] = {
    import Augmentors._
    val fml = nextF(nextNames("z", size / 3 + 1), 2*size, false, false)
    for (j <- 1 to randomReps) {
      //@todo min(size, fml.size)
      val pos = nextPosition(size).inExpr
      try { return fml.at(pos)._1 }
      catch {case _: IllegalArgumentException => }
    }
    throw new IllegalStateException("Monte Carlo generation of context failed despite " + randomReps + " rounds for " + fml)
  }



  def nextPosition(size : Int): Position = if (rand.nextBoolean())
    AntePosition(rand.nextInt(size), PosInExpr(nextPos(size)))
  else
    SuccPosition(rand.nextInt(size), PosInExpr(nextPos(size)))

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

  def nextF(vars : IndexedSeq[Variable], n : Int, dotTs: Boolean = false, dotFs: Boolean = false) : Formula = {
	  require(n>=0)
	  if (n == 0 || rand.nextFloat()<=shortProbability) return if (dotFs && rand.nextInt(100)>=70) {assert(dotFs);DotFormula} else True
      val r = rand.nextInt(if (dotFs) 300 else 290)
      r match {
        case 0 => False
        case 1 => True
        case it if 2 until 10 contains it => Equal(nextT(vars, n-1, dotTs), nextT(vars, n-1, dotTs))
        case it if 10 until 20 contains it => Not(nextF(vars, n-1, dotTs, dotFs))
        case it if 20 until 30 contains it => And(nextF(vars, n-1, dotTs, dotFs), nextF(vars, n-1, dotTs, dotFs))
        case it if 30 until 40 contains it => Or(nextF(vars, n-1, dotTs, dotFs), nextF(vars, n-1, dotTs, dotFs))
        case it if 40 until 50 contains it => Imply(nextF(vars, n-1, dotTs, dotFs), nextF(vars, n-1, dotTs, dotFs))
        case it if 50 until 60 contains it => Equiv(nextF(vars, n-1, dotTs, dotFs), nextF(vars, n-1, dotTs, dotFs))
        case it if 60 until 70 contains it => NotEqual(nextT(vars, n-1, dotTs), nextT(vars, n-1, dotTs))
        case it if 70 until 80 contains it => GreaterEqual(nextT(vars, n-1, dotTs), nextT(vars, n-1, dotTs))
        case it if 80 until 90 contains it => LessEqual(nextT(vars, n-1, dotTs), nextT(vars, n-1, dotTs))
        case it if 90 until 100 contains it => Greater(nextT(vars, n-1, dotTs), nextT(vars, n-1, dotTs))
        case it if 100 until 110 contains it => Less(nextT(vars, n-1, dotTs), nextT(vars, n-1, dotTs))
        case it if 110 until 140 contains it => Forall(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, dotTs, dotFs))
        case it if 140 until 170 contains it => Exists(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, dotTs, dotFs))
//case it if 110 until 170 contains it => True
        case it if 170 until 230 contains it => Box(nextP(vars, n-1, dotTs, dotFs), nextF(vars, n-1, dotTs, dotFs))
        case it if 230 until 290 contains it => Diamond(nextP(vars, n-1, dotTs, dotFs), nextF(vars, n-1, dotTs, dotFs))
		    case it if 290 until 400 contains it => assert(dotFs); DotFormula
        case _ => throw new IllegalStateException("random number generator range for formula generation produces the right range " + r)
      }
  }

  def nextT(vars : IndexedSeq[Variable], n : Int, dots: Boolean = false) : Term = {
      require(n>=0)
      if (n == 0 || rand.nextFloat()<=shortProbability) return if (dots && rand.nextInt(100)>=50) {assert(dots); DotTerm} else Number(BigDecimal(0))
      // TODO IfThenElseTerm not yet supported
      val r = rand.nextInt(if (dots) 70 else 60/*+1*/)
	    r match {
        case 0 => Number(BigDecimal(0))
		    case it if 1 until 10 contains it => if (rand.nextBoolean()) Number(BigDecimal(rand.nextInt(100))) else Number(BigDecimal(-rand.nextInt(100)))
        case it if 10 until 20 contains it => vars(rand.nextInt(vars.length))
        case it if 20 until 30 contains it => Plus(nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 30 until 40 contains it => Minus(nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 40 until 50 contains it => Times(nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 50 until 55 contains it => Divide(nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 55 until 60 contains it => Power(nextT(vars, n-1, dots), Number(BigDecimal(rand.nextInt(6))))
        case it if 60 until 100 contains it => assert(dots); DotTerm
        // TODO IfThenElseTerm not yet supported
//        case it if 60 until 62 contains it => IfThenElseTerm(nextF(vars, n-1), nextT(vars, n-1), nextT(vars, n-1))
		    case _ => throw new IllegalStateException("random number generator range for term generation produces the right range " + r)
      }
    }

    def nextP(vars : IndexedSeq[Variable], n : Int, dotTs: Boolean = false, dotFs: Boolean = false) : Program = {
  	  require(n>=0)
  	  if (n == 0 || rand.nextFloat()<=shortProbability) return Test(True)
        val r = rand.nextInt(190)
        r match {
          case 0 => Test(False)
          case 1 => Test(True)
          case it if 2 until 10 contains it => val v = vars(rand.nextInt(vars.length)); Assign(v, v)
          case it if 10 until 20 contains it => Test(nextF(vars, n-1, dotTs, dotFs))
          case it if 20 until 30 contains it => Assign(vars(rand.nextInt(vars.length)), nextT(vars, n-1, dotTs))
          case it if 30 until 40 contains it => AssignAny(vars(rand.nextInt(vars.length)))
          case it if 40 until 50 contains it => ODESystem(nextODE(vars, n, 0, vars.length, dotTs), nextF(vars, n-1, dotTs, dotFs))
          case it if 50 until 100 contains it => Choice(nextP(vars, n-1, dotTs, dotFs), nextP(vars, n-1, dotTs, dotFs))
          case it if 100 until 150 contains it => Compose(nextP(vars, n-1, dotTs, dotFs), nextP(vars, n-1, dotTs, dotFs))
          case it if 150 until 200 contains it => Loop(nextP(vars, n-1, dotTs, dotFs))
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
    if (lower == upper-1) return AtomicODE(DifferentialSymbol(vars(lower)), nextT(vars, 0, dotTs))
    val v = lower + rand.nextInt(upper-lower)
    assert(lower <= v && v < upper)
    if (n == 0 || rand.nextFloat()<=shortProbability
      || lower==v || v == upper-1) return AtomicODE(DifferentialSymbol(vars(v)), nextT(vars, 0, dotTs))
    val r = rand.nextInt(20)
    r match {
      case it if 0 until 10 contains it => AtomicODE(DifferentialSymbol(vars(v)), nextT(vars, n-1, dotTs))
      case it if 10 until 20 contains it =>
        DifferentialProduct(nextODE(vars, n-1, lower, v, dotTs), nextODE(vars, n-1, v, upper, dotTs))
      case _ => throw new IllegalStateException("random number generator range for ODE generation produces the right range " + r)
    }
  }
}