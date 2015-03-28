import edu.cmu.cs.ls.keymaera.core._
import scala.util.Random
import scala.collection.immutable._

/**
 * Random formula generator and random term generator and random program generator
 * for testing purposes.
 * @author aplatzer
 */
class RandomFormula(val rand : Random = new Random()) {
  private def shortProbability = 0.10
  def nextTerm(size : Int) = nextT(nextNames("z", size / 3 + 1), size)

  def nextFormula(size : Int) = nextF(nextNames("z", size / 3 + 1), size)

  def nextProgram(size : Int) = nextP(nextNames("z", size / 3 + 1), size)

  def nextDotTerm(size : Int) = nextT(nextNames("z", size / 3 + 1), size, true)

  def nextDotFormula(size : Int) = nextF(nextNames("z", size / 3 + 1), size, true)

  def nextDotProgram(size : Int) = nextP(nextNames("z", size / 3 + 1), size, true)


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
  
  def nextF(vars : IndexedSeq[Variable], n : Int, dots: Boolean = false) : Formula = {
	  require(n>=0)
	  if (n == 0 || rand.nextFloat()<=shortProbability) return return if (dots && rand.nextInt(100)>=70) CDotFormula else True
      val r = rand.nextInt(if (dots) 240 else 230/*+1*/)
      r match {
        case 0 => False
        case 1 => True
        case it if 2 until 10 contains it => Equals(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 10 until 20 contains it => Not(nextF(vars, n-1, dots))
        case it if 20 until 30 contains it => And(nextF(vars, n-1, dots), nextF(vars, n-1, dots))
        case it if 30 until 40 contains it => Or(nextF(vars, n-1, dots), nextF(vars, n-1, dots))
        case it if 40 until 50 contains it => Imply(nextF(vars, n-1, dots), nextF(vars, n-1, dots))
        case it if 50 until 60 contains it => Equiv(nextF(vars, n-1, dots), nextF(vars, n-1, dots))
        case it if 60 until 70 contains it => NotEquals(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 70 until 80 contains it => GreaterEqual(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 80 until 90 contains it => LessEqual(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 90 until 100 contains it => GreaterThan(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 100 until 110 contains it => LessThan(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 110 until 140 contains it => Forall(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, dots))
        case it if 140 until 170 contains it => Exists(Seq(vars(rand.nextInt(vars.length))), nextF(vars, n-1, dots))
        case it if 170 until 200 contains it => BoxModality(nextP(vars, n-1, dots), nextF(vars, n-1, dots))
        case it if 200 until 230 contains it => DiamondModality(nextP(vars, n-1, dots), nextF(vars, n-1, dots))
		    case it if 230 until 300 contains it => CDotFormula
        case _ => throw new IllegalStateException("random number generator range for formula generation produces the right range " + r)
      }
  }

  def nextT(vars : IndexedSeq[Variable], n : Int, dots: Boolean = false) : Term = {
      require(n>=0)
      if (n == 0 || rand.nextFloat()<=shortProbability) return if (dots && rand.nextInt(100)>=50) CDot else Number(BigDecimal(0))
      // TODO IfThenElseTerm not yet supported
      val r = rand.nextInt(if (dots) 70 else 60/*+1*/)
	    r match {
        case 0 => Number(BigDecimal(0))
		    case it if 1 until 10 contains it => if (rand.nextBoolean()) Number(BigDecimal(rand.nextInt(100))) else Number(BigDecimal(-rand.nextInt(100)))
        case it if 10 until 20 contains it => vars(rand.nextInt(vars.length))
        case it if 20 until 30 contains it => Add(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 30 until 40 contains it => Subtract(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 40 until 50 contains it => Multiply(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 50 until 55 contains it => Divide(Real, nextT(vars, n-1, dots), nextT(vars, n-1, dots))
        case it if 55 until 60 contains it => Exp(Real, nextT(vars, n-1, dots), Number(BigDecimal(rand.nextInt(6))))
        case it if 60 until 100 contains it => CDot
        // TODO IfThenElseTerm not yet supported
//        case it if 60 until 62 contains it => IfThenElseTerm(nextF(vars, n-1), nextT(vars, n-1), nextT(vars, n-1))
		    case _ => throw new IllegalStateException("random number generator range for term generation produces the right range " + r)
      }
    }

    def nextP(vars : IndexedSeq[Variable], n : Int, dots: Boolean = false) : Program = {
  	  require(n>=0)
  	  if (n == 0 || rand.nextFloat()<=shortProbability) return Test(True)
        val r = rand.nextInt(190)
        r match {
          case 0 => Test(False)
          case 1 => Test(True)
          case it if 2 until 10 contains it => val v = vars(rand.nextInt(vars.length)); Assign(v, v)
          case it if 10 until 20 contains it => Test(nextF(vars, n-1, dots))
          case it if 20 until 30 contains it => Assign(vars(rand.nextInt(vars.length)), nextT(vars, n-1, dots))
          case it if 30 until 40 contains it => NDetAssign(vars(rand.nextInt(vars.length)))
          case it if 40 until 50 contains it => ODESystem(Seq(), nextODE(vars, n, dots), nextF(vars, n-1, dots))
          case it if 50 until 100 contains it => Choice(nextP(vars, n-1, dots), nextP(vars, n-1, dots))
          case it if 100 until 150 contains it => Sequence(nextP(vars, n-1, dots), nextP(vars, n-1, dots))
          case it if 150 until 200 contains it => Loop(nextP(vars, n-1, dots))
      		case _ => throw new IllegalStateException("random number generator range for program generation produces the right range " + r)
        }
    }

    def nextODE(vars : IndexedSeq[Variable], n : Int, dots: Boolean = false) : DifferentialProgram = {
      if (n == 0 || rand.nextFloat()<=shortProbability) return new EmptyODE()
      val r = rand.nextInt(20)
        r match {
          case 0 => new EmptyODE()
          case it if 1 until 10 contains it => AtomicODE(Derivative(Real, vars(rand.nextInt(vars.length))), nextT(vars, n-1, dots))
          case it if 10 until 20 contains it => ODEProduct(nextODE(vars, n-1, dots), nextODE(vars, n-1, dots))
          case _ => throw new IllegalStateException("random number generator range for ODE generation produces the right range " + r)
        }
    }
}