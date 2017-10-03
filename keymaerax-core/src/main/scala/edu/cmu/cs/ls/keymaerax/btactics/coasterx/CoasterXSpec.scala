package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.AccelEnvelope.EnvScalar
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.{AFile, Section, _}
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXSpec._
import edu.cmu.cs.ls.keymaerax.core.{Formula, _}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

object AccelEnvelope {
  type EnvScalar = Number
  def scalarLeq(x:EnvScalar,y:EnvScalar):Boolean = x.value <= y.value
  def scalarGeq(x:EnvScalar,y:EnvScalar):Boolean = x.value >= y.value
  def scalarMin(x:EnvScalar, y:EnvScalar):EnvScalar = if(scalarLeq(x,y)) x else y
  def scalarMax(x:EnvScalar, y:EnvScalar):EnvScalar = if(scalarLeq(x,y)) y else x
  val NEG_INF = Number(-1000000.0)
  val POS_INF = Number(1000000.0)
  // Based on ASTM F2291-17 limits for SUSTAINED acceleration >= 40s, making this conservative
  // For short ranges bigger numbers are OK.
  val MIN_RAD:EnvScalar = Number(-1.1)
  val MAX_RAD:EnvScalar = Number(2.0)
  // Ranges for 0 seconds
  val MINN_RAD:EnvScalar = Number(-2.0)
  val MAXX_RAD:EnvScalar = Number(6.0)

  // Same for tangential acceleration, should always be in [-1,1] range for pure gravity coaster
  val MIN_TAN:EnvScalar = Number(-1.5)
  val MAX_TAN:EnvScalar = Number(2.5)
  val MINN_TAN:EnvScalar = Number(-3.5)
  val MAXX_TAN:EnvScalar = Number(6.0)
  val empty = AccelEnvelope(POS_INF, POS_INF, NEG_INF, NEG_INF, POS_INF, NEG_INF, POS_INF, NEG_INF, 1.0)
}
case class AccelEnvelope(private val rMin:EnvScalar, private val rMinAbs:EnvScalar,
                         private val rMax:EnvScalar, private val rMaxAbs:EnvScalar,
                         private val tMin:EnvScalar, private val tMax:EnvScalar,
                        /* Note: vMin, vMax are bounds on v^2 to avoid arbitrary-precision square roots */
                         private val vMin:EnvScalar, private val vMax:EnvScalar,
                         private val feetPerUnit:Double) {
  import AccelEnvelope._

  var centrips:Map[(Int,TPoint), EnvScalar] = Map()
  val FEET_PER_INCH =  0.0833
  val METERS_PER_FOOT = 0.3048
  val metersPerUnit = METERS_PER_FOOT * feetPerUnit
  val unitsPerMeter = 1.0/metersPerUnit

  private def round(x:Number):Number = {
    val MAX_SCALE = 4
    Number(x.value.setScale(MAX_SCALE,BigDecimal.RoundingMode.UP))
  }

  def radMinAbs:EnvScalar = { round(rMinAbs) }
  def radMaxAbs:EnvScalar = { round(rMaxAbs) }
  def radMin:EnvScalar = { round(rMin) }
  def radMax:EnvScalar = { round(rMax) }
  def tanMin:EnvScalar = { round(tMin) }
  def tanMax:EnvScalar = { round(tMax) }
  def velMin:EnvScalar = { round(vMin) }
  def velMax:EnvScalar = { round(vMax) }

  // Ratio of model units to meters
  val g = 9.80665
  val sqrtG = 3.13155712067
  // @TODO: Probably wrong
  private def scaleAccel(t:EnvScalar):EnvScalar = {
    Number(t.value/(metersPerUnit*metersPerUnit*g))
  }
  def printLoudly():Unit = {
    println("*************************************************************")
    println("*    ACCELERATION+VELOCITY ENVELOPE                         *")
    println("*************************************************************")
    println("MINIMUM RADIAL: " + radMin.value)
    println("MAXIMUM RADIAL: " + radMax.value)
    println("MINIMUM TANGENTIAL: " + tanMin.value)
    println("MAXIMUM TANGENTIAL: " + tanMax.value)
    //velocity in m/s = sqrt(2*deltaH*unitsPerMeter*gravity)/unitsPerMeter39.3701
    println("MINIMUM VELOCITY:" + round(Number(Math.sqrt(velMin.value.toDouble*metersPerUnit*g))))
    println("MAXIMUM VELOCITY:" + round(Number(Math.sqrt(velMax.value.toDouble*metersPerUnit*g))))
  }

  def extendR(r:EnvScalar, isCw:Boolean, debugInfo:Option[(Int,TPoint)]):AccelEnvelope = {
    val signed = if (isCw) r else {Number(-r.value)}
    val env = AccelEnvelope(scalarMin(rMin,signed), scalarMin(rMinAbs,r), scalarMax(rMax,signed), scalarMax(rMaxAbs,r), tMin, tMax, vMin, vMax,feetPerUnit)
    val map =
    debugInfo match {
      case None => centrips
      case Some(info) => centrips.+((info, r))
    }
    centrips = map
    env.centrips = map
    env
  }

  def extendT(t:EnvScalar):AccelEnvelope = {
    val env = AccelEnvelope(rMin,rMinAbs,rMax,rMaxAbs,scalarMin(t,tMin),scalarMax(t,tMax), vMin, vMax,feetPerUnit)
    env.centrips = centrips
    env
  }

  def extendV(v:EnvScalar):AccelEnvelope = {
    val env = AccelEnvelope(rMin,rMinAbs,rMax,rMaxAbs,tMin,tMax,scalarMin(v,vMin),scalarMax(v,vMax),feetPerUnit)
    env.centrips = centrips
    env
  }

  // Not intended for soundness criticality, but as a check during spec generation to ensure there's some chance of the
  // spec being useful
  def isSafe:Boolean = {
    scalarLeq(AccelEnvelope.MIN_TAN,tMin) && scalarLeq(tMax,AccelEnvelope.MAX_TAN) && scalarLeq(AccelEnvelope.MIN_RAD,rMin) && scalarLeq(rMax, AccelEnvelope.MAX_RAD)
  }

  val DEFAULT_TOLERANCE = Number(0.001)

  def relaxBy(tolerance:EnvScalar=DEFAULT_TOLERANCE):AccelEnvelope = {
    AccelEnvelope(Number(rMin.value-tolerance.value), Number(rMinAbs.value-tolerance.value),
      Number(rMax.value+tolerance.value), Number(rMaxAbs.value+tolerance.value),
      Number(tMin.value-tolerance.value),Number(tMax.value+tolerance.value),
      Number(vMin.value-tolerance.value), Number(vMax.value+tolerance.value),feetPerUnit)
  }

  private def tanSpec(dy:Term):Formula = {
    s"($tanMin)*g() <= -($dy)*g() & -($dy)*g() <= ($tanMax)*g()".asFormula
  }

  private def velSpec:Formula = {
    //s"v^2 <= v^2 & v^2 <= v^2".asFormula
    s"($velMin)*g() <= v^2 & v^2 <= ($velMax)*g()".asFormula
  }

  def lineSpec(dy:Term):Formula = And(velSpec,tanSpec(dy))

  def radSpec(r:Term, isCw:Boolean):Formula = {
    val a = s"v^2/($r)".asTerm //if(isCw) s"v^2/($r)".asTerm else s"-v^2/($r)".asTerm
    s"($radMinAbs)*g()<=($a)&($a)<=($radMaxAbs)*g()".asFormula
  }

  def arcSpec(dy:Term, r:Term, isCw:Boolean):Formula = {
    And(velSpec,And(radSpec(r, isCw), tanSpec(dy)))
  }
}

/* Generate dL specification for safety of CoasterX models from a file
* */
object CoasterXSpec {
  type TPoint = (Term, Term)
  type Context = Map[BaseVariable, Double]
}
class CoasterXSpec(feetPerUnit:Double) {

  var ctx:Context = Map.empty

  /* Approximate term evaluator, with limited range especially for square roots.
   * Thus it's not suitable for rigorous proof purposes, but can be used both (a) for guiding spec+proof strategy when we need to compare irrational terms to
   * make a decision and (b) for general debugging purposes when we want a quantitative view on complicated terms */
  def evalTerm(t:Term):Number = Number(evalTermFast(t))
  def evalTermFast(t:Term):Double = {
    t match {
      case x:BaseVariable => ctx(x)
      case n:Number => n.value.toDouble
      case Neg(x) => (-evalTermFast(x))
      case Plus(x,y) => (evalTermFast(x) + evalTermFast(y))
      case Minus(x,y) => (evalTermFast(x) - evalTermFast(y))
      case Times(x,y) => (evalTermFast(x) * evalTermFast(y))
      case Divide(x,y) => (evalTermFast(x) / evalTermFast(y))
      case Power(x,y:Number) if y == 0 => (1)
      case Power(x,y:Number) if y.value.isValidInt && y.value > 0 => (evalTermFast(x)*evalTermFast(Power(x,Number(y.value-1))))
      case Power(x,y) => (Math.pow(evalTermFast(x).toDouble, evalTermFast(y).toDouble))
    }
  }

  /* Approximate formula evaluator, useful for similar purposes as above, e.g. to debug whether coasters are reasonable before formal proof */
  def evalFml(f:Formula):Boolean = {
    val cmpDelta = 1.0E-10
    f match {
      case Equal(t1,t2) => Math.abs(evalTerm(t1).value.toDouble - evalTerm(t2).value.toDouble) < cmpDelta
      case NotEqual(t1,t2) => Math.abs(evalTerm(t1).value.toDouble - evalTerm(t2).value.toDouble) >= cmpDelta
      case LessEqual(t1, t2) => evalTerm(t1).value < evalTerm(t2).value + cmpDelta
      case Less(t1,t2) => evalTerm(t1).value < evalTerm(t2).value
      case GreaterEqual(t1, t2) => evalTerm(t1).value > evalTerm(t2).value - cmpDelta
      case Greater(t1,t2) => evalTerm(t1).value > evalTerm(t2).value
      case And(p,q)  => evalFml(p) && evalFml(q)
      case Or(p,q)  => evalFml(p) || evalFml(q)
      case Imply(p,q)  => !evalFml(p) || evalFml(q)
      case Equiv(p,q) => evalFml(p) == evalFml(q)
      case Not(p) => !evalFml(p)
    }
  }

/* START CONSTANT-FOLDING IMPLEMENTATION
 * This is used to help produce smaller specifications.
 * In the best of conditions our specifications are already quite large and stress the parser, UI, etc.
 * So it helps to eliminate the many silly operations and constants that arise */
  def foldMinus(t1:Term, t2:Term):Term = {
    val candidate =
    (t1,t2) match {
      case (n1:Number,n2:Number) => Number(n1.value - n2.value)
      case (n1:Number, _) if n1 == Number(0) => foldNeg(t2)
      case (_, n2:Number) if n2 == Number(0) => t1
      case _ => Minus(t1,t2)
    }
    candidate match {
      case (Minus(n1:Number, Minus(n2:Number, t3:Term))) if n1 == n2 => t3
      case x => x
    }
  }

  def foldPlus(t1:Term, t2:Term):Term = {
    val candidate =
      (t1,t2) match {
        case (n1:Number,n2:Number) => Number(n1.value + n2.value)
        case (n1:Number, _) if n1 == Number(0) => t2
        case (_, n2:Number) if n2 == Number(0) => t1
        case _ => Plus(t1,t2)
      }
    candidate match {
      case (Plus(x,Neg(y))) => foldMinus(x,y)
      case _ => candidate
    }
  }

  def foldTimes(t1:Term, t2:Term):Term = {
    (t1,t2) match {
      case (n1:Number,n2:Number) => Number(n1.value * n2.value)
      case (n1:Number, _) if n1 == Number(1) => t2
      case (_, n2:Number) if n2 == Number(1) => t1
      case (n1:Number, _) if n1 == Number(-1) => foldNeg(t2)
      case (_, n2:Number) if n2 == Number(-1) => foldNeg(t1)
      case (n1:Number, _) if n1 == Number(0) => Number(0)
      case (_, n2:Number) if n2 == Number(0) => Number(0)

      case _ => Times(t1,t2)
    }
  }

  def foldDivide(t1:Term, t2:Term):Term = {
    val candidate =
      (t1,t2) match {
      case (n1:Number,n2:Number) if n2.value != BigDecimal(0) && n1.value.remainder(n2.value) == BigDecimal(0) =>
        Number(n1.value / n2.value)
      case _ => Divide(t1,t2)
    }
    candidate match {
      case (Divide(Number(n), denom)) if n == BigDecimal(0) => Number(0)
      case (Divide(numer, Number(m))) if m == BigDecimal(1) => numer
      // Could generalize this to anything that we know is exactly representable
      case (Divide(numer:Number, Number(m))) if m == BigDecimal(2) => Number(numer.value / 2)
      case _ => candidate
    }
  }

  def foldPower(t1:Term, t2:Term):Term = {
    def doRoot() = {
      try {
        val (n1:Number) = t1.asInstanceOf[Number]
        val i = n1.value.toIntExact
        val root:Int = Math.sqrt(i).toInt
        val j = root*root
        if (i == j) {
          Number(root)
        } else {
          Power(t1,t2)
        }
      } catch {
        case _:java.lang.ArithmeticException => Power(t1,t2)
      }
    }
    val candidate =
    (t1,t2) match {
      case (n1:Number,n2:Number) if n2.value == BigDecimal(0)  => Number(1)
      case (n1:Number,n2:Number) if n2.value.isValidInt && n2.value > 0  =>
        val tail:Number = foldPower(n1,Number(n2.value-1)).asInstanceOf[Number]
        Number(tail.value*n1.value)
      // Compute roots when perfect square
      case (n1:Number, Divide(n2:Number,n3:Number)) if n2.value == 1 && n3.value == 2 => {
        doRoot()
      }
      case (n1:Number, n2:Number) if n2.value == 0.5 => {
        doRoot()
      }
      case (n1:Number, pow) if n1 == Number(1) && pow != Number(0) => n1
      case (n1:Number, pow) if n1 == Number(0) && pow != Number(0) => n1
      case _ => Power(t1,t2)
    }
    // silly optimization because it happens in our models
    candidate match {
      case Power(Divide(Power(t1,Number(pow1)),t2),Number(pow2)) if pow1 * pow2 == 1 =>
        val a = Divide(t1,Power(t2,Number(pow2)))
        val b = Divide(t1,foldPower(t2,Number(pow2)))
        if (a != b) {}
        a
      case x => x
    }
  }

  def foldNeg(t1:Term):Term = {
    t1 match {
      case n:Number => Number(-n.value)
      case _ => Neg(t1)
    }
  }

  // Arbitrary term constant folding.
  // Use sparingly because it's much slower than just using an individual folding operation.
  def compact(t:Term):Term = {
    t match {
      case Plus(t1,t2) => foldPlus(compact(t1),compact(t2))
      case Times(t1,t2) => foldTimes(compact(t1),compact(t2))
      case Divide(t1,t2) =>
        val div = foldDivide(compact(t1),compact(t2))
        div match {
          case Divide(Plus(Minus(x1:Variable,y1:Variable),Plus(x2:Variable,y2:Variable)),Number(n)) if x1 == x2 && y1 == y2 && n == 2 =>
            x1
          case x => x
        }
      case Minus(t1,t2) =>
        val minus = foldMinus(compact(t1),compact(t2))
        val minus2 = minus match {
          case (Minus(x1:Variable, Plus(x2:Variable, t:Term))) if x1 == x2 => Neg(t)
          case (Minus(x1:Variable, Minus(x2:Variable, t:Term))) if x1 == x2 => t
          case x => x
        }
        minus2 match {
          case Minus(x1:Variable,x2:Variable) if x1 == x2 => Number(0)
          case x => x
        }
      case Neg(t) =>
        val neg = foldNeg(compact(t))
        neg match {
          case Neg(Neg(t)) => t
          case x => x
        }
      case Power(t1,t2) => foldPower(compact(t1),compact(t2))
      case Differential(t) => Differential(compact(t))
      case Pair(t1,t2) => Pair(compact(t1),compact(t2))
      case t => t
    }
  }

// BEGIN GEOMETRIC HELPERS
  def vecScale(xy:(Term,Term), scale:Term):(Term,Term) = {
    (foldTimes(xy._1,scale), foldTimes(xy._2,scale))
  }

  def vecPlus(xy1:(Term,Term), xy2:(Term,Term)):(Term,Term) = {
    (foldPlus(xy1._1,xy2._1),foldPlus(xy1._2, xy2._2))
  }

  def arcCenter(xy1:TPoint, xy2:TPoint):(Term, Term) = {
    (foldDivide(foldPlus(xy1._1,xy2._1),Number(2)), foldDivide(foldPlus(xy1._2,xy2._2),Number(2)))
  }

  def lineDir(xy1:TPoint, xy2:TPoint):(Term,Term) = {
    val mag:Term = foldPower(foldPlus(foldPower(foldMinus(xy2._1,xy1._1),Number(2)),foldPower(foldMinus(xy2._2,xy1._2),Number(2))),foldDivide(Number(1),Number(2)))
    (foldDivide(foldMinus(xy2._1,xy1._1),mag), foldDivide(foldMinus(xy2._2,xy1._2),mag))
  }

  /* Nasty math provided by Mathematica: Compute center of circle using two points on circle and tangent vector:
* Given two points (x1,y1) and (x2,y2) find the passing through them tangent
* to the line ax + by = c at (x1, y1)

* Eq (1)  b x - a y = b x1 - a y1
* Eq (2)  (x1-x2)x + (y1-y2)y = (1/2)(x1^2 - x2^2 + y1^2 - y2^2)

* Note that we have (x1,y1), (dx,dy) representation, from which we can derived a,b,c representation:
* a = (-dy)
* b = (dx)
* c = (dx y1 - x1 dy)
======================================== Final solution for x ======================================
(2 dx x1 (-y1 + y2) +
dy (x1^2 + x2^2 - y1^2 + 2 y1 y2 + y2^2))/(2 (dy (x1 - x2) +
 dx (-y1 + Example)))
====================================================================================================
====================================== Final solution for y =======================================
((x1 + x2) (2 dy (x1 - x2) y1 +
 dx (x1^2 - 2 x1 x2 - x2^2 - y1^2 - y2^2)))/(2 (x1 -
 x2) (dy (x1 + x2) + dx (y1 - y2)))
===================================================================================================
@TODO: Use the constant-folding versions of arithmetic operate

*/
  def centerFromStartSlope (x1:Term, y1:Term, x2:Term, y2:Term, dxy:TPoint):TPoint = {
    val (a,b) = (foldNeg(dxy._2), dxy._1)
    val cx = s"(($a)*(($x1)^2 - ($x2)^2 - (($y1) - ($y2))^2) + 2*($b)*($x1)*(($y1) - ($y2)))/(2*(($a)*(($x1) - ($x2)) + ($b)*(($y1) - ($y2))))".asTerm
    val cy = s"(2*($a)*(($x1) - ($x2))*($y1) - ($b)*((($x1) - ($x2))^2 - ($y1)^2 + ($y2)^2))/(2*(($a)*(($x1) - ($x2)) + ($b)*(($y1) - ($y2))))".asTerm
    (compact(cx),compact(cy))
  }
  // Compute direction-to-center vector using tangent vector and wiseness
  def centerFromTangent(dir:TPoint, angles:(Number,Number), delta:Number):(Term,Term) = {
    val isCw = delta.value < 0
    if (isCw) {
      (dir._2, foldNeg(dir._1))
    } else {
      (foldNeg(dir._2), dir._1)
    }
  }

  def tangentFromCenter(dir:TPoint, angles:(Number,Number), delta:Number):(Term,Term) =
    centerFromTangent(dir, angles.swap, foldNeg(delta).asInstanceOf[Number])

  def sqDist (p1:TPoint, p2:TPoint):Term = {
    foldPlus(foldPower(foldMinus(p1._1,p2._1), Number(2)), foldPower(foldMinus(p1._2,p2._2),Number(2)))
  }

  def dist (p1:TPoint, p2:TPoint):Term = {
    foldPower(sqDist(p1,p2),foldDivide(Number(1),Number(2)))
  }

  def magnitude(xy:TPoint):Term = {
    val (x,y) = xy
    foldPower(foldPlus(foldPower(x,Number(2)), foldPower(y,Number(2))),Divide(Number(1),Number(2)))
  }

  def normalizeVector(xy:TPoint):TPoint = {
    val (x,y) = xy
    (foldDivide(x,magnitude(xy)), foldDivide(y,magnitude(xy)))
  }

  def slope(xy1:TPoint, xy2:TPoint):Term = {
    foldDivide(foldMinus(xy1._2, xy2._2),foldMinus(xy1._1, xy2._1))
  }

  /* y-intercept of segment */
  def yOffset(xy1:TPoint, xy2:TPoint):Term = {
    foldMinus(xy1._2,foldTimes(slope(xy1,xy2), xy1._1))
  }

  // BEGIN SPEC GENERATION PROPER
  def segmentOde(segBounds:((Section,(TPoint,TPoint),TPoint),Int)):Program = {
    val ((seg, (start,end), initD), iSection) = segBounds
    val x = Variable("x")
    val y = Variable("y")
    def evol(isUp:Boolean,movesLeft:Boolean) = {
      val ybound =
        if(isUp) {
          And(LessEqual(start._2, y), LessEqual(y, end._2))
        } else {
          And(LessEqual(end._2, y), LessEqual(y, start._2))
        }
      val xbound =
        if(movesLeft) {
          And(LessEqual(end._1, x), LessEqual(x, start._1))
        } else {
          And(LessEqual(start._1, x), LessEqual(x, end._1))
        }
      And(xbound, ybound)
    }
    val dx = Variable("dx")
    val dy = Variable("dy")
    val (dxi:Variable, dyi:Variable) = iDirection(iSection)
    seg match {
      case LineSection(Some(LineParam((x1,y1),(x2,y2))), Some(gradient), isUp) =>
        val v = Variable("v")
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        // Inlined version of ODE not used right now but still experimenting
        val xOdeInlined = AtomicODE(DifferentialSymbol(Variable("x")), foldTimes(v, dxval))
        val yOdeInlined = AtomicODE(DifferentialSymbol(Variable("y")), foldTimes(v, dyval))
        val vOdeInlined = s"v' = -($dyval)".asDifferentialProgram
        val sysInlined = DifferentialProduct(DifferentialProduct(xOdeInlined,yOdeInlined),vOdeInlined)
        val xOde = AtomicODE(DifferentialSymbol(Variable("x")), foldTimes(v,dx))
        val yOde = AtomicODE(DifferentialSymbol(Variable("y")), foldTimes(v,dy))
        val vOde = s"v' = -dy*g()".asDifferentialProgram
        val sys = DifferentialProduct(DifferentialProduct(xOde,yOde),vOde)
        //@TODO: Left-going straight lines too
        val ode = ODESystem(sys, evol(isUp, movesLeft = false))
        val (setx,sety) = (Assign(dx,dxi), Assign(dy,dyi))
        Compose(setx,Compose(sety, ode))
      case ArcSection(Some(ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
        val r = iRadius(iSection)  //CoasterXSpec.dist(start, (cx,cy))
        val sysBase = "x' = dx*v, y' = dy*v, v' = -dy*g()".asDifferentialProgram
        val isCw = deltaTheta.value < 0
        val (dxTerm, dyTerm) = if (isCw) {(foldDivide("dy*v".asTerm, r), foldDivide("-dx*v".asTerm, r))} else {(foldDivide("-dy*v".asTerm, r), foldDivide("dx*v".asTerm, r))}
        val sys = DifferentialProduct(sysBase,DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("dx")), dxTerm),
          AtomicODE(DifferentialSymbol(Variable("dy")), dyTerm)))
        val t1 = theta1.value
        val dt = deltaTheta.value
        val startsLeft = t1 < -90 || t1 > 90 || (t1 == -90 && dt < 0) || (t1 == 90 && dt > 0)
        val movesLeft = (t1 <= 0 && dt < 0) || (t1 >= 0 && dt > 0)
        val isUp = (startsLeft && isCw) || (!startsLeft && !isCw)
        val (cx,cy) = iCenter(iSection)
        val (setx,sety) =
          if (isCw) {(s"-(($cy)-y)/($r)".asTerm, s"(($cx)-x)/($r)".asTerm)}
          else {(s"(($cy)-y)/($r)".asTerm, s"-(($cx)-x)/($r)".asTerm)}
        val ode = ODESystem(sys, evol(isUp, movesLeft))
        Compose(Assign(dx,setx),Compose(Assign(dy,sety), ode))
      case _ => Test(True)
    }
  }

  val gconst = FuncOf(Function("g", None, Unit, Real), Nothing)
  val gpos = Greater(gconst, Number(0))

  def segmentPre(segBounds:(Section,(TPoint,TPoint),TPoint), v0:Term):Formula = {
    val (seg, (start,end), initD) = segBounds
    seg match {
      case LineSection(Some(LineParam((x1,y1),(x2,y2))), Some(gradient),isUp) =>
        /* TODO: Assert
        v0 > 0 &   /* non-negative velocity initially */
        dx > 0 &    /* travelling rightwards initially */
        l > 0 /* length of track is strictly positive */

        y*dx = x*dy + c*dx &    /* is on track initially */
        dx^2 + dy^2 = 1 &    /* unit vector */
        dx*(v0^2) > 2*dy*l &    /* coaster has enough initial kinetic energy to reach end of track */
        */
        val (dxval,dyval) = lineDir((x1,y1),(x2,y2))
        val dx = Variable("dx")
        val dy = Variable("dy")
        val x = Variable("x")
        val y = Variable("y")
        val v = Variable("v")
        val dxeq = Equal(dx,dxval)
        val dyeq = Equal(dy,dyval)
        val xeq = Equal(x,x1)
        val yeq = Equal(y,y1)
        val veq = Equal(v, v0)
        And(gpos,And(dxeq,And(dyeq,And(xeq,And(yeq,veq)))))
      case ArcSection(Some(param@ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
        // @TODO: Update radius computation
        /* TODO: Assert
        r > 0 &
        cy > y0 &
        cx >= xend &
        ((y-cy)/r)^2 + ((x-cx)/r)^2 = 1 &
        xend > x0 &
        y0 > yend &
        (cx - x0)^2   + (cy - y0)^2   = r^2 &
        (cx - xend)^2 + (cy - yend)^2 = r^2
        v0 > 0      /* positive velocity initially */
        */
        val ((x3,y3),(x4,y4)) = (start,end)
        val (cx, cy) = arcCenter((x1,y1),(x2,y2))

        val x = Variable("x")
        val y = Variable("y")
        val v = Variable("v")
        val r = foldDivide(foldMinus(x2,x1),Number(2))
        val dcxTerm = foldDivide(foldMinus(cx,x), r)
        val dcyTerm = foldDivide(foldMinus(cy,y),r)
        val (dtx,dty) = tangentFromCenter((dcxTerm,dcyTerm),(param.theta1, param.theta2), param.deltaTheta)
        val dx = Variable("dx")
        val dy = Variable("dy")
        val dxeq = Equal(dx, dtx)
        val dyeq = Equal(dy,dty)
        val xeq = Equal(x,x3)
        val yeq = Equal(y,y3)
        val veq = Equal(v, v0)
        And(gpos,And(dxeq,And(dyeq,And(xeq,And(yeq,veq)))))
      case _ => True
    }
  }

  def segmentPost(env:AccelEnvelope)(segBounds:((Section,(TPoint,TPoint), TPoint), Int)):Formula = {
    val ((seg, (start, end), initD), i) = segBounds
    val x = Variable("x")
    val y = Variable("y")
    val (dxval:Term, dyval:Term) = iDirection(i)
    seg match {
      case LineSection(Some(LineParam((x1, y1), (x2, y2))), Some(gradient), isUp) =>
        val inRange = And(LessEqual(x1, x), LessEqual(x, x2))
        val dxInv = s"dx=($dxval)".asFormula
        val dyInv = s"dy=($dyval)".asFormula
        //val dInv = And(dxInv, dyInv)
        val onTrack = Equal(foldTimes(dxval, y), foldPlus(foldTimes(dyval, x), foldTimes(dxval,yOffset((x1, y1), (x2, y2)))))
        Imply(inRange, And(env.lineSpec(dyval),onTrack))
      case ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)) =>
        val ((x3:Term, y3:Term), (x4:Term, y4:Term)) = (start,end)
        val t1 = theta1.value
        val dt = deltaTheta.value
        val startsLeft = t1 < -90 || t1 > 90 || (t1 == -90 && dt < 0) || (t1 == 90 && dt > 0)
        val startsTop = (t1 == 180 && dt < 0) || (t1 < 180 && t1 > 0) || (t1 == 0 && dt > 0)
        val movesLeft = (t1 <= 0 && dt < 0) || (t1 >= 0 && dt > 0)
        val isCw = param.deltaTheta.value < 0
        val isUp = (startsLeft && isCw) || (!startsLeft && !isCw)
        val xRange =
          if (movesLeft) {
            And(LessEqual(x4, x), LessEqual(x, x3))
          } else {
            And(LessEqual(x3, x), LessEqual(x, x4))
          }
        val yRange =
          if (isUp) {
            And(LessEqual(y3, y), LessEqual(y,y4))
          } else {
            And(LessEqual(y4, y), LessEqual(y,y3))
          }
        val inRange = And(xRange,yRange)
        val (cx:Term, cy:Term) = iCenter(i)
        val r = iRadius(i)
        val centered = Equal(sqDist((x,y), (cx,cy)), foldPower(r,Number(2)))
        val outY = if(startsTop) LessEqual(cy,y) else LessEqual(y,cy)
        val outX = if(startsLeft) LessEqual(x, cx) else LessEqual(cx, x)
        val outRange = And(outX, outY)
        val (dxInv, dyInv) =
          if (isCw) {
            (s"dx=-(($cy)-y)/($r)".asFormula, s"dy=(($cx)-x)/($r)".asFormula)
          } else {
            (s"dx=-(y-($cy))/($r)".asFormula, s"dy=(x-($cx))/($r)".asFormula)
          }
        //val dInv = And(dxInv, dyInv)
        Imply(inRange, And(centered, And(outRange,env.arcSpec(dyval,r,isCw))))
      case _ => True
    }
  }

  def segmentEmpty(seg:Section):Boolean = {
    seg match {
      case LineSection(Some(_),Some(_), _) => false
      case LineSection(_, _, _) => true
      case ArcSection(Some(_), Some(_)) => false
      case ArcSection(_, _) => true
    }
  }

  // assumes ys.length = xs.length + 1
  def zipConsecutive[A,B,C](xs:List[A],ys:List[B],zs:List[C]):List[(A,(B,B),C)] = {
    (xs, ys, zs) match {
      case (x1::xss, y1::y2::yss, z::zss) =>  (x1,(y1,y2),z) :: zipConsecutive(xss, y2::yss, zss)
      case (Nil, _::Nil, Nil) => Nil
      case _ => ???
    }
  }

  def zipConsecutive2[A,B](xs:List[A],ys:List[B]):List[(A,(B,B))] = {
    (xs, ys) match {
      case (x1::xss, y1::y2::yss) =>  (x1,(y1,y2)) :: zipConsecutive2(xss, y2::yss)
      case (Nil, _::Nil) => Nil
      case _ =>
        val 2 = 1 + 1
        ???
    }
  }

  def countSections(in:AFile):Int = {
    val (_,secs,_,_,_)= in
    secs.length
  }

  def prepareFile(file:CoasterXParser.File):(AFile,Formula) = {
    val ROUND_SCALE = 0
    val fileRounded = roundFile (ROUND_SCALE)(file)
    alignFile(fileRounded)
  }

  def iCenter(i:Int):TPoint = { (Variable("cx", Some(i)), Variable("cy",Some(i))) }
  def iDirection(i:Int):TPoint = { (Variable("dx", Some(i)), Variable("dy",Some(i))) }
  def iRadius(i:Int):Term = { Variable("r", Some(i))}

  def fromAligned(align:(AFile,Formula),env:AccelEnvelope):Formula = {
    val (aligned@(points, segments, v0pre, _, dirs), segmentDefs) = align
    val v0 = s"($v0pre)*(g()^(1/2))".asTerm
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive(nonemptySegs,points,dirs)
    val pre = segmentPre(withBounds.head,v0)
    val ode = withBounds.zipWithIndex.map(segmentOde).reduceRight[Program]({case(x,y) => Choice(x,y)})
    val y0 = points.head._2
    val energyConserved = s"v^2 + 2*y*g() = ($v0)^2 + 2*($y0)*g()".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    val post = And(globalPost, withBounds.zipWithIndex.map(segmentPost(env)).reduceRight[Formula]{case (x,y) => And(x,y)})
    Imply(And(segmentDefs,pre),Box(Loop(ode), post))
  }

  def apply(file:CoasterXParser.File):Formula = {
    val (aligned, fml)= prepareFile(file)
    val env = envelope(aligned)
    env.printLoudly()
    fromAligned((aligned,fml), env)
  }

// BEGIN ROUNDING OF FLOATY MODELS TO INTEGER PRECISION
  def roundNumber(scale:Int)(n:Number):Number = {
    Number(new BigDecimal(n.value.bigDecimal).setScale(scale, BigDecimal.RoundingMode.DOWN))
  }

  def roundTerm(scale:Int)(n:Term):Term = {
    n match {
      case n:Number => roundNumber(scale)(n)
      case _ => n
    }
  }

  def roundPoint(scale:Int)(xy:TPoint):TPoint = {
    (roundTerm(scale)(xy._1), roundTerm(scale)(xy._2))
  }

  def roundArcParam(scale:Int)(seg:ArcParam):ArcParam = {
    ArcParam(roundPoint(scale)(seg.bl), roundPoint(scale)(seg.tr), roundNumber(scale)(seg.theta1), roundNumber(scale)(seg.deltaTheta))
  }

  def roundLineParam(scale:Int)(seg:LineParam):LineParam = {
    LineParam(roundPoint(scale)(seg.bl), roundPoint(scale)(seg.tr))
  }

  def roundParam(scale:Int)(seg:SectionParam):SectionParam = {
    seg match {
      case s:LineParam => roundLineParam(scale)(s)
      case s:ArcParam => roundArcParam(scale)(s)
    }
  }

  def roundSegment(scale:Int)(seg:Section):Section = {
    seg match {
      case ArcSection(param, grad) => ArcSection(param.map(roundArcParam(scale)), grad.map(roundTerm(scale)))
      case LineSection(param, grad, isUp) => LineSection(param.map(roundLineParam(scale)), grad.map(roundTerm(scale)), isUp)
    }
  }

  /* Mostly to produce readable models, also avoids making QE deal with obnoxiously large literals - though not clear whether the latter is a practical concern */
  def roundFile (scale:Int)(file:File):File = {
    val (points, segments, v0, tent) = file
    (points.map(roundPoint(scale)), segments.map(roundSegment(scale)), roundNumber(scale)(v0), roundParam(scale)(tent))
  }


  def setStartY(sections:List[(Section,(TPoint,TPoint))], y:Term) = {
    sections match {
      case (LineSection(Some(LineParam((x1,y1),(x2,y2))),Some(grad), isUp), ((xx1, yy1), (xx2, yy2))) :: rest =>
        (LineSection(Some(LineParam((x1,y),(x2,y2))),Some(grad), isUp), ((xx1, y), (xx2, yy2))) :: rest
      case (ArcSection(Some(ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)), ((xx1, yy1), (xx2, yy2))) :: rest =>
        (ArcSection(Some(ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)), ((xx1, y), (xx2, yy2))) :: rest
      case _ => sections

    }
  }


// BEGIN ALIGNMENT OF ROUNDED MODELS

  def unsplitZipped(sections: List[(Section, (TPoint, TPoint))]):List[(Section, (TPoint, TPoint))] = {
    sections match {
      case Nil => Nil
      case (ArcSection(Some(ArcParam((x1,y1),(x2,y2), theta1, deltaTheta1)), slope1), ((xx1,yy1),(xx2,yy2))) ::
        (ArcSection(Some(ArcParam((x3,y3),(x4,y4), theta2, deltaTheta2)), _slope2), ((xx3,yy3),(xx4,yy4))) ::
            tail
      if x1 == x3 && x2 == x4 && y1 == y3 && y2 == y4 =>
        val combinedSec = ArcSection(Some(ArcParam((x1,y1),(x2,y2), theta1, Number(deltaTheta1.value+deltaTheta2.value))),slope1)
        val combined = (combinedSec, ((xx1,yy1),(xx4,yy4)))
        // In typical use case combined will not need to get unsplit again, but might as well since this is already well-founded
        unsplitZipped(combined::tail)
      case sec1 :: tail => sec1 :: unsplitZipped(tail)
    }
  }

  /*
  * Solve these equations:
  * (cx-x1)^2 + (cy-y1)^2 = (cx-x2)^2 + (cy-y2)^2
  * (dx^2 + dy^2)*((cx-x1)^2 + (cy-y1)^2) = (dy*x -dx*y + c)^2
  * dx*y >= dy*x+c
  * */
  def alignArcFromDirection(secs: List[(Section, (TPoint, TPoint))], index: Int, dx: Term, dy: Term):List[(Section,(TPoint,TPoint), Formula, TPoint)] = {
    val (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1:Term, yy1:Term), (xx2:Term, yy2:Term))) :: rest = secs
    val (cxe:Term, cye:Term) = centerFromStartSlope(xx1,yy1,xx2,yy2,(dx,dy))
    val cxapprox = evalTerm(cxe).value
    val cyapprox = evalTerm(cye).value

    def q1approx(x: BigDecimal, y: BigDecimal): Boolean = {
      x >= cxapprox && y >= cyapprox
    }

    def q2approx(x: BigDecimal, y: BigDecimal): Boolean = {
      x <= cxapprox && y >= cyapprox
    }

    def q3approx(x: BigDecimal, y: BigDecimal): Boolean = {
      x <= cxapprox && y <= cyapprox
    }

    def q4approx(x: BigDecimal, y: BigDecimal): Boolean = {
      x >= cxapprox && y <= cyapprox
    }

    def q1approxccw(x: BigDecimal, y: BigDecimal): Boolean = {
      q1approx(x, y) && !q2approx(x, y)
    }

    def q2approxccw(x: BigDecimal, y: BigDecimal): Boolean = {
      q2approx(x, y) && !q3approx(x, y)
    }

    def q3approxccw(x: BigDecimal, y: BigDecimal): Boolean = {
      q3approx(x, y) && !q4approx(x, y)
    }

    def q4approxccw(x: BigDecimal, y: BigDecimal): Boolean = {
      q4approx(x, y) && !q1approx(x, y)
    }

    def splitArcRecursively(secs: List[(Section, (TPoint, TPoint))], index: Int, dx: Term, dy: Term):List[(Section,(TPoint,TPoint), Formula, TPoint)] = {
      secs match {
        case (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1:Term, yy1:Term), (xx2:Term, yy2:Term))) :: rest
          =>
      val (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1:Term, yy1:Term), (xx2:Term, yy2:Term))) :: rest = secs
      val xx1approx = evalTerm(xx1).value
      val xx2approx = evalTerm(xx2).value
      val yy1approx = evalTerm(yy1).value
      val yy2approx = evalTerm(yy2).value
      val endDX = Variable("dx", Some(index))
      val endDY = Variable("dy", Some(index))
      val cx = Variable("cx", Some(index))
      val cy = Variable("cy", Some(index))
      val r = Variable("r", Some(index))
      val re = dist((cx, cy), (xx1, yy1))
      val yendSign = if (param.theta2.value > 0) {
        Number(1)
      } else Number(-1)
      val xend = xx2
      val (dcxe, dcye) = (foldMinus(cx, xend), foldMinus(cy, yy2))
      val (dtxe: Term, dtye: Term) = normalizeVector(tangentFromCenter((dcxe, dcye), (param.theta1, param.theta2), param.deltaTheta))
      val cxDef: Formula = Equal(cx, cxe)
      val cyDef: Formula = Equal(cy, cye)
      val endDXDef: Formula = Equal(endDX, dtxe)
      val endDYDef: Formula = Equal(endDY, dtye)
      val rDef = Equal(r, re)
      val allDefs = And(rDef, And(And(cxDef, cyDef), And(endDXDef, endDYDef)))
      ctx = ctx.+(cx -> evalTermFast(cxe), cy -> evalTermFast(cye))
      ctx = ctx.+(r -> evalTermFast(re))
      ctx = ctx.+(endDX -> evalTermFast(dtxe), endDY -> evalTermFast(dtye))
      // If we accidentally made this into a two-quadrant arc, then adjust again.
      // Yes, this is super nasty and could use some work
      val dT = deltaTheta.value
      val isCw = (dT < 0)
      val (t1, t2) = (theta1.value, normalizeAngle(theta1.value + deltaTheta.value))
      val q1 = (t1 == 0 && dT > 0) || (t1 > 0 && t1 < 90) || (t1 == 90 && dT < 0) //&& t2 <= 90
      val q2 = (t1 == 90 && dT > 0) || (t1 > 90 && t1 < 180) || (t1 == 180 && dT < 0) //!(q1 || q3 || q4)
      val q3 = ((t1 == 180 || t1 == -180) && dT > 0) || (t1 > -180 && t1 < -90) || (t1 == -90 && dT < 0) //&& t2 <= -90
      val q4 = (t1 == -90 && dT > 0) || (t1 > -90 && t1 < 0) || (t1 == 0 && dT < 0) //&& t2 <= 0

      val endDX2 = Variable("dx", Some(index + 1))
      val endDY2 = Variable("dy", Some(index + 1))
      val cx2 = Variable("cx", Some(index + 1))
      val cy2 = Variable("cy", Some(index + 1))
      val r2 = Variable("r", Some(index + 1))
      val cxDef2: Formula = Equal(cx2, cxe)
      val cyDef2: Formula = Equal(cy2, cye)
      val endDXDef2: Formula = Equal(endDX2, dtxe)
      val endDYDef2: Formula = Equal(endDY2, dtye)
      val rDef2 = Equal(r2, re)
      val allDefs2 = And(rDef2, And(And(cxDef2, cyDef2), And(endDXDef2, endDYDef2)))
      ctx = ctx.+(r2 -> evalTermFast(re), cx2 -> evalTermFast(cxe), cy2 -> evalTermFast(cye), endDX2 -> evalTermFast(dtxe), endDY2 -> evalTermFast(dtye))
      if (cxapprox > xx1approx && q4 && !isCw) {
        println("PRE-SPLITTING Q4CCW -> (Q3,Q4)CCW")
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), Number(-91), Number(1))), Some(oldSlope)),
          ((xx1, yy1), (cx, foldMinus(cy, r))),
          allDefs,
          (endDX, endDY))
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(-90), Number((param.theta2.value - (-90)).max(1)))), Some(oldSlope)),
          ((cx, foldMinus(cy, r)), (xx2, yy2)),
          allDefs2,
          (endDX, endDY))
        sec1 :: sec2 :: splitArcRecursively(rest,index+2,dx,dy)
      }
      else if (q2approxccw(xx1approx, yy1approx) && !q2approx(xx2approx, yy2approx) && !isCw) {
        println("SPLITTING Q2CCW -> (Q2,Q3)CCW")
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(BigDecimal(90).max(t1)), Number(BigDecimal(1).max(180 - t1).min(90)))), Some(oldSlope)),
          ((xx1, yy1), (foldMinus(cx, r), cy)),
          allDefs,
          (endDX, endDY))
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          // Intentially avoid normalizing, e.g. 270 degrees -> -90 Degrees when adding t1 + dT in order to support inversions
          Number(180), Number(((theta1.value + deltaTheta.value) - 180).max(1)))), Some(oldSlope)),
          ((foldMinus(cx, r), cy), (xx2, yy2))
        )
        // @TODO: Figure out what to do with formulas generated by recursive call
        sec1 :: splitArcRecursively(sec2:: rest,index+1,endDX,endDY)
      } else if (q1approxccw(xx1approx, yy1approx) && !q1approx(xx2approx, yy2approx) && !isCw) {
        println("SPLITTING Q1CCW -> (Q1,Q2)CCW")
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(BigDecimal(0).max(t1)), Number(BigDecimal(1).max(90 - t1).min(90)))), Some(oldSlope)),
          ((xx1, yy1), (cx, foldPlus(cy, r))),
          allDefs,
          (endDX, endDY))
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          // Intentially avoid normalizing, e.g. 270 degrees -> -90 Degrees when adding t1 + dT in order to support inversions
          Number(90), Number(((theta1.value + deltaTheta.value) - 90).max(1)))), Some(oldSlope)),
          ((cx, foldPlus(cy, r)), (xx2, yy2))
        )
        // @TODO: Figure out what to do with formulas generated by recursive call
        sec1 :: alignZipped(sec2 :: rest, Some((endDX, endDY)), index + 1)
      } else if (q4approxccw(xx1approx, yy1approx) && !q4approx(xx2approx, yy2approx) && !isCw) {
        println("SPLITTING Q4CCW -> (Q4,Q1) CCW")
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(BigDecimal(-1).min(t1)), Number(BigDecimal(1).max(0 - t1).min(90)))), Some(oldSlope)),
          ((xx1, yy1), (foldPlus(cx, r), cy)),
          allDefs,
          (endDX, endDY))
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          // Intentially avoid normalizing, e.g. 270 degrees -> -90 Degrees when adding t1 + dT in order to support inversions
          Number(0), Number(((theta1.value + deltaTheta.value) - 0).max(1)))), Some(oldSlope)),
          ((foldPlus(cx, r), cy), (xx2, yy2)))
        // @TODO: Figure out what to do with formulas generated by recursive call
        sec1 :: splitArcRecursively(sec2:: rest,index+1,endDX,endDY)
      } else if (cxapprox > xx2approx && q4 && isCw) {
        println("SPLITTING Q4CW -> (Q4,Q3)CW")
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(BigDecimal(-89).max(t1)), Number(BigDecimal(-1).min(-90 - t1)))), Some(oldSlope)),
          ((xx1, yy1), (cx, foldMinus(cy, r))),
          allDefs,
          (endDX, endDY))
        // TODO: Need to set dx and such intermediately for those components
        // TODO: Not an obvious value for the deltatheta dude
        // TODO: Need to figure out definition numbering and stuff
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(-90), Number((param.theta2.value - (-90)).min(-1)))), Some(oldSlope)),
          ((cx, foldMinus(cy, r)), (xx2, yy2)),
          allDefs2,
          (endDX, endDY))
        sec1 :: sec2 :: splitArcRecursively(rest,index+2,endDX,endDY)
      }
      // Insert a 3rdq arc because hmm whoops turns out we're not so q4 after all
      else if (cxapprox < xx2approx && q3) {
        println("SPLITTING Q3CCW -> (Q3,Q4)CCW")
        assert(theta1.value <= -90 && param.theta2.value >= -90)
        // @TODO: This assumes it's a Q3-Q4 arc, but gotta start somewhere
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), theta1, Number(-90 - theta1.value))), Some(oldSlope)),
          ((xx1, yy1), (cx, foldMinus(cy, re))),
          allDefs,
          (endDX, endDY))
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
          Number(-90), Number((param.theta2.value - (-90)).max(1)))), Some(oldSlope)),
          ((cxe, foldMinus(cy, r)), (xx2, yy2)),
          allDefs2,
          (endDX, endDY))
        sec1 :: sec2 :: splitArcRecursively(rest,index+2,endDX,endDY)
      } else if (cxapprox < xx2approx && q2) {
        println("SPLITTING Q2CCW -> (Q2,Q1)CCW")
        // @TODO: This assumes it's a Q2-Q1 arc, but gotta start somewhere
        //assert(param.theta1.value >= 90 && param.theta2.value <= 90)
        val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), theta1, Number(90 - param.theta1.value))),
          Some(oldSlope)),
          ((xx1, yy1), (cx, foldPlus(cy, r))),
          allDefs,
          (endDX, endDY))
        val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), Number(90), Number((param.theta2.value - 90).min(-1)))), Some(oldSlope)),
          ((cxe, foldPlus(cy, r)), (xx2, yy2)),
          allDefs2,
          (endDX, endDY))
        sec1 :: sec2 :: splitArcRecursively(rest,index+2,endDX,endDY)
      } else {
        val head = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), theta1, deltaTheta)), Some(oldSlope)),
          ((xx1, yy1), (xx2, yy2)),
          allDefs,
          (endDX, endDY))
        head :: splitArcRecursively(rest,index+1,endDX,endDY)
      }
        case _ => alignZipped(secs,Some(dx,dy),index)
      }
    }
    splitArcRecursively(secs, index, dx, dy)
  }

  def alignArcFromCenter(secs:List[(Section,(TPoint,TPoint))], index:Int):List[(Section,(TPoint,TPoint), Formula, TPoint)] = {
    val (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1, yy1), (xx2, yy2))) :: rest = secs
    // Approach: Take (x0, y0), (x1,y1), (dx0, dy0)  as given and compute (cx,cy).
    val (cxe,cye) = arcCenter((x1,y1),(x2,y2))
    val (dcxD, dcyD) = (foldMinus(cxe, xx1), foldMinus(cye, yy1))
    val directionD = normalizeVector(tangentFromCenter((dcxD,dcyD), (param.theta1, param.theta2), param.deltaTheta))
    alignArcFromDirection(secs, index, directionD._1, directionD._2)
  }

  /* @param zip is a list of sections annotated with their lower-left and upper-right boundaries
  *  @param dL term (e.g. a variable m_i) representing the slope of the previous line segment, or None if this is the first segment.
  *   (@TODO: Should basically-never truly need to introduce a new slope variable in the straight line segment case, but
  *    currently always introduces a variable in ordr to make it easier to keep track of the variables)
  *  @return List of rounded sections with their rounded bounding boxes, with a formula defining any new variables introduced
  *    to define the segment, e.g. x_i, y_i, m_i
  *    */
  def alignZipped(zip:List[(Section,(TPoint,TPoint))], _initD:Option[TPoint], index:Int):List[(Section,(TPoint,TPoint), Formula, TPoint)] = {
    println("DOING ALIGN-ZIP")
    zip match {
      case Nil => Nil
      case (LineSection(Some(LineParam((x1,y1),(x2,y2))),Some(_), isUp), ((xx1, yy1), (xx2, yy2))) :: rest =>
      //  val endY = Variable("y", Some(index))
        val endDX = Variable("dx", Some(index)) // Redundant but simplifies design
        val endDY = Variable("dy", Some(index)) // Redundant but simplifies design
        val defaultD = normalizeVector((foldMinus(xx2,xx1), foldMinus(yy2,yy1)))
        val endD:TPoint = defaultD //initD.getOrElse(defaultD)
        val endMTerm = foldDivide(foldMinus(yy2,yy1),foldMinus(xx2,xx1))
        val endYTerm = yy2
        //val endYDef:Formula = Equal(endY, endYTerm)
        val endDXDef = Equal(endDX, endD._1)
        val endDYDef = Equal(endDY, endD._2)
        val allDefs = And(endDXDef, endDYDef)
        ctx = ctx.+(endDX -> evalTermFast(endD._1), endDY -> evalTermFast(endD._2))
        val head = (LineSection(Some(LineParam((xx1,yy1),(xx2,yy2))), Some(endMTerm), isUp), ((xx1,yy1),(xx2,yy2)), allDefs, endD)
        head :: alignZipped(setStartY(rest,yy2), Some(endD), index+1)
      case (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1, yy1), (xx2, yy2))) :: rest =>
        //initD match {
          /*case None => */alignArcFromCenter(zip, index)
          /*case Some((dx,dy)) => alignArcFromDirection(zip, index, dx, dy)
        }*/
      case _ => ???
    }
  }

  def unzipConsecutive(tuples: List[(CoasterXParser.Section, ((Term, Term), (Term, Term)), Formula, TPoint)]):(List[TPoint], List[Section], Formula, List[TPoint]) = {
    tuples match {
      case Nil => (Nil, Nil, True, Nil)
      case (sec,(start,end), fml, x)::Nil =>
        (start :: end :: Nil, sec :: Nil, fml, x :: Nil)
      case (sec,(start,end),fml,x)::rest =>
        val (points, secs,fmls,xs) = unzipConsecutive(rest)
        (start :: points, sec :: secs, And(fml,fmls), x :: xs)
    }
  }




  def envelope(y0:Number, v0:Number, segs:List[(Section,(TPoint,TPoint))]):AccelEnvelope = {
    //val g = 9.80665
    def velSquaredAt(y:Number):Number = Number(v0.value*v0.value + (2*y0.value) - (2*y.value))
    val res =
    segs.zipWithIndex.foldRight(AccelEnvelope.empty){case(((sec,((x1:Term,y1:Term),(x2:Term,y2:Term))),iSection), env) =>
      sec match {
        case (LineSection(Some(LineParam(bl,tr)),Some(grad), isUp)) =>
          // Line sections - no centripetal acceleration
          val (dx,dy) = lineDir(bl,tr)
          env.extendT(Number(evalTerm(Neg(dy)).value))
            .extendV(velSquaredAt(evalTerm(y1))).extendV(velSquaredAt(evalTerm(y2)))
        case (ArcSection(Some(ArcParam(bl,tr,theta1,deltaTheta)), Some(grad))) =>
          val rad = (evalTerm(bl._1).value-evalTerm(tr._1).value).abs/2
          val cx = (evalTerm(bl._1).value + evalTerm(tr._1).value) /2
          val isCw = deltaTheta.value < 0
          /* Centripetal acceleration perpendicular to track */
          def radialAt(y:Number):Number = {
            val cent = velSquaredAt(y).value/rad
            Number(cent)
          }
          /* Acceleration tangential to track */
          def tangentialAt(x:Number):Number = {
            val dy =
              if (isCw) {
                (cx-x.value)/rad
              } else {
                (x.value-cx)/rad
              }
            // Leave out factor of g()
            Number(-dy)
          }
          val r1 = radialAt(evalTerm(y1))
          val r2 = radialAt(evalTerm(y2))
          val t1 = tangentialAt(evalTerm(x1))
          val t2 = tangentialAt(evalTerm(x2))
          val debugInfo1 = (iSection, (evalTerm(x1),evalTerm(y1)))
          val debugInfo2 = (iSection, (evalTerm(x2),evalTerm(y2)))
          env.extendR(r2, isCw, Some(debugInfo2)).extendR(r1, isCw, Some(debugInfo1)).extendT(t2).extendT(t1)
            .extendV(velSquaredAt(evalTerm(y1))).extendV(velSquaredAt(evalTerm(y2)))
      }}
    res.relaxBy()
  }

  def envelope(file:AFile):AccelEnvelope = {
    val (points, segments, v0, tent,_) = file
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive2(nonemptySegs,points)
    envelope(withBounds.head._2._1._2.asInstanceOf[Number], v0, withBounds)
  }

  /* Adjust y-coordinates such that all adjacent track segments are tangent to each other, while leaving x-coordinates alone
  * Coasters exported from CoasterX typically satisfy this property modulo floatiness, but it becomes slightly false due to rounding.
  * This should never be a "big" change in terms of magnitude, but can be a huge change in the complexity of the term.
  * There are a few different approaches to manage the size of the terms.
  * The main difficulty arises from irrational points lying on circles.
  * We leave the (rational) endpoints and beginning slope of an arc fixed, from
  * which nasty math (derived by Mathematica) derives an often-irrational point for the center of the circle.
  * However this also makes the end slope nasty, so we introduce extra variables for the center and radius to keep formula
  * size down. This can be hidden for sections where they are not relevant, keeping QE time under control. */
  private def alignFile(file:File):(AFile,Formula) = {
    val (points, segments, v0, tent) = file
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive2(nonemptySegs,points)
    val withoutSplits = unsplitZipped(withBounds)
    val alignedBounds = alignZipped(withoutSplits,None,0)
    val (pointss, segmentss, fml, dirs) = unzipConsecutive(alignedBounds)
    ((pointss, segments.head :: segmentss, v0, tent, dirs),fml)
  }
}
