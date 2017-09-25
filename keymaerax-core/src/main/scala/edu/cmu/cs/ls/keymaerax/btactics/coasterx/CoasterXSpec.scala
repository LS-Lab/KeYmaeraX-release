package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.AccelEnvelope.EnvScalar
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.{Section, _}
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
  // For short ranges smaller numbers are OK.
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
  val empty = AccelEnvelope(POS_INF, NEG_INF, POS_INF, NEG_INF)
}
case class AccelEnvelope(private val rMin:EnvScalar, private val rMax:EnvScalar, private val tMin:EnvScalar, private val tMax:EnvScalar) {
  import AccelEnvelope._

  private def round(x:Number):Number = {
    val MAX_SCALE = 4
    Number(x.value.setScale(MAX_SCALE,BigDecimal.RoundingMode.UP))
  }

  def radMin:Term = { round(rMin) }
  def radMax:Term = { round(rMax) }
  def tanMin:Term = { round(tMin) }
  def tanMax:Term = { round(tMax) }

  def printLoudly():Unit = {
    println("*************************************************************")
    println("*    ACCELERATION ENVELOPE                                  *")
    println("*************************************************************")
    println("MINIMUM RADIAL: " + radMin)
    println("MAXIMUM RADIAL: " + radMax)
    println("MINIMUM TANGENTIAL: " + tanMin)
    println("MAXIMUM TANGENTIAL: " + tanMax)
  }

  def extendR(r:EnvScalar):AccelEnvelope = {
    AccelEnvelope(scalarMin(rMin,r), scalarMax(rMax,r), tMin, tMax)
  }

  def extendT(t:EnvScalar):AccelEnvelope = {
    AccelEnvelope(rMin,rMax,scalarMin(t,tMin),scalarMax(t,tMax))
  }

  // Ratio of model units to meters
  val scale = 100.0
  val g = 9.80665
  // @TODO: Probably wrong
  private def scaleAccel(t:EnvScalar):EnvScalar = {
    Number(t.value/(scale*scale*g))
  }
  // Not intended for soundness criticality, but as a check during spec generation to ensure there's some chance of the
  // spec being useful
  def isSafe:Boolean = {
    scalarLeq(AccelEnvelope.MIN_TAN,tMin) && scalarLeq(tMax,AccelEnvelope.MAX_TAN) && scalarLeq(AccelEnvelope.MIN_RAD,rMin) && scalarLeq(rMax, AccelEnvelope.MAX_RAD)
  }

  val DEFAULT_TOLERANCE = Number(0.001)

  def relaxBy(tolerance:EnvScalar=DEFAULT_TOLERANCE):AccelEnvelope = {
    AccelEnvelope(Number(rMin.value-tolerance.value), Number(rMax.value+tolerance.value),Number(tMin.value-tolerance.value),Number(tMax.value+tolerance.value))
  }

  private def tanSpec(dy:Term):Formula = {
    s"($tanMin)*g() <= -($dy)*g() & -($dy)*g() <= ($tanMax)*g()".asFormula
  }

  def lineSpec(dy:Term):Formula = tanSpec(dy)

  def radSpec(r:Term, isCw:Boolean):Formula = {
    val a = s"v^2/($r)".asTerm //if(isCw) s"v^2/($r)".asTerm else s"-v^2/($r)".asTerm
    s"($radMin)*g()<=($a)&($a)<=($radMax)*g()".asFormula
  }

  def arcSpec(dy:Term, r:Term, isCw:Boolean):Formula = {
    And(radSpec(r, isCw), tanSpec(dy))
  }
}

/* Generate dL specification for safety of CoasterX models from a file
* */
object CoasterXSpec {
  type TPoint = (Term, Term)
  type Context = Map[BaseVariable, Term]
}
class CoasterXSpec {

  var ctx:Context = Map.empty

  /* Approximate term evaluator, with limited range especially for square roots.
   * Thus it's not suitable for rigorous proof purposes, but can be used both (a) for guiding spec+proof strategy when we need to compare irrational terms to
   * make a decision and (b) for general debugging purposes when we want a quantitative view on complicated terms */
  def evalTerm(t:Term):Number = {
    t match {
      case x:BaseVariable => evalTerm(ctx(x))
      case n:Number => n
      case Neg(x) => Number(-evalTerm(x).value)
      case Plus(x,y) => Number(evalTerm(x).value + evalTerm(y).value)
      case Minus(x,y) => Number(evalTerm(x).value - evalTerm(y).value)
      case Times(x,y) => Number(evalTerm(x).value * evalTerm(y).value)
      case Divide(x,y) => Number(evalTerm(x).value / evalTerm(y).value)
      case Power(x,y:Number) if y.value == 0 => Number(1)
      case Power(x,y:Number) if y.value.isValidInt && y.value > 0 => Number(evalTerm(x).value*evalTerm(Power(x,Number(y.value-1))).value)
      case Power(x,y) => Number(Math.pow(evalTerm(x).value.toDouble, evalTerm(y).value.toDouble))
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
        println("doin a thing")
        val a = Divide(t1,Power(t2,Number(pow2)))
        val b = Divide(t1,foldPower(t2,Number(pow2)))
        if (a != b) {println("Oh interesting", a, b)}
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
      case Divide(t1,t2) => foldDivide(compact(t1),compact(t2))
      case Minus(t1,t2) => foldMinus(compact(t1),compact(t2))
      case Neg(t) => foldNeg(compact(t))
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
    (cx,cy)
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
    def evol(isUp:Boolean) = {
      val ybound =
        if(isUp) {
          And(LessEqual(start._2, y), LessEqual(y, end._2))
        } else {
          And(LessEqual(end._2, y), LessEqual(y, start._2))
        }
      And(And(LessEqual(start._1, x), LessEqual(x, end._1)),
        ybound)
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
        val ode = ODESystem(sys, evol(isUp))
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
        val isLeft = t1 < -90 || t1 > 90 || (t1 == -90 && dt < 0) || (t1 == 90 && dt > 0)
        val isUp = (isLeft && isCw) || (!isLeft && !isCw)
        val (cx,cy) = iCenter(iSection)
        val (setx,sety) =
          if (isCw) {(s"-(($cy)-y)/($r)".asTerm, s"(($cx)-x)/($r)".asTerm)}
          else {(s"(($cy)-y)/($r)".asTerm, s"-(($cx)-x)/($r)".asTerm)}
        val ode = ODESystem(sys, evol(isUp))
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
    val (dxval, dyval) = iDirection(i)
    seg match {
      case LineSection(Some(LineParam((x1, y1), (x2, y2))), Some(gradient), isUp) =>
        val inRange = And(LessEqual(x1, x), LessEqual(x, x2))
        val dxInv = s"dx=($dxval)".asFormula
        val dyInv = s"dy=($dyval)".asFormula
        //val dInv = And(dxInv, dyInv)
        val onTrack = Equal(foldTimes(dxval, y), foldPlus(foldTimes(dyval, x), foldTimes(dxval,yOffset((x1, y1), (x2, y2)))))
        Imply(inRange, And(env.lineSpec(dyval),onTrack))
      case ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)) =>
        val ((x3, y3), (x4, y4)) = (start,end)
        val inRange = And(LessEqual(x3, x), LessEqual(x, x4))
        val (cx, cy) = iCenter(i)
        val r = iRadius(i)
        val centered = Equal(sqDist((x,y), (cx,cy)), foldPower(r,Number(2)))
        val isCw = param.deltaTheta.value < 0
        val t1 = theta1.value
        val dt = deltaTheta.value
        val isLeft = t1 < -90 || t1 > 90 || (t1 == -90 && dt < 0) || (t1 == 90 && dt > 0)
        val outY = if(isCw) LessEqual(cy,y) else LessEqual(y,cy)
        val outX = if(isLeft) LessEqual(x, cx) else LessEqual(cx, x)
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
      case _ => ???
    }
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
    val (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1, yy1), (xx2, yy2))) :: rest = secs
    val endDX = Variable("dx", Some(index))
    val endDY = Variable("dy", Some(index))
    val cx = Variable("cx", Some(index))
    val cy = Variable("cy", Some(index))
    val r = Variable("r", Some(index))
    val (cxe, cye) = centerFromStartSlope(xx1,yy1,xx2,yy2,(dx,dy))
    val re = dist((cx,cy),(xx1,yy1))
    val yendSign = if (param.theta2.value > 0) { Number(1) } else Number(-1)
    val xend = xx2
    val (dcxe, dcye) = (foldMinus(cx, xend), foldMinus(cy, yy2))
    val (dtxe, dtye) = normalizeVector(tangentFromCenter((dcxe,dcye), (param.theta1, param.theta2), param.deltaTheta))
    val cxDef:Formula = Equal(cx, cxe)
    val cyDef:Formula = Equal(cy, cye)
    val endDXDef:Formula = Equal(endDX, dtxe)
    val endDYDef:Formula = Equal(endDY, dtye)
    val rDef = Equal(r, re)
    val allDefs = And(rDef, And(And(cxDef, cyDef),And(endDXDef, endDYDef)))
    ctx = ctx.+(r -> re, cx -> cxe, cy -> cye, endDX -> dtxe, endDY -> dtye)
    // If we accidentally made this into a two-quadrant arc, then adjust again.
    // Yes, this is super nasty and could use some work
    val (t1,t2) = (theta1.value, normalizeAngle(theta1.value + deltaTheta.value))
    val q1 = t1 >= 0    && t1 <= 90  //&& t2 <= 90
    val q2 = t1 >= 90   && t1 <= 180 //!(q1 || q3 || q4)
    val q3 = t1 >= -180 && t1 <= -90 //&& t2 <= -90
    val q4 = t1 >= -90  && t1 <= 0   //&& t2 <= 0
    println("Attempting split maybe")
    val cxapprox = evalTerm(cxe).value
    val xx2approx = evalTerm(xx2).value
    if (cxapprox < xx2approx && q3) {
      assert(theta1.value <= -90 && param.theta2.value >= -90)
      // @TODO: This assumes it's a Q3-Q4 arc, but gotta start somewhere
      val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), theta1, Number(-90 - theta1.value))), Some(oldSlope)),
        ((xx1, yy1), (cx, foldMinus(cy,r))),
        allDefs,
        (endDX, endDY))
      // TODO: Need to set dx and such intermediately for those components
      // TODO: Not an obvious value for the deltatheta dude
      // TODO: Need to figure out definition numbering and stuff
      val endDX2 = Variable("dx", Some(index+1))
      val endDY2 = Variable("dy", Some(index+1))
      val cx2 = Variable("cx", Some(index+1))
      val cy2 = Variable("cy", Some(index+1))
      val r2 = Variable("r", Some(index+1))
      val cxDef2:Formula = Equal(cx2, cxe)
      val cyDef2:Formula = Equal(cy2, cye)
      val endDXDef2:Formula = Equal(endDX2, dtxe)
      val endDYDef2:Formula = Equal(endDY2, dtye)
      val rDef2 = Equal(r2, re)
      val allDefs2 = And(rDef2, And(And(cxDef2, cyDef2),And(endDXDef2, endDYDef2)))
      ctx = ctx.+(r2 -> re, cx2 -> cxe, cy2 -> cye, endDX2 -> dtxe, endDY2 -> dtye)
      val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)),
        Number(-90), Number((param.theta2.value - (-90)).max(1)))), Some(oldSlope)),
        ((cx, foldMinus(cy,r)), (xx2, yy2)),
        allDefs2,
        (endDX, endDY))
      sec1 :: sec2 :: alignZipped(rest, Some((endDX, endDY)), index + 2)
    } else if (cxapprox < xx2approx && q2) {
      // @TODO: This assumes it's a Q2-Q1 arc, but gotta start somewhere
      assert(param.theta1.value >= 90 && param.theta2.value <= 90)
      val sec1 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), theta1, Number(90-param.theta1.value))),
        Some(oldSlope)),
        ((xx1, yy1), (cx, foldPlus(cy,r))),
        allDefs,
        (endDX, endDY))
      // TODO: Need to set dx and such intermediately for those components
      // TODO: Not an obvious value for the deltatheta dude
      // TODO: Need to figure out definition numbering and stuff
      val endDX2 = Variable("dx", Some(index+1))
      val endDY2 = Variable("dy", Some(index+1))
      val cx2 = Variable("cx", Some(index+1))
      val cy2 = Variable("cy", Some(index+1))
      val r2 = Variable("r", Some(index+1))
      val cxDef2:Formula = Equal(cx2, cxe)
      val cyDef2:Formula = Equal(cy2, cye)
      val endDXDef2:Formula = Equal(endDX2, dtxe)
      val endDYDef2:Formula = Equal(endDY2, dtye)
      val rDef2 = Equal(r2, re)
      val allDefs2 = And(rDef2, And(And(cxDef2, cyDef2),And(endDXDef2, endDYDef2)))
      ctx = ctx.+(r2 -> re, cx2 -> cxe, cy2 -> cye, endDX2 -> dtxe, endDY2 -> dtye)
      val sec2 = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), Number(90), Number((param.theta2.value-90).min(-1)))), Some(oldSlope)),
        ((cx, foldPlus(cy,r)), (xx2, yy2)),
        allDefs2,
        (endDX, endDY))
      sec1 :: sec2 :: alignZipped(rest, Some((endDX, endDY)), index + 2)
    } else {
      val head = (ArcSection(Some(ArcParam((foldMinus(cx, r), foldMinus(cy, r)), (foldPlus(cx, r), foldPlus(cy, r)), theta1, deltaTheta)), Some(oldSlope)),
        ((xx1, yy1), (xx2, yy2)),
        allDefs,
        (endDX, endDY))
      head :: alignZipped(rest, Some((endDX, endDY)), index + 1)
    }
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
        ctx = ctx.+(endDX -> endD._1, endDY -> endD._2)
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
    val res =
    segs.foldRight(AccelEnvelope.empty){case((sec,((x1:Term,y1:Term),(x2:Term,y2:Term))), env) =>
      sec match {
        case (LineSection(Some(LineParam(bl,tr)),Some(grad), isUp)) =>
          // Line sections - no centripetal acceleration
          val (dx,dy) = lineDir(bl,tr)
          env.extendT(Number(evalTerm(Neg(dy)).value))
        case (ArcSection(Some(ArcParam(bl,tr,theta1,deltaTheta)), Some(grad))) =>
          val rad = (evalTerm(bl._1).value-evalTerm(tr._1).value).abs/2
          val cx = (evalTerm(bl._1).value + evalTerm(tr._1).value) /2
          /* Centripetal acceleration perpendicular to track */
          def radialAt(y:Number):Number = {
            val yy = y.value
            val KE = v0.value*v0.value + (2*y0.value) - (2*yy)
            val cent = KE/rad
            Number(cent)
          }
          /* Acceleration tangential to track */
          def tangentialAt(x:Number):Number = {
            val isCw = deltaTheta.value < 0
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
          env.extendR(r2).extendR(r1).extendT(t2).extendT(t1)
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
