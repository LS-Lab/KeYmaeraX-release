package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/* Generate dL specification for safety of CoasterX models from a file */
object CoasterXSpec {

  def foldMinus(t1:Term, t2:Term):Term = {
    (t1,t2) match {
      case (n1:Number,n2:Number) => Number(n1.value - n2.value)
      case _ => Minus(t1,t2)
    }
  }

  def foldPlus(t1:Term, t2:Term):Term = {
    val candidate =
      (t1,t2) match {
        case (n1:Number,n2:Number) => Number(n1.value + n2.value)
        case _ => Plus(t1,t2)
      }
    candidate match {
      case (Plus(x,Neg(y))) => Minus(x,y)
      case _ => candidate
    }
  }

  def foldTimes(t1:Term, t2:Term):Term = {
    (t1,t2) match {
      case (n1:Number,n2:Number) => Number(n1.value * n2.value)
      case _ => Times(t1,t2)
    }
  }

  def foldDivide(t1:Term, t2:Term):Term = {
    val candidate =
      (t1,t2) match {
      case (n1:Number,n2:Number) if n1.value.remainder(n2.value) == BigDecimal(0) => Number(n1.value / n2.value)
      case _ => Divide(t1,t2)
    }
    candidate match {
      case (Divide(Number(n), denom)) if n == BigDecimal(0) => denom
      case _ => candidate
    }
  }

  def foldPower(t1:Term, t2:Term):Term = {
    (t1,t2) match {
      case (n1:Number,n2:Number) if n2.value == BigDecimal(0)  => Number(1)
      case (n1:Number,n2:Number) if n2.value.isValidInt && n2.value > 0  =>
        val tail:Number = foldPower(n1,Number(n2.value-1)).asInstanceOf[Number]
        Number(tail.value*n1.value)
      case _ => Power(t1,t2)
    }
  }

  def foldNeg(t1:Term):Term = {
    t1 match {
      case n:Number => Number(-n.value)
      case _ => Neg(t1)
    }
  }

  /* @TODO (Major) #2: Maintain sanity of models by projecting all new straight line endpoints and arc control points
  *    so they are tangent to the previous section*/
  def degToRad(theta:Number):Number = {
    Number(2*Math.PI*theta.value.doubleValue()/360.0)
  }

  def radDir(rad:Number):Point = {
    (Number(Math.cos(rad.value.doubleValue())), Number(Math.sin(rad.value.doubleValue())))
  }

  def vecScale(xy:(Term,Term), scale:Number):(Term,Term) = {
    (foldTimes(xy._1,scale), foldTimes(xy._2,scale))
  }

  def vecPlus(xy1:(Term,Term), xy2:(Term,Term)):(Term,Term) = {
    (foldPlus(xy1._1,xy2._1),foldPlus(xy1._2, xy2._2))
  }

  def min (x:Term,y:Term):Term = FuncOf(Function("min", domain = Tuple(Real,Real), interpreted = true, sort = Real), Pair(x,y))

  def max (x:Term,y:Term):Term = FuncOf(Function("max", domain = Tuple(Real,Real), interpreted = true, sort = Real), Pair(x,y))

  def boundingBox(points:List[(Term,Term)]):((Term,Term),(Term,Term)) = {
    points.foldLeft((points.head,points.head))({case ((accbl,acctr),(x,y)) =>  ((min(accbl._1,x),min(accbl._2,y)),(max(acctr._1,x),max(acctr._2,y)))})
  }

  def arcBounds(xy1:Point, xy2:Point, theta1:Number, theta2:Number):((Term,Term),(Term,Term)) = {
    val rad1 = degToRad(theta1)
    val rad2 = degToRad(theta2)
    val (cx, cy) = arcCenter((xy1),(xy2))
    val r = Number((xy2._1.value-xy1._1.value)/2)
    val dir1 = radDir(rad1)
    val dir2 = radDir(rad2)
    val scale1 = vecScale(dir1,r)
    val scale2 =vecScale(dir2,r)
    val sum1 = vecPlus((cx,cy),scale1)
    val sum2 = vecPlus((cx,cy),scale2)
    val box = boundingBox(List(sum1, sum2))
    box
  }

  def arcCenter(xy1:Point, xy2:Point):(Term, Term) = {
    (foldDivide(foldPlus(xy1._1,xy2._1),Number(2)), foldDivide(foldPlus(xy1._2,xy2._2),Number(2)))
  }

  def segmentOde(segBounds:(Section,(Point,Point))):Program = {
    val (seg, (start,end)) = segBounds
    val x = Variable("x")
    val evol = And(LessEqual(start._1, x),LessEqual(x,end._1))
    seg match {
      case LineSection(Some(LineParam((x1,y1),(x2,y2))), Some(gradient)) =>
        val v = Variable("v")
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        val xOde = AtomicODE(DifferentialSymbol(Variable("x")), foldTimes(v, dxval))
        val yOde = AtomicODE(DifferentialSymbol(Variable("y")), foldTimes(v, dyval))
        val vOde = "v' = -dy".asDifferentialProgram
        val sys = DifferentialProduct(DifferentialProduct(xOde,yOde),vOde)
        // val evol = And(LessEqual(x1,x),LessEqual(x,x2))
        ODESystem(sys, evol)
      case ArcSection(Some(ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
        //val ((x3,y3),(x4,y4)) = arcBounds((x1,y1),(x2,y2),theta1,Number(theta1.value+deltaTheta.value))
        //val r = Number((x4.value-x3.value)/2)
        val r = foldDivide(foldMinus(end._1,start._1),Number(2))
        val sysBase = "x' = dx*v, y' = dy*v, v' = -dy".asDifferentialProgram
        /* TODO: Set sign based on direction of arc */
        val sys = DifferentialProduct(sysBase,DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("dx")), foldDivide("-dy*v".asTerm, r)),
          AtomicODE(DifferentialSymbol(Variable("dy")), foldDivide("dx*v".asTerm, r))))
        // val evol = And(LessEqual(x3,x),LessEqual(x,x4))
        ODESystem(sys, evol)
      case _ => Test(True)
    }
  }

  /* This is evidently not part of the standard library for BigDecimal, but I also haven't decided what number
   * representation to go with yet...
   */
  def numSqrt(n:Number):Number = {
    // TODO: Real bad implementation
    Number(Math.sqrt(n.value.doubleValue()))
  }

  def lineDir(xy1:Point, xy2:Point):(Term,Term) = {
    val mag:Term = foldPower(foldPlus(foldPower(foldMinus(xy2._1,xy1._1),Number(2)),foldPower(foldMinus(xy2._2,xy1._2),Number(2))),foldDivide(Number(1),Number(2)))
    //val mag = numSqrt(Number((xy2._1.value - xy1._1.value).pow(2) + (xy2._2.value - xy1._2.value).pow(2)))
    (foldDivide(foldMinus(xy2._1,xy1._1),mag), foldDivide(foldMinus(xy2._2,xy1._2),mag))
  }

  def segmentPre(segBounds:(Section,(Point,Point)), v0:Number):Formula = {
    val (seg, (start,end)) = segBounds
    seg match {
      case LineSection(Some(LineParam((x1,y1),(x2,y2))), Some(gradient)) =>
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
        And(dxeq,And(dyeq,And(xeq,And(yeq,veq))))
      case ArcSection(Some(ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
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
        // ((x1,y1),(x2,y2),theta1,Number(theta1.value+deltaTheta.value))
        val ((x3,y3),(x4,y4)) = (start,end)
        val (cx, cy) = arcCenter((x1,y1),(x2,y2))
        val dx = Variable("dx")
        val dy = Variable("dy")
        val x = Variable("x")
        val y = Variable("y")
        val v = Variable("v")
        val r = Variable("r")
        val dxeq = Equal(dx,foldDivide(foldNeg(foldMinus(y,cy)),r))
        val dyeq = Equal(dy,foldDivide(foldMinus(x,cy),r))
        val xeq = Equal(x,x3)
        val yeq = Equal(y,y3)
        val veq = Equal(v, v0)
        And(dxeq,And(dyeq,And(xeq,And(yeq,veq))))
      case _ => True
    }
  }

  def slope(xy1:Point, xy2:Point):Term = {
    foldDivide(foldMinus(xy1._2, xy2._2),foldMinus(xy1._1, xy2._1))
  }

  /* y-intercept of segment */
  def yOffset(xy1:Point, xy2:Point):Term = {
    foldMinus(xy1._2,foldTimes(slope(xy1,xy2), xy1._1))
  }

  def segmentPost(segBounds:(Section,(Point,Point))):Formula = {
    val (seg, (start, end)) = segBounds
    val x = Variable("x")
    val y = Variable("y")
    seg match {
      case LineSection(Some(LineParam((x1, y1), (x2, y2))), Some(gradient)) =>
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        val inRange = And(LessEqual(x1, x), LessEqual(x, x2))
        val onTrack = Equal(foldTimes(dxval, y), foldPlus(foldTimes(dyval, x), yOffset((x1, y1), (x2, y2))))
        Imply(inRange, onTrack)
      case ArcSection(Some(ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)) =>
        val ((x3, y3), (x4, y4)) = (start,end)
          //val ((x3, y3), (x4, y4)) =arcBounds((x1, y1), (x2, y2), theta1, Number(theta1.value+deltaTheta.value))

        val inRange = And(LessEqual(x3, x), LessEqual(x, x4))
        val r = foldDivide(foldMinus(end._1,start._1),Number(2))
        //  val r = Number((x4.value - x3.value) / 2)
        val (cx, cy) = arcCenter((x1, y1), (x2, y2))
        val centered = Equal(foldPlus(foldPower(foldMinus(cx, x), Number(2)), foldPower(foldMinus(cy, y), Number(2))), foldPower(r,Number(2)))
        val outRange = And(LessEqual(x, cx), Less(cy, y))
        /* (x0 + l <= x & x <= xend) -> ((cx - x)^2 + (cy - y)^2 = r^2 & x <= cx & cy < y))*/
        Imply(inRange, And(centered, outRange))
      case _ => True
    }
  }
  /* (x0 <= x & x <= x0 + l) -> y = m*x + c) */
  /*((x0 + l <= x & x <= xend) -> ((cx - x)^2 + (cy - y)^2 = r^2 & x <= cx & cy < y))*/

  def segmentEmpty(seg:Section):Boolean = {
    seg match {
      case LineSection(Some(_),Some(_)) => false
      case LineSection(_, _) => true
      case ArcSection(Some(_), Some(_)) => false
      case ArcSection(_, _) => true
    }
  }

  // assumes ys.length = xs.length + 1
  def zipConsecutive[A,B](xs:List[A],ys:List[B]):List[(A,(B,B))] = {
    (xs, ys) match {
      case (x1::xss, y1::y2::yss) =>  (x1,(y1,y2)) :: zipConsecutive(xss, y2::yss)
      case (Nil, _::Nil) => Nil
      case _ => ???
    }
  }

  def apply(file:CoasterXParser.File):Formula = {
    val ROUND_SCALE = 0
    val fileRounded = roundFile (ROUND_SCALE)(file)
    val (points, segments, v0, _) = fileRounded
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive(nonemptySegs,points)
    val pre = segmentPre(withBounds.head,v0)
    val ode = withBounds.map(segmentOde).reduceRight[Program]({case(x,y) => Choice(x,y)})
    val energyConserved = "v^2 + 2*y = v0^2 + 2*y0".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    val post = And(globalPost, withBounds.map(segmentPost).reduceRight[Formula]{case (x,y) => And(x,y)})
    Imply(pre,Box(Loop(ode), post))
  }

  def roundNumber(scale:Int)(n:Number):Number = {
    Number(new BigDecimal(n.value.bigDecimal).setScale(scale, BigDecimal.RoundingMode.DOWN))
  }

  def roundPoint(scale:Int)(xy:Point):Point = {
    (roundNumber(scale)(xy._1), roundNumber(scale)(xy._2))
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
      case ArcSection(param, grad) => ArcSection(param.map(roundArcParam(scale)), grad.map(roundNumber(scale)))
      case LineSection(param, grad) => LineSection(param.map(roundLineParam(scale)), grad.map(roundNumber(scale)))
    }
  }

  /* Mostly to produce readable models, also avoids making QE deal with obnoxiously large literals - though not clear whether the latter is a practical concern */
  def roundFile (scale:Int)(file:File):File = {
    val (points, segments, v0, tent) = file
    (points.map(roundPoint(scale)), segments.map(roundSegment(scale)), roundNumber(scale)(v0), roundParam(scale)(tent))
  }

  /* x'  =  dx * v,  y' = dy * v,
v'  =  -dy
dx' =  -dy*v/r,
dy' =  dx*v/r,*/

}
