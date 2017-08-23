package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/* Generate dL specification for safety of CoasterX models from a file */
object CoasterXSpec {

  /* @TODO (Major) #1: Apply arbitrary amounts of rounding to model to make numbers less gross
  *  @TODO (Major) #2: Maintain sanity of models by projecting all new straight line endpoints and arc control points
  *    so they are tangent to the previous section
  *  @TODO (Major) #3: Adopt arbitrary (closed) dL terms as number representation to enable exact projection.*/
  def degToRad(theta:Number):Number = {
    Number(2*Math.PI*theta.value.doubleValue()/360.0)
  }

  def radDir(rad:Number):Point = {
    (Number(Math.cos(rad.value.doubleValue())), Number(Math.sin(rad.value.doubleValue())))
  }

  def vecScale(xy:Point, scale:Number):Point = {
    (Number(xy._1.value*scale.value), Number(xy._2.value*scale.value))
  }

  def vecPlus(xy1:Point, xy2:Point):Point = {
    (Number(xy1._1.value + xy2._1.value),Number(xy1._2.value + xy2._2.value))
  }

  def min (x:Number,y:Number):Number = if (x.value < y.value) x else y

  def max (x:Number,y:Number):Number = if (x.value > y.value) x else y

  def boundingBox(points:List[Point]):(Point,Point) = {
    points.foldLeft((points.head,points.head))({case ((accbl,acctr),(x,y)) =>  ((min(accbl._1,x),min(accbl._2,y)),(max(acctr._1,x),max(acctr._2,y)))})
  }

  def arcBounds(xy1:Point, xy2:Point, theta1:Number, theta2:Number):(Point,Point) = {
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

  def arcCenter(xy1:Point, xy2:Point):Point = {
    (Number((xy1._1.value+xy2._1.value)/2), Number((xy2._2.value+xy2._2.value)/2))
  }

  def segmentOde(segBounds:(Section,(Point,Point))):Program = {
    val (seg, (start,end)) = segBounds
    val x = Variable("x")
    val evol = And(LessEqual(start._1, x),LessEqual(x,end._1))
    seg match {
      case LineSection(Some(LineParam((x1,y1),(x2,y2))), Some(gradient)) =>
        val v = Variable("v")
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        val xOde = AtomicODE(DifferentialSymbol(Variable("x")), Times(v, dxval))
        val yOde = AtomicODE(DifferentialSymbol(Variable("y")), Times(v, dyval))
        val vOde = "v' = -dy".asDifferentialProgram
        val sys = DifferentialProduct(DifferentialProduct(xOde,yOde),vOde)
        // val evol = And(LessEqual(x1,x),LessEqual(x,x2))
        ODESystem(sys, evol)
      case ArcSection(Some(ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
        val ((x3,y3),(x4,y4)) = arcBounds((x1,y1),(x2,y2),theta1,Number(theta1.value+deltaTheta.value))
        val r = Number((x4.value-x3.value)/2)
        val sysBase = "x' = dx*v, y' = dy*v, v' = -dy".asDifferentialProgram
        /* TODO: Set sign based on direction of arc */
        val sys = DifferentialProduct(sysBase,DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("dx")), Divide("-dy*v".asTerm, r)),
          AtomicODE(DifferentialSymbol(Variable("dy")), Divide("dx*v".asTerm, r))))
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

  def lineDir(xy1:Point, xy2:Point):Point = {
    val mag = numSqrt(Number((xy2._1.value - xy1._1.value).pow(2) + (xy2._2.value - xy1._2.value).pow(2)))
    (Number((xy2._1.value-xy1._1.value)/mag.value), Number((xy2._2.value-xy1._2.value)/mag.value))
  }

  def segmentPre(seg:Section, v0:Number):Formula = {
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
        val ((x3,y3),(x4,y4)) = arcBounds((x1,y1),(x2,y2),theta1,Number(theta1.value+deltaTheta.value))
        val (cx, cy) = arcCenter((x1,y1),(x2,y2))
        val dx = Variable("dx")
        val dy = Variable("dy")
        val x = Variable("x")
        val y = Variable("y")
        val v = Variable("v")
        val r = Variable("r")
        val dxeq = Equal(dx,Divide(Neg(Minus(y,cy)),r))
        val dyeq = Equal(dy,Divide(Minus(x,cy),r))
        val xeq = Equal(x,x3)
        val yeq = Equal(y,y3)
        val veq = Equal(v, v0)
        And(dxeq,And(dyeq,And(xeq,And(yeq,veq))))
      case _ => True
    }
  }

  def slope(xy1:Point, xy2:Point):Number = {
    Number((xy1._2.value-xy2._2.value)/(xy1._1.value-xy2._1.value))
  }

  /* y-intercept of segment */
  def yOffset(xy1:Point, xy2:Point):Number = {
    Number(xy1._2.value - (slope(xy1,xy2).value*xy1._1.value))
  }

  def segmentPost(segBounds:(Section,(Point,Point))):Formula = {
    val (seg, (start, end)) = segBounds
    val x = Variable("x")
    val y = Variable("y")
    seg match {
      case LineSection(Some(LineParam((x1, y1), (x2, y2))), Some(gradient)) =>
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        val inRange = And(LessEqual(x1, x), LessEqual(x, x2))
        val onTrack = Equal(Times(dxval, y), Plus(Times(dyval, x), yOffset((x1, y1), (x2, y2))))
        Imply(inRange, onTrack)
      case ArcSection(Some(ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)) =>
        val ((x3, y3), (x4, y4)) = arcBounds((x1, y1), (x2, y2), theta1, Number(theta1.value+deltaTheta.value))
        val inRange = And(LessEqual(x3, x), LessEqual(x, x4))
        val r = Number((x4.value - x3.value) / 2)
        val (cx, cy) = arcCenter((x1, y1), (x2, y2))
        val centered = Equal(Plus(Power(Minus(cx, x), Number(2)), Power(Minus(cy, y), Number(2))), Number(r.value * r.value))
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
    val pre = segmentPre(nonemptySegs.head,v0)
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
