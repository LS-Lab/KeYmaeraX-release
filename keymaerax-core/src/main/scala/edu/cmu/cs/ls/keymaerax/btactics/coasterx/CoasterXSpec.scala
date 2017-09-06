package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/* Generate dL specification for safety of CoasterX models from a file
* @TODO: Straight-line case: consider turning dx, dy into assignment instead of plugging directly into ODE
* */
object CoasterXSpec {

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
    val candidate =
    (t1,t2) match {
      case (n1:Number,n2:Number) if n2.value == BigDecimal(0)  => Number(1)
      case (n1:Number,n2:Number) if n2.value.isValidInt && n2.value > 0  =>
        val tail:Number = foldPower(n1,Number(n2.value-1)).asInstanceOf[Number]
        Number(tail.value*n1.value)
      case (n1:Number, pow) if n1 == Number(1) && pow != Number(0) => n1
      case (n1:Number, pow) if n1 == Number(0) && pow != Number(0) => n1
      case _ => Power(t1,t2)
    }
    // silly optimization because it happens in our models
    candidate match {
      case Power(Divide(Power(t1,Number(pow1)),t2),Number(pow2)) if pow1 * pow2 == 1 =>
        Divide(t1,Power(t2,Number(pow2)))
      case x => x
    }
  }

  def foldNeg(t1:Term):Term = {
    t1 match {
      case n:Number => Number(-n.value)
      case _ => Neg(t1)
    }
  }

  def degToRad(theta:Number):Number = {
    Number(2*Math.PI*theta.value.doubleValue()/360.0)
  }

  def radDir(rad:Number):Point = {
    (Number(Math.cos(rad.value.doubleValue())), Number(Math.sin(rad.value.doubleValue())))
  }

  def slopeDir(t:Term):TPoint = {
    (foldDivide(Number(1), foldPower(foldPlus(Number(1),foldPower(t,Number(2))),foldDivide(Number(1),Number(2)))),
     foldDivide(t, foldPower(foldPlus(Number(1),foldPower(t,Number(2))),foldDivide(Number(1),Number(2)))))
  }
  def vecScale(xy:(Term,Term), scale:Term):(Term,Term) = {
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

  def arcCenter(xy1:TPoint, xy2:TPoint):(Term, Term) = {
    (foldDivide(foldPlus(xy1._1,xy2._1),Number(2)), foldDivide(foldPlus(xy1._2,xy2._2),Number(2)))
  }

  def segmentOde(segBounds:(Section,(TPoint,TPoint))):Program = {
    val (seg, (start,end)) = segBounds
    val x = Variable("x")
    val y = Variable("y")
    val evol = And(And(LessEqual(start._1, x),LessEqual(x,end._1)),
      And(LessEqual(start._2, y),LessEqual(y,end._2)))
    seg match {
      case LineSection(Some(LineParam((x1,y1),(x2,y2))), Some(gradient)) =>
        val v = Variable("v")
        val dx = Variable("dx")
        val dy = Variable("dy")
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        // Inlined version of ODE not used right now but still experimenting
        val xOdeInlined = AtomicODE(DifferentialSymbol(Variable("x")), foldTimes(v, dxval))
        val yOdeInlined = AtomicODE(DifferentialSymbol(Variable("y")), foldTimes(v, dyval))
        val vOdeInlined = s"v' = -($dyval)".asDifferentialProgram
        val sysInlined = DifferentialProduct(DifferentialProduct(xOdeInlined,yOdeInlined),vOdeInlined)
        val xOde = AtomicODE(DifferentialSymbol(Variable("x")), foldTimes(v,dx))
        val yOde = AtomicODE(DifferentialSymbol(Variable("y")), foldTimes(v,dy))
        val vOde = s"v' = -dy".asDifferentialProgram
        val sys = DifferentialProduct(DifferentialProduct(xOde,yOde),vOde)
        // val evol = And(LessEqual(x1,x),LessEqual(x,x2))
        ODESystem(sys, evol)
      case ArcSection(Some(ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
        //val ((x3,y3),(x4,y4)) = arcBounds((x1,y1),(x2,y2),theta1,Number(theta1.value+deltaTheta.value))
        //val r = Number((x4.value-x3.value)/2)
        val r = foldDivide(foldMinus(x2,x1),Number(2))
        val sysBase = "x' = dx*v, y' = dy*v, v' = -dy".asDifferentialProgram
        val isCw = deltaTheta.value < 0
        val (dxTerm, dyTerm) = if (isCw) {(foldDivide("dy*v".asTerm, r), foldDivide("-dx*v".asTerm, r))} else {(foldDivide("-dy*v".asTerm, r), foldDivide("dx*v".asTerm, r))}
        val sys = DifferentialProduct(sysBase,DifferentialProduct(AtomicODE(DifferentialSymbol(Variable("dx")), dxTerm),
          AtomicODE(DifferentialSymbol(Variable("dy")), dyTerm)))
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

  def lineDir(xy1:TPoint, xy2:TPoint):(Term,Term) = {
    val mag:Term = foldPower(foldPlus(foldPower(foldMinus(xy2._1,xy1._1),Number(2)),foldPower(foldMinus(xy2._2,xy1._2),Number(2))),foldDivide(Number(1),Number(2)))
    //val mag = numSqrt(Number((xy2._1.value - xy1._1.value).pow(2) + (xy2._2.value - xy1._2.value).pow(2)))
    (foldDivide(foldMinus(xy2._1,xy1._1),mag), foldDivide(foldMinus(xy2._2,xy1._2),mag))
  }


  /* Nasty math provided by Mathematica: Compute center of circle using two points on circle and tangent vector*/
  def centerFromStartSlope (x1:Term, x2:Term, y1:Term, y2:Term, dxy:TPoint) = {
    // TODO: slope to direction means gross terms
    val (a,b) = dxy
    val cxnum= /*foldNeg(*/
      foldPlus(foldPlus(foldPlus(foldNeg(a),foldPower(x1,Number(2))), foldPlus(foldPlus(a,foldPower(x2,Number(2))),foldMinus(foldMinus(foldTimes(Number(2),foldTimes(b,foldTimes(x1,y1))), foldTimes(Number(3),foldTimes(a,foldPower(y1,Number(2))))),foldTimes(Number(2),foldTimes(b,foldTimes(x1,y2)))))),
        foldPlus(foldTimes(Number(2),foldTimes(a,foldTimes(y1,y2))), foldTimes(a,foldPower(y2,Number(2)))))
    val cxden = foldTimes(Number(2), foldPlus(foldMinus(foldMinus(foldTimes(a,x1), foldTimes(a,x2)),foldTimes(b,y1)), foldTimes(b,y2)))
    val cx = foldNeg(foldDivide(cxnum,cxden))
    val cyterm = foldTimes(Number(2), foldTimes(a, foldTimes(foldPlus(foldNeg(x1),x2),y1)))
    val cyfac = foldPlus(foldMinus(foldPlus(foldMinus(foldPower(x1,Number(2)),foldTimes(Number(2),foldTimes(x1,x2))), foldPower(x2,Number(2))), foldPower(y1,Number(2))),foldPower(y2,Number(2)))
    val cynum = foldPlus(cyterm, foldTimes(b,cyfac))
    val cyden =foldTimes(Number(2),foldPlus(foldTimes(a,foldMinus(x1,x2)),foldTimes(b,foldMinus(y2,y1))))
    val cy = foldNeg(foldDivide(cynum,cyden))
    (cx,cy)
  }
  // Compute direction-to-center vector using tangent vector and wiseness
  def centerFromTangent(dir:TPoint, angles:(Number,Number), delta:Number) = {
    val isCw = delta.value < 0
    if (isCw) {
      (dir._2, foldNeg(dir._1))
    } else {
      (foldNeg(dir._2), dir._1)
    }
  }
  def tangentFromCenter(dir:TPoint, angles:(Number,Number), delta:Number) =
    centerFromTangent(dir, angles.swap, foldNeg(delta).asInstanceOf[Number])

  def sqDist (p1:TPoint, p2:TPoint):Term = {
    foldPlus(foldPower(foldMinus(p1._1,p2._1), Number(2)), foldPower(foldMinus(p1._2,p2._2),Number(2)))
  }

  def dist (p1:TPoint, p2:TPoint):Term = {
    foldPower(sqDist(p1,p2),foldDivide(Number(1),Number(2)))
  }

  def segmentPre(segBounds:(Section,(TPoint,TPoint)), v0:Number):Formula = {
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
      case ArcSection(Some(param@ArcParam((x1,y1),(x2,y2),theta1,deltaTheta)), Some(gradient)) =>
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
        //val dxeq = Equal(dx,foldDivide(foldNeg(foldMinus(y,cy)),r))
        val dyeq = Equal(dy,dty)
        val xeq = Equal(x,x3)
        val yeq = Equal(y,y3)
        val veq = Equal(v, v0)
        And(dxeq,And(dyeq,And(xeq,And(yeq,veq))))
      case _ => True
    }
  }

  def slope(xy1:TPoint, xy2:TPoint):Term = {
    foldDivide(foldMinus(xy1._2, xy2._2),foldMinus(xy1._1, xy2._1))
  }

  /* y-intercept of segment */
  def yOffset(xy1:TPoint, xy2:TPoint):Term = {
    foldMinus(xy1._2,foldTimes(slope(xy1,xy2), xy1._1))
  }

  def segmentPost(segBounds:(Section,(TPoint,TPoint))):Formula = {
    val (seg, (start, end)) = segBounds
    val x = Variable("x")
    val y = Variable("y")
    seg match {
      case LineSection(Some(LineParam((x1, y1), (x2, y2))), Some(gradient)) =>
        val (dxval, dyval) = lineDir((x1, y1), (x2, y2))
        val inRange = And(LessEqual(x1, x), LessEqual(x, x2))
        val dxInv = s"dx=($dxval)".asFormula
        val dyInv = s"dy=($dyval)".asFormula
        val dInv = And(dxInv, dyInv)
        val onTrack = Equal(foldTimes(dxval, y), foldPlus(foldTimes(dyval, x), foldTimes(dxval,yOffset((x1, y1), (x2, y2)))))
        Imply(inRange, And(dInv,onTrack))
      case ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)) =>
        val ((x3, y3), (x4, y4)) = (start,end)
          //val ((x3, y3), (x4, y4)) =arcBounds((x1, y1), (x2, y2), theta1, Number(theta1.value+deltaTheta.value))
        val inRange = And(LessEqual(x3, x), LessEqual(x, x4))
        //foldDivide(foldMinus(x2,x1),Number(2))
        //  val r = Number((x4.value - x3.value) / 2)
        val (cx, cy) = arcCenter((x1, y1), (x2, y2))
        val r = dist(start, (cx,cy))
        val centered = Equal(sqDist((x,y), (cx,cy)), foldPower(r,Number(2)))
        val isCw = param.deltaTheta.value < 0
        val isLeft = start._1.asInstanceOf[Number].value < cx.asInstanceOf[Number].value
        val outY = if(isCw) LessEqual(cy,y) else LessEqual(y,cy)
        val outX = if(isLeft) LessEqual(x, cx) else LessEqual(cx, x)
        val outRange = And(outX, outY)
        val (dxInv, dyInv) =
          if (isCw) {
            (s"dx=-(($cy)-y)/($r)".asFormula, s"dy=(($cx)-x)/($r)".asFormula)
          } else {
            (s"dx=-(y-($cy))/($r)".asFormula, s"dy=(x-($cx))/($r)".asFormula)
          }
        val dInv = And(dxInv, dyInv)
        /* (x0 + l <= x & x <= xend) -> ((cx - x)^2 + (cy - y)^2 = r^2 & x <= cx & cy < y))*/
        Imply(inRange, And(dInv, And(centered, outRange)))
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

  def prepareFile(file:CoasterXParser.File):(File,Formula) = {
    val ROUND_SCALE = 0
    val fileRounded = roundFile (ROUND_SCALE)(file)
    alignFile(fileRounded)
  }

  def fromAligned(align:(File,Formula)):Formula = {
    val (aligned@(points, segments, v0, _), segmentDefs) = align
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive(nonemptySegs,points)
    val pre = segmentPre(withBounds.head,v0)
    val ode = withBounds.map(segmentOde).reduceRight[Program]({case(x,y) => Choice(x,y)})
    val y0 = points.head._2
    val energyConserved = s"v^2 + 2*y = ($v0)^2 + 2*($y0)".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    val post = And(globalPost, withBounds.map(segmentPost).reduceRight[Formula]{case (x,y) => And(x,y)})
    Imply(And(segmentDefs,pre),Box(Loop(ode), post))
  }

  def apply(file:CoasterXParser.File):Formula = {
    fromAligned(prepareFile(file))
  }

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
      case LineSection(param, grad) => LineSection(param.map(roundLineParam(scale)), grad.map(roundTerm(scale)))
    }
  }

  /* Mostly to produce readable models, also avoids making QE deal with obnoxiously large literals - though not clear whether the latter is a practical concern */
  def roundFile (scale:Int)(file:File):File = {
    val (points, segments, v0, tent) = file
    (points.map(roundPoint(scale)), segments.map(roundSegment(scale)), roundNumber(scale)(v0), roundParam(scale)(tent))
  }

  type TPoint = (Term,Term)

  def setStartY(sections:List[(Section,(TPoint,TPoint))], y:Term) = {
    sections match {
      case (LineSection(Some(LineParam((x1,y1),(x2,y2))),Some(grad)), ((xx1, yy1), (xx2, yy2))) :: rest =>
        (LineSection(Some(LineParam((x1,y),(x2,y2))),Some(grad)), ((xx1, y), (xx2, yy2))) :: rest
      case (ArcSection(Some(ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)), ((xx1, yy1), (xx2, yy2))) :: rest =>
        (ArcSection(Some(ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(gradient)), ((xx1, y), (xx2, yy2))) :: rest
      case _ => sections

    }
  }

  def magnitude(xy:TPoint):Term = {
    val (x,y) = xy
    foldPower(foldPlus(foldPower(x,Number(2)), foldPower(y,Number(2))),Divide(Number(1),Number(2)))
  }

  def normalizeVector(xy:TPoint):TPoint = {
    val (x,y) = xy
    (foldDivide(x,magnitude(xy)), foldDivide(y,magnitude(xy)))
  }

  /* @param zip is a list of sections annotated with their lower-left and upper-right boundaries
  *  @param dL term (e.g. a variable m_i) representing the slope of the previous line segment, or None if this is the first segment.
  *   (@TODO: use direction vectors instead of slopes in order to handle vertical sections)
  *   (@TODO: Should basically-never truly need to introduce a new slope variable in the straight line segment case, but
  *    currently always introduces a variable in ordr to make it easier to keep track of the variables)
  *  @return List of rounded sections with their rounded bounding boxes, with a formula defining any new variables introduced
  *    to define the segment, e.g. x_i, y_i, m_i
  *    */
  def alignZipped(zip:List[(Section,(TPoint,TPoint))], initD:Option[TPoint], index:Int):List[(Section,(TPoint,TPoint), Formula)] = {
    zip match {
      case Nil => Nil
      case (LineSection(Some(LineParam((x1,y1),(x2,y2))),Some(_)), ((xx1, yy1), (xx2, yy2))) :: rest =>
        val endY = Variable("y", Some(index))
        val endM = Variable("m", Some(index)) // @TODO: Totally redundant but probably makesn life easier
        val defaultD = normalizeVector((foldMinus(xx2,xx1), foldMinus(yy2,xx1)))
        val endMTerm = initD match {case Some((dx,dy)) => foldDivide(dy,dx) case None => foldDivide(foldMinus(yy2,yy1),foldMinus(xx2,xx1))}
        val endYTerm = initD match {case Some((dx,dy)) => foldPlus(foldTimes(foldDivide(dy,dx), foldMinus(xx2,xx1)),yy1) case None => yy2}
        val endYDef:Formula = Equal(endY, endYTerm)
        val endMDef:Formula = Equal(endM, endMTerm)
        val allDefs = endYDef // Ignore slopes for now
        val head = (LineSection(Some(LineParam((xx1,yy1),(xx2,endY))), Some(endM)), ((xx1,yy1),(xx2,endY)), allDefs)
        val endD:TPoint = initD.getOrElse(defaultD)
        head :: alignZipped(setStartY(rest,endY), Some(endD), index+1)
      case (ArcSection(Some(param@ArcParam((x1, y1), (x2, y2), theta1, deltaTheta)), Some(oldSlope)), ((xx1, yy1), (xx2, yy2))) :: rest =>
        // Algorithm: Take (x0, y1), (dx0, dy0), (cx, cy) as given (where cx, cy based on xx1,yy1,xx2,yy2).
        // Pray the resulting circle still intersects (x1, ???) for some ??? and compute a new value of y1 to fill in ???
        val endY = Variable("y", Some(index))
        val endM = Variable("m", Some(index)) // @TODO: Totally redundant but probably makesn life easier
        // Compute default center, vector-to-center and tangent vector
        val (cx, cy) = arcCenter((x1,y1),(x2,y2))
        val (dcxD, dcyD) = (foldMinus(cx, xx1), foldMinus(cy, yy1))
        val directionD = tangentFromCenter((dcxD,dcyD), (param.theta1, param.theta2), param.deltaTheta)
        val rad = foldDivide(foldMinus(x2,x1),Number(2))
        // @TODO: first need to correct center by projecting to where stuff is ok
        // by geometry, yend^2 = cy +- sqrt(r^2 - (cx-x)^2), which +- depends on quadrant
        val yendSign = if (param.theta2.value > 0) { Number(1) } else Number(-1)
        val xend = xx2
        // TODO: Double-check definition
        val yEndTerm =  foldPlus(cy, foldTimes(yendSign, foldPower(foldMinus(foldPower(rad,Number(2)),foldPower(foldMinus(cx,xend),Number(2))), foldDivide(Number(1),Number(2)))))
        val (dcxe, dcye) = (foldMinus(cx, xend), foldMinus(cy, endY))
        val (dtxe, dtye) = tangentFromCenter((dcxe,dcye), (param.theta1, param.theta2), param.deltaTheta)
        //val mEndTerm = foldDivide(foldMinus(newcy,endY), foldMinus(xend,newcx))
        val mEndTerm = foldDivide(dtye,dtxe)
        val endYDef:Formula = Equal(endY, yEndTerm)
        val endMDef:Formula = Equal(endM, mEndTerm)
        val allDefs = endYDef //Ignore slopes for now
        val head = (ArcSection(Some(ArcParam((foldMinus(cx,rad), foldMinus(cy,rad)), (foldPlus(cx,rad), foldPlus(cy,rad)), theta1, deltaTheta)), Some(oldSlope)),
          ((xx1, yy1), (xx2, endY)),
          allDefs)
        // Note: Start slope for next line is variable, keeps size reasonable
        head :: alignZipped(setStartY(rest, endY), Some(dtxe,dtye), index+1)
      case _ => ???
    }
    //val (dxC, dyC) = centerFromTangent((dx,dy), (param.theta1,param.theta2))
    //val (newcx, newcy) = vecPlus((xx1,yy1), vecScale((dxC,dyC), rad))
    //val centerSlope = foldDivide(Number(-1), slope2)
    //val cyy = foldPlus(yy1,foldTimes(dx,foldMinus(newcx,xx1)))
    //((2 a (-x1 + x2) y1
    //            + b (x1^2 - 2 x1 x2 + x2^2 - y1^2 + y2^2))/
    //            (2 (a (x1 - x2) + b (-y1 + y2))))
    /*foldMinus(foldPlus(foldMinus(foldPlus(foldNeg(foldTimes(b,foldPower(x1,Number(2)))),
      // 2 b x1 x2
      foldTimes(Number(2), foldTimes(b,foldTimes(x1,x2)))
      // b x2^2
    ),foldTimes(b,foldPower(x2,Number(2)))
    ),foldTimes(Number(2),foldTimes(a,foldTimes(x1,y1)))
    ),foldTimes(Number(2),foldTimes(a,foldTimes(x2,y1)))
    )*/

  }

  def unzipConsecutive(tuples: List[(CoasterXParser.Section, ((Term, Term), (Term, Term)), Formula)]):(List[TPoint], List[Section], Formula) = {
    tuples match {
      case Nil => (Nil, Nil, True)
      case (sec,(start,end), fml)::Nil =>
        (start :: end :: Nil, sec :: Nil, fml)
      case (sec,(start,end),fml)::rest =>
        val (points, secs,fmls) = unzipConsecutive(rest)
        (start :: points, sec :: secs, And(fml,fmls))
    }
  }

  // Adjust y-coordinates such that all adjacent track segments are tangent to each other, while leaving x-coordinates alone
  // Coasters exported from CoasterX typically satisfy this property modulo floatiness, but it becomes slightly false due to rounding.
  // This should never be a "big" change in terms of magnitude, but can be a huge change in the complexity of the term.
  // There are a few different approaches to manage the size of the terms.
  // The main difficulty arises from irrational points lying on circles.
  // The oldly-implemented approach is to leave the (rational) endpoints and beginning slope of an arc fixed, from
  // which nasty math (derived by Mathematica) derives an often-irrational point for the center of the circle.
  // However this also makes the end slope nasty, so the current algorithm gives up on making the slopes on a track
  // totally continuous here. The current approach could be incrementally improved by simplifying some the math.
  // For a more serious improvement (i.e. getting full tangency), now trying to to introduce
  // auxilliary variables standing for the new start/end coordinates for track sections, replacing exponential explosion
  // in term size with linear increase in variable count.
  // With a little luck, the increase in variables should not mean a big blowup in the number of variables seen by any one
  // QE call.
  def alignFile(file:File):(File,Formula) = {
    val (points, segments, v0, tent) = file
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive(nonemptySegs,points)
    val alignedBounds = alignZipped(withBounds,None,1)
    val (pointss, segmentss, fml) = unzipConsecutive(alignedBounds)
    ((pointss, segments.head :: segmentss, v0, tent),fml)
  }
  /* x'  =  dx * v,  y' = dy * v,
v'  =  -dy
dx' =  -dy*v/r,
dy' =  dx*v/r,*/

}
