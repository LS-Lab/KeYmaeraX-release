package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.{TPoint => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXSpec._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.NoProofTermProvable

/*
* Proves that CoasterX models meet their specs, by composing component proofs
* @TODO: Generate loop invariant
* @TODO: Split into branches
* @TODO: Function returning provable, with proof repeats
* @TODO: Function returning provable, with proof reuse
* @TODO: Function returning tactic with proof repeats
* @TODO: Function returning tactic with proof reuse
* */
object CoasterXProver {
  def interpret(e:BelleExpr, pr:Provable):Provable = {
    SequentialInterpreter()(e, BelleProvable(NoProofTermProvable(pr))) match {
      case BelleProvable(result,_) => result.underlyingProvable
    }
  }

  def invariant(align:(File,Formula)):Formula = {
    val (aligned@(points, segments, v0, _), segmentDefs) = align
    val nonemptySegs = segments.filter(!segmentEmpty(_))
    val withBounds = zipConsecutive(nonemptySegs, points)
    val ode = withBounds.map(segmentOde).reduceRight[Program]({ case (x, y) => Choice(x, y) })
    val energyConserved = "v^2 + 2*y = v0^2 + 2*y0".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    And(globalPost, withBounds.map(segmentPost).reduceRight[Formula] { case (x, y) => And(x, y) })
  }

  //@TODO: Add stuff from vector proof
  def quad1Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):BelleExpr = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    val ECirc:Formula = s"v^2=($v0)^2+2*($y0)-2*y&(($cx)-x)^2+(($cy)-y)^2=($r)^2".asFormula
    val xLim:Formula = s"x<=($cx)".asFormula
    val yLim:Formula = s"y<=($yEnd)".asFormula
    val cyLim:Formula = s"($cy) < ($yEnd)".asFormula
    val dGDefined:Formula = s"2*v*($r)!=0".asFormula
    val e:BelleExpr =
      normalize &
        dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)) &
        dC(s"dy=(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)) &
        dC(ECirc)('R) <(nil, dI()(1)) &
        dC(xLim)('R) <(nil, dW(1) & QE) &
        dC(cyLim)('R) <(nil, dW(1) & QE) &
        dC(yLim)('R) <(nil, dW(1) & QE) &
        dC("v>0".asFormula)('R) <(nil,
          dC(dGDefined)(1) <(
            dG(AtomicODE(DifferentialSymbol(Variable("a")), s"((($cx)-x)/(2*v*($r))*a+0".asTerm), Some("a^2*v=1".asFormula))(1) &
            existsR("(1/v)^(1/2)".asTerm)(1) & dI()(1),
            ODE(1)
          )
        )
    e
  }

  //@TODO: Add stuff from vector proof
  def quad2Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):BelleExpr = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)) &
    dC(s"dy=(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)) &
    dC(s"(($cx)-x)^2+(($cy-y)^2=r()^2".asFormula)(1) <(nil, dI()(1)) &
    dC(s"($cx)<=x".asFormula)(1) <(nil,
      dC(s"2*($cy-y)*($r)!=0".asFormula)(1) <(nil, ODE) &
      dG(s"a' = ((($cx)-x)*v/(2*(($cy)-y)*($r)))*a + 0".asDifferentialProgram, Some(s"a^2*(($cy)-y) = -1".asFormula))(1) &
      existsR(s"(-1/(($cy)-y))^(1/2)".asTerm)(1) &
      dW(1) & QE
    ) &
    dC(s"-($r) < ($cx)-x&($cx)-x < ($r)".asFormula)(1) <(dW(1) & QE, dW(1) & QE)
  }
  
  def quad3Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):BelleExpr = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)) &
    dC(s"dy=(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)) &
    dC(s"v^2=($v0)^2+2*($y0)-2*y".asFormula)(1)  <(nil, dI()(1)) &
    dC(s"v>0".asFormula)(1)  <(nil, ODE(1)) ;
    dC(s"y < ($cy)".asFormula)(1)  <(nil, dI()(1))
  }
  
  def quad4Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):BelleExpr = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    dC(s"dx=-(y-cy())/r()".asFormula)(1)  <(nil, ODE(1)) &
    dC(s"dy=(x-cx())/r()".asFormula)( 1)  <(nil, ODE(1)) &
    dC(s"cx()<=x".asFormula)(1)  <(nil, ODE(1)) &
    dC(s"v^2=v0()^2+2*y0()-2*y".asFormula)(1) <(nil, ODE(1)) &
    dC(s"(cx()-x)^2+(cy()-y)^2=r()^2".asFormula)(1) <(nil, ODE(1)) &
    dC(s"y < cy()".asFormula)(1) <(nil,
      dC(s"2*(y-cy())*r()!=0".asFormula)(1)  <(
      dG(s"{a'=(cx()-x)*v/(2*(y-cy())*r())*a+0}".asDifferentialProgram, Some("a^2*(y-cy())=-1".asFormula))(1) &
        existsR("(-1/(y-cy()))^(1/2)".asTerm)(1) &
        ODE(1),
      ODE(1)
    )
    ) ;
    dC(s"v>0".asFormula)(1)  <(nil,
      dC(s"2*v*r()!=0".asFormula)(1)  <(
      dG(s"a'=(x-cx())/(2*v*r())*a+0}".asDifferentialProgram, Some("v>0".asFormula))(1) &
        existsR("(1/v)^(1/2)".asTerm)(1) &
        dC("a^2*v=1".asFormula)(1)  <(
          ODE(1),
          ODE(1)
        ),
      ODE(1)
      )
    )
  }
  
  def sectionTactic(pr: Provable, p1: TPoint, p2: TPoint, v0:Number, section: Section):BelleExpr = {
    section match {
      case ArcSection(Some(ArcParam(bl,tr,theta1,deltaTheta)),Some(grad)) =>
        (theta1.value < -90, theta1.value < 0, theta1.value < 90) match {
          case (true, _, _) => quad3Tactic(pr, p1, p2, bl, tr, v0, theta1, deltaTheta) // Quadrant 3
          case (_, true, _) => quad4Tactic(pr, p1, p2, bl, tr, v0, theta1, deltaTheta) // Quadrant 4
          case (_, _, true) => quad1Tactic(pr, p1, p2, bl, tr, v0, theta1, deltaTheta) // Quadrant 1
          case _ => quad2Tactic(pr, p1, p2, bl, tr, theta1, v0, deltaTheta) /// Quadrant 2
        }
      case LineSection(Some(LineParam(bl,tr)), Some(grad)) =>
        master()
      case _ => ???
    }
  }

  def provePosts(pr:Provable, fml:Formula, p1: TPoint, p2: TPoint, section: Section, v: Number, i: Int, j:Int):BelleExpr = {
    val thisE =
      if(i == j) {
        sectionTactic(pr, p1, p2, v, section)
      } else {
        dW(1) & QE
      }
    fml match {
      case And(p,q) => andR(1) <(thisE, provePosts(pr, q, p1, p2, section, v, i, j+1))
      case _ => thisE
    }
  }

  def componentTactic(pr:Provable, p1: TPoint, p2: TPoint, section: Section, v: Number, i: Int):BelleExpr = {
    sectionTactic(pr, p1, p2, v, section) & dW(1) & QE
  /*  val globalPost = ???
    val componentPost = provePosts(pr, pr.conclusion.succ.head, p1, p2, section, v, i, 0)
    andR(1) <(globalPost, componentPost)*/
  }

  def componentTactics(pr:Provable, points:List[TPoint], segments:List[Section], v:Number, i:Int):List[BelleExpr] = {
    (points, segments) match {
      case (_ :: Nil, Nil) => Nil
      case (p1 :: p2 :: ps, s1 :: ss) =>
        componentTactic(pr, p1, p2, s1, v, i) :: componentTactics(pr, p2::ps, ss, v, i+1)
      case _ => ???
    }
  }

  def mapChoices(es:List[BelleExpr]):BelleExpr = {
    es match {
      case Nil => nil
      case (e :: Nil) => e
      case (e1 :: ess) =>  choiceb(1) & andR(1) <(e1, mapChoices(ess))
    }
  }

  def apply(fileName:String):Provable = {
    val parsed = CoasterXParser.parseFile(fileName).get
    val align@(aligned@(points, segments, v0, _), segmentDefs) = prepareFile(parsed)
    val spec = fromAligned(align)
    val pr = Provable.startProof(spec)
    val pr1 = interpret(implyR(1), pr)
    val pr2 = interpret(loop(invariant(align))(1) <(QE, QE, nil), pr1)
    val es = componentTactics(pr2, points, segments.tail, v0, 0)
    val e = mapChoices(es)
    val prEnd = interpret(e, pr2)
    assert(prEnd.isProved, "CoasterX model not proved")
    prEnd
  }
}
