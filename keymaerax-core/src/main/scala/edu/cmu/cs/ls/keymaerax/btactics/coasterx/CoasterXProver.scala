package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.{TPoint => _, _}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{dW, _}
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
    val y0 = points.head._2
    val energyConserved = s"v^2 + 2*y = ($v0)^2 + 2*($y0)".asFormula
    val globalPost = And("v > 0".asFormula, energyConserved)
    val fml = And(globalPost, withBounds.map(segmentPost).reduceRight[Formula] { case (x, y) => And(x, y) })
    fml
  }

  //@TODO: Add stuff from vector proof
  def quad1Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):Provable = {
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
    interpret(e,pr)
  }

  //@TODO: Add stuff from vector proof
  def quad2Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):Provable = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    val e =
      dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"dy=(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"(($cx)-x)^2+(($cy-y)^2=($r)^2".asFormula)(1) <(nil, dI()(1)) &
      dC(s"($cx)<=x".asFormula)(1) <(nil,
        dC(s"2*($cy-y)*($r)!=0".asFormula)(1) <(nil, ODE) &
        dG(s"a' = ((($cx)-x)*v/(2*(($cy)-y)*($r)))*a + 0".asDifferentialProgram, Some(s"a^2*(($cy)-y) = -1".asFormula))(1) &
        existsR(s"(-1/(($cy)-y))^(1/2)".asTerm)(1) &
        dW(1) & QE
      ) &
      dC(s"-($r) < ($cx)-x&($cx)-x < ($r)".asFormula)(1) <(dW(1) & QE, dW(1) & QE)
    interpret(e,pr)
  }
  
  def quad3Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):Provable = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    val e =
      dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"dy=(x-($cx))/($r)".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"v^2=($v0)^2+2*($y0)-2*y".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"v>0".asFormula)(1)  <(nil, ODE(1)) ;
      dC(s"y < ($cy)".asFormula)(1)  <(nil, dI()(1))
    interpret(e, pr)
  }
  
  def quad4Tactic(pr: Provable, p1: TPoint, p2: TPoint, bl: TPoint, tr: TPoint, v0: Number, theta1: Number, deltaTheta: Number):Provable = {
    val cx = foldDivide(foldPlus(tr._1,bl._1),Number(2))
    val cy = foldDivide(foldPlus(tr._2,bl._2),Number(2))
    val r = foldDivide(foldMinus(tr._1,bl._1),Number(2))
    val y0 = p1._2
    val yEnd = p2._2
    //val pr0 = interpret(implyR(1), pr)
    val pr1 = interpret(dC(s"dx=-(y-($cy))/($r)".asFormula)(1)  <(nil, dI()(1)), pr)
    val pr2 = interpret(dC(s"dy=(x-($cx))/($r)".asFormula)( 1)  <(nil, ODE(1)), pr1)
    val pr3 = interpret(dC(s"($cx)<=x".asFormula)(1)  <(nil, ODE(1)), pr2)
    val pr4 = interpret(dC(s"v^2=($v0)^2+2*($y0)-2*y".asFormula)(1) <(nil, ODE(1)), pr3)
    val pr5 = interpret(dC(s"(($cx)-x)^2+(($cy)-y)^2=($r)^2".asFormula)(1) <(nil, ODE(1)), pr4)
    val pr6 = interpret(dC(s"y < ($cy)".asFormula)(1) <(nil,
      dC(s"2*(y-($cy))*($r)!=0".asFormula)(1)  <(
        dG(s"{a'=(($cx)-x)*v/(2*(y-($cy))*($r))*a+0}".asDifferentialProgram, Some(s"a^2*(y-($cy))=-1".asFormula))(1) &
          existsR(s"(-1/(y-($cy)))^(1/2)".asTerm)(1) &
          ODE(1),
        ODE(1)
      )
    ), pr5)
    val pr7 = interpret(dC(s"v>0".asFormula)(1)  <(nil,
      dC(s"2*v*($r)!=0".asFormula)(1)  <(
        dG(s"{a'=(x-($cx))/(2*v*($r))*a+0}".asDifferentialProgram, Some("v>0".asFormula))(1) &
          existsR("(1/v)^(1/2)".asTerm)(1) &
          dC("a^2*v=1".asFormula)(1)  <(
            ODE(1),
            ODE(1)
          ),
        ODE(1)
      )
    ), pr6)
    pr7
  }
  
  def sectionTactic(pr: Provable, p1: TPoint, p2: TPoint, v0:Number, section: Section):Provable = {
    section match {
      case ArcSection(Some(ArcParam(bl,tr,theta1,deltaTheta)),Some(grad)) => {
        val pr1 =
          ((theta1.value < -90, theta1.value < 0, theta1.value < 90) match {
            case (true, _, _) => quad3Tactic(pr, p1, p2, bl, tr, v0, theta1, deltaTheta) // Quadrant 3
            case (_, true, _) => quad4Tactic(pr, p1, p2, bl, tr, v0, theta1, deltaTheta) // Quadrant 4
            case (_, _, true) => quad1Tactic(pr, p1, p2, bl, tr, v0, theta1, deltaTheta) // Quadrant 1
            case _ => quad2Tactic(pr, p1, p2, bl, tr, theta1, v0, deltaTheta) /// Quadrant 2
          })
        interpret(dW(1) & QE, pr1)
      }
      case LineSection(Some(LineParam(bl,tr)), Some(grad)) =>
        interpret(master(), pr)
      case _ => ???
    }
  }

  def provePosts(pr:Provable, fml:Formula, p1: TPoint, p2: TPoint, section: Section, v: Number, i: Int, j:Int):BelleExpr = {
    val thisE =
      if(i == j) {
        sectionTactic(pr, p1, p2, v, section)
        //@TODO: fix
        nil
      } else {
        dW(1) & QE
      }
    fml match {
      case And(p,q) => andR(1) <(thisE, provePosts(pr, q, p1, p2, section, v, i, j+1))
      case _ => thisE
    }
  }

  def componentTactic(pr:Provable, p1: TPoint, p2: TPoint, section: Section, v: Number, i: Int):Provable = {
    sectionTactic(pr, p1, p2, v, section)
  /*  val globalPost = ???
    val componentPost = provePosts(pr, pr.conclusion.succ.head, p1, p2, section, v, i, 0)
    andR(1) <(globalPost, componentPost)*/
  }

  def proveAllComponents(global:Provable, locals: List[Provable], points: List[(Term, Term)], segments: List[Section], v: Number, i: Int):Provable = {
    (points, segments, locals) match {
      case (p1 :: p2 :: Nil, s1 :: Nil, pr :: Nil) => componentTactic(pr, p1, p2, s1, v, i)
      case (p1 :: p2 :: ps, s1 :: ss, pr :: prs) =>
        val sg = componentTactic(pr, p1, p2, s1, v, i)
        proveAllComponents(global(sg, 0), prs, p2::ps, ss, v, i+1)
      case _ => ???
    }
  }

  def splitComponents(pr:Provable,i:Int = 0):(Provable, List[Provable]) = {
    pr.subgoals(i).succ.head match {
      case (Box(Choice(_,_), _)) =>
        val pr1 = interpret(choiceb(1) & andR(1), pr)
        val sg = Provable.startProof(pr1.subgoals(i))
        val (global, locals) = splitComponents(pr1, i+1)
        (global, sg::locals)
      case  _ =>
        (pr, Provable.startProof(pr.subgoals.last) :: Nil)
//      case Nil => ???
    }
  }

  def apply(fileName:String):Provable = {
    val parsed = CoasterXParser.parseFile(fileName).get
    val align@(aligned@(points, segments, v0, _), segmentDefs) = prepareFile(parsed)
    val spec = fromAligned(align)
    val pr = Provable.startProof(spec)
    val pr1 = interpret(implyR(1), pr)
    val pr2 = interpret(loop(invariant(align))(1), pr1)
    val pr3 = interpret(nil <(QE, nil, nil), pr2)
    val pr4 = interpret(nil <(QE, nil), pr3)
    val (globalPr, localPrs) = splitComponents(pr4)
      //mapChoices(es)
    val prEnd = proveAllComponents(globalPr, localPrs, points, segments.tail, v0, 0)
    //val prs = localPrs.zip(es)
    //val prEnd = interpret(e, pr4)
    assert(prEnd.isProved, "CoasterX model not proved")
    prEnd
  }
}
