import java.io.File

import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.tactics.ProofNode.ProofStep
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import testHelper.ParserFactory._
import edu.cmu.cs.ls.keymaerax.tactics.ModelPlex.{modelplex, modelplexInPlace, diamondModelplexTestT,
  locateT, optimizationOne, modelplexControllerMonitorTrafo, controllerMonitorT, modelMonitorT}
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.diamondDiffSolve2DT
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{locateSucc,lastSucc,onBranch,lastAnte}
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.instantiateT
import TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import scala.collection.immutable
import scala.collection.mutable.ListBuffer
import scala.language.postfixOps

/**
 * Created by smitsch on 3/8/15.
 * @author Stefan Mitsch
 */
class ModelplexTacticTests extends testHelper.TacticTestSuite {

  def monitorSize(f: Formula): Int = {
    var numOperators = 0
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case _ => println(e); numOperators += 1; Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case _: Variable => Left(None)
        case Number(_) => Left(None)
        case FuncOf(_, _) => Left(None)
        case Nothing => Left(None)
        case _ => println(e); numOperators += 1; Left(None)
      }
    }, f)
    numOperators
  }

  def numSteps(n: ProofNode): Int = if (n.children.nonEmpty) n.children.map(numSteps).min else 0
  def numSteps(s: ProofStep): Int = if (s.subgoals.nonEmpty) 1 + s.subgoals.map(numSteps).sum else 1

  def numBranches(n: ProofNode): Int = if (n.children.nonEmpty) n.children.map(numBranches).min else 0
  def numBranches(s: ProofStep): Int = if (s.subgoals.nonEmpty) s.subgoals.map(numBranches).sum else 1

  def report(result: Formula, proof: ProofNode, name: String) = {
    println(s"$name monitor size: " + monitorSize(result))
    println("Number of proof steps: " + numSteps(proof))
    println("Number of branches (open/all): " + proof.openGoals().size + "/" + numBranches(proof))
  }

  "Watertank modelplex" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
    val tactic = locateSucc(modelplex)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 2
    result.openGoals()(0).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula)
    result.openGoals()(0).sequent.succ should contain only "-1<=fpost_0() & fpost_0()<=(m-x)/ep".asFormula
    result.openGoals()(1).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula, "-1<=fpost_0()".asFormula, "fpost_0()<=(m-x)/ep".asFormula)
    result.openGoals()(1).sequent.succ should contain only "tpost_0()=0 & (fpost()=fpost_0() & xpost()=x & tpost()=tpost_0())".asFormula
  }

  it should "simple: find correct controller monitor by updateCalculus implicationally" in {
    import TactixLibrary.chase
    import TactixLibrary.proveBy
    import TactixLibrary.useAt
    import scala.collection._

    val in = //getClass.getResourceAsStream("examples/casestudies/modelplex/simple.key")
      getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model, Variable("f"), Variable("l"), Variable("c"))

    // child position needed to nibble off the <-> from the chase (maybe ought to be in chase itself???)
    def posChild(pos: Position): Position = if (pos.isAnte)
      AntePosition(pos.index, pos.inExpr.child)
    else
      SuccPosition(pos.index, pos.inExpr.child)

    // prepend position where uncontrol/modelPlex chase was started off in the first place
    def prependPos(pos: Position, prep: PosInExpr): Position = if (pos.isAnte)
      AntePosition(pos.index, prep.append(pos.inExpr))
    else
      SuccPosition(pos.index, prep.append(pos.inExpr))

    // mutable state per call
    def modelPlex(loopStack: mutable.ListBuffer[Position]): PositionTactic = {
      def uncontrol: PositionTactic = chase(3, 3, e => e match {
        // no equational assignments
        case Box(Assign(_, _), _) => "[:=] assign" :: "[:=] assign update" :: Nil
        case Diamond(Assign(_, _), _) => "<:=> assign" :: "<:=> assign update" :: Nil
        // remove loops
        case Diamond(Loop(_), _) => "<*> stuck" :: Nil //"<*> approx" :: Nil
        // remove ODEs for controller monitor
        case Diamond(ODESystem(_, _), _) => "<'> stuck" :: Nil
        case _ => AxiomIndex.axiomsFor(e)
      },
        (ax, pos) => pr => {
          println("uncontrol using " + ax + " at " + pos)
          ax match {
            // log loop applications
            case "<*> stuck" => posChild(pos) +=: loopStack  // this means prepend pos to stack
              println("Stuck with <*> at stack " + loopStack)
            case "<'> stuck" => posChild(pos) +=: loopStack
              println("Stuck with <'> at stack " + loopStack)
//            case "<:=> assign update" => pos +=: loopStack
//              println("Stuck with <:=> at stack " + loopStack)
            case _ =>
          };
          pr
        }
      )

      new PositionTactic("ModelPlex") {
        override def applies(s: Sequent, p: Position): Boolean = true
        override def apply(p: Position): Tactic =
          (debugAtT("huhu") & uncontrol & debugAtT("uncontrolled") &
            // retroactively handle postponed loops in inverse order, so inside-out
            Tactics.ignorePosition(Tactics.foldLazyLeft(loopStack.toList.map(prependPos(_,p.inExpr)))(
              (debugAtT("one loop") & (/*useAt("<:=> assign") |*/ useAt("<*> approx") | useAt("DX diamond differential skip")) & debugAtT("delooped")) & new PositionTactic("lazy modelPlex recursor") {
                override def applies(s: Sequent, p: Position): Boolean = true
                //@note indirect/postponed/lazy call to modelPlex is required to prevent infinite recursion in tactic construction
                override def apply(p: Position): Tactic = modelPlex(new ListBuffer())(p)
              }
            ))) (p)

      }
    }

    val result = proveBy(modelplexInput, modelPlex(new ListBuffer[Position]())(SuccPosition(0, PosInExpr(1 :: Nil))))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "true -> ???".asFormula
  }

  it should "find correct controller monitor by updateCalculus implicationally" in {
    import TactixLibrary.chase
    import TactixLibrary.proveBy

    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model, Variable("f"), Variable("l"), Variable("c"))

    def controllerMonitor: PositionTactic = chase(3,3, e => e match {
      // no equational assignments
      case Box(Assign(_,_),_) => "[:=] assign" :: "[:=] assign update" :: Nil
      case Diamond(Assign(_,_),_) => "<:=> assign" :: "<:=> assign update" :: Nil
      // remove loops
      case Diamond(Loop(_), _) => "<*> approx" :: Nil
      // remove ODEs for controller monitor
      case Diamond(ODESystem(_, _), _) => "DX diamond differential skip" :: Nil
      case _ => AxiomIndex.axiomsFor(e)
    }
    )

    val result = proveBy(modelplexInput, controllerMonitor(SuccPosition(0, PosInExpr(1 :: Nil))))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "true -> ".asFormula
  }

  ignore should "find correct model monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val tactic = locateSucc(modelplex)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 2
    result.openGoals()(0).sequent.ante should contain only "0<=x & x<=m & 0<ep".asFormula
    result.openGoals()(0).sequent.succ should contain only "-1<=f & f<=(m-x)/ep".asFormula
    result.openGoals()(1).sequent.ante should contain only ("0<=x & x<=m & 0<ep".asFormula, "-1<=f & f<=(m-x)/ep".asFormula)
    result.openGoals()(1).sequent.succ should contain only "f_post()=f & x_post()=x & t_post()=0".asFormula
  }

  "Watertank modelplex in place" should "find correct controller monitor condition with Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with Modelplex diamond test
//    val expected = "-1<=f & f<=(m-x)/ep & (-1<=f & f<=(m-x)/ep -> f_post()=f & x_post()=x & t_post()=0)".asFormula

    // with ordinary diamond test
    val expected = "-1<=fpost_0()&fpost_0()<=(m-x)/ep&(fpost()=fpost_0()&xpost()=x&tpost()=0)".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=x & x<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank controller")
  }

  it should "find correct controller monitor condition from model file" in {
    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model, Variable("f"), Variable("l"), Variable("c"))

    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(modelplexInput))))

    val expected = "-1<=fpost_0()&fpost_0()<=(m-l)/ep&(cpost_0()=0&(cpost_0()<=ep&l>=0&lpost()=l&fpost()=fpost_0()&cpost()=cpost_0()))".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "true".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank controller")
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
    val tactic = modelplexInPlace(useOptOne=false)(controllerMonitorT)(SuccPosition(0)) & optimizationOne()(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = "-1<=fpost_0()&fpost_0()<=(m-x)/ep&(fpost()=fpost_0()&xpost()=x&tpost()=0)".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=x & x<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank controller")
  }

  it should "find correct model monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val tactic = modelplexInPlace(useOptOne=true, Some(Variable("c", Some(1), Real)))(modelMonitorT)(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with diamond test, after local QE
    val expected = "-1<=fpost_0()&fpost_0()<=(m-l)/ep&(cpost_0()=0&(ep=cpost()&(l=0&(tpost_0()=0&(cpost_0()=ep&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=0)|(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=0))))|tpost_0()>0&(cpost_0()=-1*tpost_0()+ep&(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()))))|l>0&(tpost_0()=0&(cpost_0()=ep&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=l))))|tpost_0()>0&(cpost_0()=-1*tpost_0()+ep&(-1*tpost_0()^-1*l<=fpost_0()&fpost_0() < 0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l))))))|ep>cpost()&(l=0&(tpost_0()=0&(cpost_0()=cpost()&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=0)|(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=0))))|tpost_0()>0&(cpost_0()=cpost()+-1*tpost_0()&(fpost_0()=0&(fpost()=0&lpost()=0)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()))))|l>0&(tpost_0()=0&(cpost_0()=cpost()&(fpost_0() < 0&(fpost()=fpost_0()&lpost()=l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=l))))|tpost_0()>0&(cpost_0()=cpost()+-1*tpost_0()&(-1*tpost_0()^-1*l<=fpost_0()&fpost_0() < 0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l)|(fpost_0()=0&(fpost()=0&lpost()=l)|fpost_0()>0&(fpost()=fpost_0()&lpost()=fpost_0()*tpost_0()+l))))))))".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=l & l<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank model")
  }

  it should "find correct model monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val tactic = modelplexInPlace(useOptOne=false)(modelMonitorT)(SuccPosition(0)) &
      (optimizationOne()(SuccPosition(0))*)
    val result = helper.runTactic(tactic, new RootNode(s))

    // with diamond test, after local QE
//    val expected = "-1<=f&f<=(m-l)/ep&(f()=f&(c_1=0&((c_post=c_1&((f_post<0&((ep=c_post&(f()=f_post&(l>=c_1*f()+-1*ep*f()&l_post=l+-1*c_1*f()+c_post*f())))|(ep>c_post&(f()=f_post&(l>=c_1*f()+-1*c_post*f()&l_post=l+-1*c_1*f()+c_post*f())))))|((f_post=0&(ep>=c_post&(f()=0&(l>=0&l_post=l))))|(f_post>0&(ep>=c_1&(f()=f_post&(l>=c_1*f()+-1*c_post*f()&l_post=l+-1*c_1*f()+c_post*f())))))))|(c_post>c_1&((f_post<0&(ep>=c_post&(f()=f_post&(l>=c_1*f()+-1*c_post*f()&l_post=l+-1*c_1*f()+c_post*f()))))|((f_post=0&(ep>=c_post&(f()=0&(l>=0&l_post=l))))|(f_post>0&(ep>=c_post&(f()=f_post&(l>=0&l_post=l+-1*c_1*f()+c_post*f()))))))))))".asFormula
    val expected = "-1<=f&f<=(m-l)/ep&(f()=f&(c_1=0&(t>=0&(((c_1<ep&(t<0|((t=0&l>=0)|(0<t&t<=-1*c_1+ep&(l>=0&f()>=-1*l*t^-1)))))|((c_1=ep&(t<0|(t=0&l>=0)))|(c_1>ep&t<0)))&(f_post=f()&l_post=t*f()+l&c_post=1*t+c_1)))))".asFormula

  result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=l & l<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank model")
  }

  ignore should "find model monitor condition when manually guided in place" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val p = SuccPosition(0)
    val tactic = debugT("Start") &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondNDetAssign :: Nil)(p) &
      optimizationOne()(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondTestT :: Nil)(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondTestT :: Nil)(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondAssignEqualT :: Nil)(p) &
      locateT(v2vAssignT :: Nil)(p) &
      locateT(diamondDiffSolve2DT :: Nil)(p) &
      (locateT(substitutionDiamondAssignT :: Nil)(p)*)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only
      ("0<=l & l<=m & 0<ep -> -1<=f&f<=(m-l)/ep & " +
        "(f()=f & !\\forall c_1.(c_1=0 -> !\\exists t.(t>=0 & " +
          "(\\forall s.(0<=s&s<=t -> 0<=s*f()+l&1*s+c_1<=ep) & " +
          "(f_post=f()&l_post=t*f()+l&c_post=1*t+c_1)))))").asFormula
  }

  ignore should "find model monitor condition when manually guided" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val p = SuccPosition(0)
    val tactic = debugT("Start") & locateSucc(ImplyRightT) &
      locateSucc(diamondSeqT) & locateSucc(diamondNDetAssign) & locateSucc(optimizationOne()) &
      locateSucc(diamondSeqT) & locateSucc(diamondModelplexTestT) & locateSucc(AndRightT) && (
        NilT,
        locateSucc(ImplyRightT) & locateSucc(diamondSeqT) & locateSucc(diamondModelplexTestT) & locateSucc(AndRightT) && (
          NilT,
          locateSucc(ImplyRightT) & locateSucc(diamondSeqT) & locateSucc(diamondAssignEqualT) &
            locateSucc(NotRightT) & lastAnte(optimizationOne()) &
            lastAnte(ImplyLeftT) && (
              NilT,
              lastAnte(NotLeftT) & locateSucc(v2vAssignT) & locateSucc(diamondDiffSolve2DT) & locateSucc(optimizationOne()) &
              locateSucc(AndRightT) && (
                NilT,
                locateSucc(AndRightT) && (
                  locateSucc(skolemizeT) & locateSucc(ImplyRightT) & (locateSucc(substitutionDiamondAssignT)*),
                  locateSucc(substitutionDiamondAssignT)*
                  )
                )
            )
          )
      ) & (locateAnte(eqLeft(exhaustive = true) & hideT)*)

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 6
    result.openGoals()(0).sequent.ante should contain only "0<=l & l<=m & 0<ep".asFormula
    result.openGoals()(0).sequent.succ should contain only "-1<=f & f<=(m-l)/ep".asFormula
    result.openGoals()(1).sequent.ante should contain only ("0<=l & l<=m & 0<ep".asFormula, "-1<=f & f<=(m-l)/ep".asFormula)
    result.openGoals()(1).sequent.succ should contain only "f()=f".asFormula
    result.openGoals()(2).sequent.ante should contain only ("0<=l & l<=m & 0<ep".asFormula, "-1<=f & f<=(m-l)/ep".asFormula, "f()=f".asFormula)
    result.openGoals()(2).sequent.succ should contain only "c_1=0".asFormula
    result.openGoals()(3).sequent.ante should contain only ("0<=l & l<=m & 0<ep".asFormula, "-1<=f & f<=(m-l)/ep".asFormula, "f()=f".asFormula)
    result.openGoals()(3).sequent.succ should contain only "t>=0".asFormula
    result.openGoals()(4).sequent.ante should contain only ("0<=l & l<=m & 0<ep".asFormula, "-1<=f & f<=(m-l)/ep".asFormula, "0<=s&s<=t".asFormula)
    result.openGoals()(4).sequent.succ should contain only "0<=s*f+l & 1*s+c_1<=ep".asFormula
    result.openGoals()(5).sequent.ante should contain only ("0<=l & l<=m & 0<ep".asFormula, "-1<=f & f<=(m-l)/ep".asFormula)
    result.openGoals()(5).sequent.succ should contain only "f_post=f & l_post=t*f+l & c_post=1*t+c_1".asFormula
  }

  ignore should "Local lane control modelplex find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key"))
    val tactic = locateSucc(modelplex)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 22
    // TODO check (are same as 13 above except that several goals are duplicated)
  }

  ignore should "work manually" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key"))

    def sp(i: Int) = new SuccPosition(i)

    def stayStoppedTactic(where: Int) = AndRightT(sp(where)) && (
      LabelBranch("ContinueBrakePLast"),
      ImplyRightT(sp(where)) & lastSucc(substitutionDiamondAssignT) & lastSucc(substitutionDiamondAssignT) & LabelBranch("ContinueBrakePMid"))

    def brakeTactic(where: Int) = debugT(s"Brake $where") & AndRightT(sp(where)) && (
      LabelBranch("ContinueAccPLast"),
      ImplyRightT(sp(where)) & lastSucc(substitutionDiamondAssignT) & LabelBranch("ContinueAccPMid"))

    def accTactic(where: Int) = debugT(s"Acc $where") & AndRightT(sp(where)) && (
      NilT,
      ImplyRightT(sp(where)) & lastSucc(substitutionDiamondAssignT))

    val tactic = ImplyRightT(sp(0)) &
      diamondSeqT(sp(0)) & diamondNDetAssign(sp(0)) & instantiateT(sp(0)) &
      diamondSeqT(sp(0)) & diamondModelplexTestT(sp(0)) & AndRightT(sp(0)) && (NilT,
      ImplyRightT(sp(0)) & diamondSeqT(sp(0)) & diamondChoiceT(sp(0)) & OrRightT(sp(0)) &
        // first: accelerate
      diamondSeqT(sp(0)) /* now moved to end */ & lastSucc(diamondModelplexTestT) & // continue branch at 1.1
      // second: stay stopped
      diamondChoiceT(sp(0)) /* now moved to end */ & lastSucc(OrRightT) &
      diamondSeqT(sp(1)) /* now moved to end */ & lastSucc(diamondModelplexTestT) &
      // third: brake
      diamondSeqT(sp(1)) /* now moved to end */ & lastSucc(diamondNDetAssign) & lastSucc(instantiateT) & lastSucc(diamondModelplexTestT) &
      // 1.1
      AndRightT(sp(0)) && (stayStoppedTactic(1) & onBranch(
        ("ContinueBrakePLast", brakeTactic(2)),
        ("ContinueBrakePMid", brakeTactic(1))),
        // accelerate
        ImplyRightT(sp(0)) /* now moved to end */ & lastSucc(diamondSeqT) & lastSucc(diamondNDetAssign) & lastSucc(instantiateT) & lastSucc(diamondModelplexTestT) &
        // stay stopped
        stayStoppedTactic(0) & onBranch(
          ("ContinueBrakePLast", brakeTactic(1) & onBranch(
            ("ContinueAccPLast", accTactic(2)),
            ("ContinueAccPMid", accTactic(1))
          )),
          ("ContinueBrakePMid", brakeTactic(0) & onBranch(
            ("ContinueAccPLast", accTactic(1)),
            ("ContinueAccPMid", accTactic(0))
          ))
        )
        )
      ) & (locateAnte(eqLeft(exhaustive = true))*)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 13
  }

  "Local lane control modelplex in place" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = ("-B<=alpost_0() & alpost_0()<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=afpost_0()&afpost_0()<=A&(xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0))) | " +
      "((vf=0&(xfpost()=xf&vfpost()=vf&afpost()=0&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0)) | " +
      "(-B<=afpost_0()&afpost_0()<=-b&(xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Local lane controller ")
  }

  ignore should "find correct controller monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key"))
    val tactic = modelplexInPlace(useOptOne=false)(controllerMonitorT)(SuccPosition(0)) &
      (optimizationOne()(SuccPosition(0))*)
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = ("-B<=alpost_0() & alpost_0()<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=afpost_0()&afpost_0()<=A&(xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0))) | " +
      "((vf=0&(xfpost()=xf&vfpost()=vf&afpost()=0&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0)) | " +
      "(-B<=afpost_0()&afpost_0()<=-b&(xfpost()=xf&vfpost()=vf&afpost()=afpost_0()&xlpost()=xl&vlpost()=vl&alpost()=alpost_0()&tpost()=0))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Local lane controller ")
  }

  "ETCS safety lemma modelplex in place" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/icfem08/safetylemma-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=false)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.succ should have size 1

    report(result.openGoals().head.sequent.succ.head, result, "ETCS controller")
  }

  "RSS passive safety modelplex in place" should "generate the correct Modelplex property from the input model" in {
    val in = getClass.getResourceAsStream("examples/casestudies/robix/passivesafetyabs.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model/*, List(Variable("a"), Variable("r"), Variable("xo"),
      Variable("yo"), Variable("t"), Variable("w"), Variable("dxo"), Variable("dyo"))*/)

    modelplexInput shouldBe  """
        true
        |  -> <dxo :=*;
        |      dyo :=*;
        |      ?dxo^2 + dyo^2 <= V()^2;
        |
        |      /* brake on current curve or remain stopped */
        |      {
        |        {a := -B; }
        |      ++{?v = 0; a := 0; w := 0; }
        |      /* or choose a new safe curve */
        |    	 ++{a :=*; ?-B <= a & a <= A;
        |
        |    	 r :=*; ?r != 0; /* do not spin */
        |    	 w :=*; ?w * r = v;
        |
        |      /* for the chosen a, w, cx, cy: worst case position of obstacles wrt. curve */
        |      xo :=*;
        |      yo :=*;
        |
        |    	 /* use that curve, if it is a safe one (admissible velocities) */
        |    	 ? abs(x-xo) > v^2/(2*B) + V()*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V()))
        |    	 | abs(y-yo) > v^2/(2*B) + V()*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V()));
        |    	 }
        |    	 };
        |
        |    	 t := 0;>(apost()=a&rpost()=r&xopost()=xo&yopost()=yo&tpost()=t&wpost()=w&dxopost()=dxo&dyopost()=dyo)
      """.stripMargin.asFormula
  }

  it should "find the correct controller monitor condition from the input model" in {
    val in = getClass.getResourceAsStream("examples/casestudies/robix/passivesafetyabs.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model/*, List(Variable("a"), Variable("r"), Variable("t"),
      Variable("dxo"), Variable("dyo"), Variable("xo"), Variable("yo"), Variable("w"))*/)

    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(modelplexInput))))

    val expectedAnte = "true".asFormula
    val expectedSucc = ("dxopost_0()^2+dyopost_0()^2<=V()^2 & (apost()=-B & rpost()=r & tpost()=0 & dxopost()=dxopost_0() & dyopost()=dyopost_0() & xopost()=xo & yopost()=yo & wpost()=w" +
      "                                       | (v=0 & (apost()=0 & rpost()=r & tpost()=0 & dxopost()=dxopost_0() & dyopost()=dyopost_0() & xopost()=xo & yopost()=yo & wpost()=0)" +
      "                                       | -B<=apost_0()&apost_0()<=A & (rpost_0()!=0 & (wpost_0()*rpost_0()=v & ((abs(x-xopost_0())>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))|abs(y-yopost_0())>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))) & (apost()=apost_0()&rpost()=rpost_0()&tpost()=0&dxopost()=dxopost_0()&dyopost()=dyopost_0()&xopost()=xopost_0()&yopost()=yopost_0()&wpost()=wpost_0()))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only expectedAnte
    result.openGoals().head.sequent.succ should contain only expectedSucc
  }

  it should "work using the command line interface" in {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/robix/passivesafety.key"
    val vars = "a,r,xo,yo,dxo,dyo,t,w"
    val outputFileName = File.createTempFile("passivesafety", ".mx").getAbsolutePath
    KeYmaeraX.main(Array("-modelplex", inputFileName, "-vars", vars, "-out", outputFileName))

    val expectedFileContent = "dxopost_0()^2+dyopost_0()^2<=V()^2&(apost()=-B&rpost()=r&xopost()=xo&yopost()=yo&dxopost()=dxopost_0()&dyopost()=dyopost_0()&tpost()=0&wpost()=w|(v=0&(apost()=0&rpost()=r&xopost()=xo&yopost()=yo&dxopost()=dxopost_0()&dyopost()=dyopost_0()&tpost()=0&wpost()=0)|-B<=apost_0()&apost_0()<=A&(rpost_0()!=0&(wpost_0()*rpost_0()=v&(((x-xopost_0()>=0->x-xopost_0()>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V())))&(x-xopost_0()<=0->xopost_0()-x>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V())))|(y-yopost_0()>=0->y-yopost_0()>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V())))&(y-yopost_0()<=0->yopost_0()-y>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))))&(apost()=apost_0()&rpost()=rpost_0()&xopost()=xopost_0()&yopost()=yopost_0()&dxopost()=dxopost_0()&dyopost()=dyopost_0()&tpost()=0&wpost()=wpost_0()))))))".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    KeYmaeraXParser(actualFileContent) shouldBe expectedFileContent
  }

  it should "work using the command line interface with abs function" in {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/robix/passivesafetyabs.key"
    val vars = "a,r,xo,yo,dxo,dyo,t,w"
    val outputFileName = File.createTempFile("passivesafetyabs", ".mx").getAbsolutePath
    KeYmaeraX.main(Array("-modelplex", inputFileName, "-vars", vars, "-out", outputFileName))

    val expectedFileContent = "dxopost_0()^2+dyopost_0()^2<=V()^2&(apost()=-B&rpost()=r&xopost()=xo&yopost()=yo&dxopost()=dxopost_0()&dyopost()=dyopost_0()&tpost()=0&wpost()=w|(v=0&(apost()=0&rpost()=r&xopost()=xo&yopost()=yo&dxopost()=dxopost_0()&dyopost()=dyopost_0()&tpost()=0&wpost()=0)|-B<=apost_0()&apost_0()<=A&(rpost_0()!=0&(wpost_0()*rpost_0()=v&((abs(x-xopost_0())>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))|abs(y-yopost_0())>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V())))&(apost()=apost_0()&rpost()=rpost_0()&xopost()=xopost_0()&yopost()=yopost_0()&dxopost()=dxopost_0()&dyopost()=dyopost_0()&tpost()=0&wpost()=wpost_0()))))))".asFormula

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    KeYmaeraXParser(actualFileContent) shouldBe expectedFileContent
  }

  "RSS passive orientation safety modelplex in place" should "extract the correct controller monitor" in {
    val in = getClass.getResourceAsStream("examples/casestudies/robix/passiveorientationsafety.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model/*, List(Variable("a"), Variable("r"),
      Variable("talpha"), Variable("odx"), Variable("ody"), Variable("ox"), Variable("oy"), Variable("dx"),
      Variable("dy"), Variable("w"), Variable("isVisible"), Variable("t"))*/)

    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(modelplexInput))))

    val expectedAnte = "true".asFormula
    val expectedSucc = "odxpost_0()^2+odypost_0()^2<=V()^2&(wpost_0()*r=v&(apost()=-b()&rpost()=r&talphapost()=talpha&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=ox&oypost()=oy&dxpost()=dx&dypost()=dy&wpost()=wpost_0()&isVisiblepost()=isVisible&tpost()=0)|(v=0&(wpost_0()*r=v&(apost()=0&rpost()=r&talphapost()=talpha&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=ox&oypost()=oy&dxpost()=-dx&dypost()=-dy&wpost()=wpost_0()&isVisiblepost()=isVisible&tpost()=0))|-b()<=apost_0()&apost_0()<=A&(rpost_0()!=0&(v+apost_0()*ep < 0&((isVisiblepost_0() < 0|((x-oxpost_0()>=0->x-oxpost_0()>v^2/(-2*apost_0())+V()*(v/-apost_0()))&(x-oxpost_0()<=0->oxpost_0()-x>v^2/(-2*apost_0())+V()*(v/-apost_0()))|(y-oypost_0()>=0->y-oypost_0()>v^2/(-2*apost_0())+V()*(v/-apost_0()))&(y-oypost_0()<=0->oypost_0()-y>v^2/(-2*apost_0())+V()*(v/-apost_0()))))&((rpost_0()>=0->v^2/(-2*apost_0()) < alpha()*rpost_0())&(rpost_0() < 0->v^2/(-2*apost_0()) < -alpha()*rpost_0())&(wpost_0()*rpost_0()=v&(apost()=apost_0()&rpost()=rpost_0()&talphapost()=0&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=oxpost_0()&oypost()=oypost_0()&dxpost()=dx&dypost()=dy&wpost()=wpost_0()&isVisiblepost()=isVisiblepost_0()&tpost()=0))))|v+apost_0()*ep>=0&((isVisiblepost_0() < 0|((x-oxpost_0()>=0->x-oxpost_0()>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))&(x-oxpost_0()<=0->oxpost_0()-x>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))|(y-oypost_0()>=0->y-oypost_0()>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))&(y-oypost_0()<=0->oypost_0()-y>v^2/(2*b())+V()*(v/b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*(v+V())))))&((rpost_0()>=0->v^2/(2*b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*v) < alpha()*rpost_0())&(rpost_0() < 0->v^2/(2*b())+(apost_0()/b()+1)*(apost_0()/2*ep^2+ep*v) < -alpha()*rpost_0())&(wpost_0()*rpost_0()=v&(apost()=apost_0()&rpost()=rpost_0()&talphapost()=0&odxpost()=odxpost_0()&odypost()=odypost_0()&oxpost()=oxpost_0()&oypost()=oypost_0()&dxpost()=dx&dypost()=dy&wpost()=wpost_0()&isVisiblepost()=isVisiblepost_0()&tpost()=0))))))))".asFormula

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only expectedAnte
    result.openGoals().head.sequent.succ should contain only expectedSucc
  }

  "Hybrid quadcopter" should "extract the correct controller monitor" in {
    val in = getClass.getResourceAsStream("examples/casestudies/quadcopter/hybridquadrotor.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model/*, List(Variable("href"))*/)

    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(modelplexInput))))

    val expectedAnte = "true".asFormula
    val expectedSucc = "h>=hrefpost_0()&hrefpost_0()>0&((kp < 0&v=0&hrefpost_0()>=h|kp < 0&v>0&2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&h*y>h*kd()+2*v|kp < 0&v < 0&2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&2*v+h*(kd()+y)>0|kp>0&v=0&hrefpost_0()=h|kp>0&v>0&(2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&h*y>h*kd()+2*v&kd()+2*sqrkp<=0|2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0|2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v)|kp>0&v < 0&(2*h*kp+v*(kd()+y)=2*hrefpost_0()*kp&kd()>2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&kd()>=2*sqrkp&h*y < h*kd()+2*v|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&kd()>2*sqrkp&2*v+h*(kd()+y)>0&h*y>=h*kd()+2*v|2*hrefpost_0()*kp+v*y=2*h*kp+kd()*v&h*y>h*kd()+2*v&2*v+h*(kd()+y)>=0&kd()+2*sqrkp < 0))&(y^2=kd()^2-4*kp&y>=0)&(sqrkp^2=kp&sqrkp>=0)&h^2*kp^2-2*h*hrefpost_0()*kp^2+hrefpost_0()^2*kp^2+h*kd()*kp*v-hrefpost_0()*kd()*kp*v+kp*v^2!=0|(kp < 0&v=0&(h*y<=h*kd()|h*(kd()+y)<=0|h>hrefpost_0())|kp < 0&v < 0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+kd()*v!=2*hrefpost_0()*kp+v*y)|kp < 0&v>0&(h*y<=h*kd()+2*v|2*v+h*(kd()+y)<=0|2*h*kp+v*(kd()+y)!=2*hrefpost_0()*kp)|kp>0&v=0&(h!=hrefpost_0()&(kd()>=2*sqrkp&h*y>=h*kd()|h*(kd()+y)>=0&kd()+2*sqrkp < 0)|kd()=2*sqrkp&h*y>=h*kd()|kd() < 2*sqrkp&kd()+2*sqrkp>0|h>hrefpost_0()|kd()>2*sqrkp&h*(kd()+y)<=0|kd()+2*sqrkp<=0&h*y<=h*kd())|kp>0&v < 0&(2*hrefpost_0()*kp+v*y!=2*h*kp+kd()*v&(h*y>=h*kd()+2*v|kd()<=2*sqrkp)|kd() < 2*sqrkp|kd()>2*sqrkp&(h*y < h*kd()+2*v&(2*hrefpost_0()*kp+v*y < 2*h*kp+kd()*v&2*h*kp+v*(kd()+y) < 2*hrefpost_0()*kp|2*hrefpost_0()*kp+v*y>2*h*kp+kd()*v|2*h*kp+v*(kd()+y)>2*hrefpost_0()*kp)|2*v+h*(kd()+y)<=0)|h*y>=h*kd()+2*v&kd()<=2*sqrkp|kd()+2*sqrkp<=0)|kp>0&v>0&(2*h*kp+v*(kd()+y)!=2*hrefpost_0()*kp&(kd()+2*sqrkp>=0|2*v+h*(kd()+y)>=0)|kd()>=2*sqrkp|kd()+2*sqrkp < 0&2*v+h*(kd()+y) < 0&(2*hrefpost_0()*kp+v*y < 2*h*kp+kd()*v|2*h*kp+v*(kd()+y) < 2*hrefpost_0()*kp|2*hrefpost_0()*kp+v*y>2*h*kp+kd()*v&2*h*kp+v*(kd()+y)>2*hrefpost_0()*kp)|kd()+2*sqrkp>0|h*y<=h*kd()+2*v))&y^2=kd()^2-4*kp&y>=0&sqrkp^2=kp&sqrkp>=0&h^2*kp^2-2*h*hrefpost_0()*kp^2+hrefpost_0()^2*kp^2+h*kd()*kp*v-hrefpost_0()*kd()*kp*v+kp*v^2=0)&hrefpost()=hrefpost_0()".asFormula

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only expectedAnte
    result.openGoals().head.sequent.succ should contain only expectedSucc
  }

  "VSL modelplex in place" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/iccps12/vsl-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = ("(x1post()=x1&v1post()=v1&a1post()=-B&tpost()=0&vslpost()=vsl&xslpost()=xsl) | " +
      "(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1post()=x1&v1post()=v1&a1post()=-B&tpost()=0&vslpost()=vslpost_0()&xslpost()=xslpost_0())) | " +
      "((xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1post_0()&a1post_0()<=A & " +
      "((x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vsl&xslpost()=xsl) | " +
      "(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vslpost_0()&xslpost()=xslpost_0()))))) | " +
      "(x1>=xsl&(-B<=a1post_0()&a1post_0()<=A&a1post_0()<=(v1-vsl)/ep & " +
      "((x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vsl&xslpost()=xsl) | " +
      "(vslpost_0()>=0&xslpost_0()>=x1+(v1^2-vslpost_0()^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1post()=x1&v1post()=v1&a1post()=a1post_0()&tpost()=0&vslpost()=vslpost_0()&xslpost()=xslpost_0()))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "v1>=0&vsl>=0&x1<=xsl&2*B*(xsl-x1)>=v1^2-vsl^2&A>=0&B>0&ep>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "VSL controller")
  }

  "Quadcopter modelplex in place" should "find correct controller monitor condition" in {
    val in = getClass.getResourceAsStream("examples/casestudies/modelplex/quadcopter/simplepid.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model, Variable("h"), Variable("v"), Variable("kp"),
      Variable("kd"), Variable("href"))

    val tactic = locateSucc(modelplexInPlace(useOptOne=true)(controllerMonitorT))
    val result = helper.runTactic(tactic, new RootNode(Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(modelplexInput))))

    val expectedAnte = "true".asFormula
    val expectedSucc = "true & (hpost()=h & vpost()=v & kppost()=kp & kdpost()=kd & hrefpost()=href)".asFormula

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only expectedAnte
    result.openGoals().head.sequent.succ should contain only expectedSucc
  }
}
