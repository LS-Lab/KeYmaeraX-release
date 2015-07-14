import java.io.File

import edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.tactics.ProofNode.ProofStep
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import testHelper.ParserFactory._
import testHelper.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.ModelplexTacticImpl.{modelplex, modelplexInPlace, diamondModelplexTestT,
  locateT, optimizationOne, modelplexControllerMonitorTrafo}
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.diamondDiffSolve2DT
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{locateSucc,lastSucc,onBranch,lastAnte}
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.FOQuantifierTacticsImpl.instantiateT
import TacticLibrary._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{LabelBranch, NilT}
import scala.collection.immutable
import scala.language.postfixOps

/**
 * Created by smitsch on 3/8/15.
 * @author Stefan Mitsch
 */
class ModelplexTacticTests extends TacticTestSuite {

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
    result.openGoals()(0).sequent.succ should contain only "-1<=f & f<=(m-x)/ep".asFormula
    result.openGoals()(1).sequent.ante should contain only ("0<=x".asFormula, "x<=m".asFormula, "0<ep".asFormula, "-1<=f".asFormula, "f<=(m-x)/ep".asFormula)
    result.openGoals()(1).sequent.succ should contain only "t_0=0 & (fpost()=f & xpost()=x & tpost()=t_0)".asFormula
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
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with Modelplex diamond test
//    val expected = "-1<=f & f<=(m-x)/ep & (-1<=f & f<=(m-x)/ep -> f_post()=f & x_post()=x & t_post()=0)".asFormula

    // with ordinary diamond test
    val expected = "-1<=f&f<=(m-x)/ep&(fpost()=f&xpost()=x&tpost()=0)".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=x & x<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank controller")
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-ctrl.key"))
    val tactic = modelplexInPlace(useOptOne=false)(SuccPosition(0)) & optimizationOne()(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = "-1<=f&f<=(m-x)/ep&(fpost()=f&xpost()=x&tpost()=0)".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=x & x<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank controller")
  }

  it should "find correct model monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val tactic = modelplexInPlace(useOptOne=true, Some(Variable("c", Some(1), Real)))(SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with diamond test, before local QE
//    val expected = "-1<=f&f<=(m-l)/ep&(f()=f&(c_1=0&\\exists t.(t>=0&(\\forall s.(0<=s&s<=t->0<=s*f()+l&1*s+c_1<=ep)&(fpost=f()&lpost=t*f()+l&cpost=1*t+c_1)))))".asFormula

    // with diamond test, after local QE
    val expected = "-1<=f&f<=(m-l)/ep&(c_1=0&(t>=0&(((c_1<ep&(t<0|((t=0&l>=0)|(0<t&t<=-1*c_1+ep&(l>=0&f>=-1*l*t^-1))))|((c_1=ep&(t<0|(t=0&l>=0)))|(c_1>ep&t<0)))&(fpost=f&lpost=t*f+l&cpost=1*t+c_1)))))".asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "0<=l & l<=m & 0<ep".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Watertank model")
  }

  it should "find correct model monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/watertank/watertank-mx.key"))
    val tactic = modelplexInPlace(useOptOne=false)(SuccPosition(0)) &
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
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with Modelplex diamond test
//    val expected = ("-B<=al&al<=A & " +
//      "(-B<=al&al<=A -> " +
//      "(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
//      "(xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) -> " +
//      "-B<=af&af<=A & " +
//      "(-B<=af&af<=A -> " +
//      "xf_post()=xf&vf_post()=vf&af_post()=af&xl_post()=xl&vl_post()=vl&al_post()=al&t_post()=0))) | " +
//      "((vf=0&(vf=0->xf_post()=xf&vf_post()=vf&af_post()=0&xl_post()=xl&vl_post()=vl&al_post()=al&t_post()=0)) | " +
//      "(-B<=af&af<=-b&(-B<=af&af<=-b -> " +
//      "xf_post()=xf&vf_post()=vf&af_post()=af&xl_post()=xl&vl_post()=vl&al_post()=al&t_post()=0))))").asFormula

    // with ordinary diamond test
    val expected = ("-B<=al & al<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=af&af<=A&(xfpost()=xf&vfpost()=vf&afpost()=af&xlpost()=xl&vlpost()=vl&alpost()=al&tpost()=0))) | " +
      "((vf=0&(xfpost()=xf&vfpost()=vf&afpost()=0&xlpost()=xl&vlpost()=vl&alpost()=al&tpost()=0)) | " +
      "(-B<=af&af<=-b&(xfpost()=xf&vfpost()=vf&afpost()=af&xlpost()=xl&vlpost()=vl&alpost()=al&tpost()=0))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Local lane controller ")
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-ctrl.key"))
    val tactic = modelplexInPlace(useOptOne=false)(SuccPosition(0)) &
      (optimizationOne()(SuccPosition(0))*)
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = ("-B<=al & al<=A & " +
      "((xf+vf^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*vf)<xl+vl^2/(2*B) & " +
      "(-B<=af&af<=A&(xfpost()=xf&vfpost()=vf&afpost()=af&xlpost()=xl&vlpost()=vl&alpost()=al&tpost()=0))) | " +
      "((vf=0&(xfpost()=xf&vfpost()=vf&afpost()=0&xlpost()=xl&vlpost()=vl&alpost()=al&tpost()=0)) | " +
      "(-B<=af&af<=-b&(xfpost()=xf&vfpost()=vf&afpost()=af&xlpost()=xl&vlpost()=vl&alpost()=al&tpost()=0))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "xf < xl & xf + vf^2/(2*b) < xl + vl^2/(2*B) & B >= b & b > 0 & vf >= 0 & vl >= 0 & A >= 0 & ep > 0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "Local lane controller ")
  }

  ignore should "find correct model monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/fm11/llc-mx.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  "ETCS safety lemma modelplex in place" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/icfem08/safetylemma-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=false))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.succ should have size 1

    report(result.openGoals().head.sequent.succ.head, result, "ETCS controller")
  }

  "RSS passive safety modelplex in place" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/rss13/passivesafety-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with Modelplex diamond test
//    val expected = ("(x_post()=x&y_post()=y&v_post()=v&a_post()=-b&w_post()=w&dx_post()=dx&dy_post()=dy&r_post()=r&ox_post()=ox&oy_post()=oy&t_post()=0) | " +
//      "((v=0&(v=0->x_post()=x&y_post()=y&v_post()=v&a_post()=0&w_post()=0&dx_post()=dx&dy_post()=dy&r_post()=r&ox_post()=ox&oy_post()=oy&t_post()=0)) | " +
//      "(-b<=a&a<=A&(-b<=a&a<=A->r>0&(r>0->w*r=v&(w*r=v->(Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&(Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)->x_post()=x&y_post()=y&v_post()=v&a_post()=a&w_post()=w&dx_post()=dx&dy_post()=dy&r_post()=r&ox_post()=ox&oy_post()=oy&t_post()=0))))))").asFormula

    // with ordinary diamond test
    val expected = ("(xpost()=x&ypost()=y&vpost()=v&apost()=-B&wpost()=w&dxpost()=dx&dypost()=dy&rpost()=r&oxpost()=ox&oypost()=oy&tpost()=0) | " +
      "((v=0&(xpost()=x&ypost()=y&vpost()=v&apost()=0&wpost()=0&dxpost()=dx&dypost()=dy&rpost()=r&oxpost()=ox&oypost()=oy&tpost()=0)) | " +
      "(-B<=a&a<=A&(r!=0&(w*r=v&((Abs(x-ox)>v^2/(2*B)+V()*(v/B)+(A/B+1)*(A/2*ep^2+ep*(v+V()))|Abs(y-oy)>v^2/(2*B)+V()*(v/B)+(A/B+1)*(A/2*ep^2+ep*(v+V())))&(xpost()=x&ypost()=y&vpost()=v&apost()=a&wpost()=w&dxpost()=dx&dypost()=dy&rpost()=r&oxpost()=ox&oypost()=oy&tpost()=0))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "v>=0 & (Abs(x-ox)>v^2/(2*B) + V()*(v/B) | Abs(y-oy)>v^2/(2*B) + V()*(v/B)) & r!=0 & dx^2+dy^2=1 & A>=0 & B>0 & ep>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "RSS controller")
  }

  it should "generate the correct Modelplex property from the input model" in {
    val in = getClass.getResourceAsStream("examples/casestudies/robix/passivesafetyabs.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model, Variable("a"), Variable("r"))

    modelplexInput shouldBe  """
        |v >= 0
        |  & ( Abs(x-xo) > v^2 / (2*B) + V()*(v/B)
        |    | Abs(y-yo) > v^2 / (2*B) + V()*(v/B))
        |  & r != 0
        |  & dx^2 + dy^2 = 1
        |  & A >= 0
        |  & B > 0
        |  & V() >= 0
        |  & ep > 0
        |  -> <a:=apre();r:=rpre();>
        |     <dxo :=*;
        |      dyo :=*;
        |      ?dxo^2 + dyo^2 <= V()^2;
        |
        |      /* brake on current curve or remain stopped */
        |      {
        |        {a := -B; r:=r; }
        |      ++{?v = 0; a := 0; w := 0; r:=r; }
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
        |    	 ? Abs(x-xo) > v^2/(2*B) + V()*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V()))
        |    	 | Abs(y-yo) > v^2/(2*B) + V()*v/B + (A/B + 1) * (A/2 * ep^2 + ep*(v+V()));
        |    	 }
        |    	 };
        |
        |    	 t := 0;>(apost()=a&rpost()=r)
      """.stripMargin.asFormula
  }

  it should "find a reduced correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/rss13/passivesafety-ctrl-reduced.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with Modelplex diamond test
    //    val expected = ("(x_post()=x&y_post()=y&v_post()=v&a_post()=-b&w_post()=w&dx_post()=dx&dy_post()=dy&r_post()=r&ox_post()=ox&oy_post()=oy&t_post()=0) | " +
    //      "((v=0&(v=0->x_post()=x&y_post()=y&v_post()=v&a_post()=0&w_post()=0&dx_post()=dx&dy_post()=dy&r_post()=r&ox_post()=ox&oy_post()=oy&t_post()=0)) | " +
    //      "(-b<=a&a<=A&(-b<=a&a<=A->r>0&(r>0->w*r=v&(w*r=v->(Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v))&(Abs(x-ox)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)|Abs(y-oy)>v^2/(2*b)+(A/b+1)*(A/2*ep^2+ep*v)->x_post()=x&y_post()=y&v_post()=v&a_post()=a&w_post()=w&dx_post()=dx&dy_post()=dy&r_post()=r&ox_post()=ox&oy_post()=oy&t_post()=0))))))").asFormula

    // with ordinary diamond test
    val expectedAnte = "v>=0 & (Abs(x-ox)>v^2/(2*B) + V()*(v/B) | Abs(y-oy)>v^2/(2*B) + V()*(v/B)) & r!=0 & dx^2+dy^2=1 & A>=0 & B>0 & ep>0".asFormula
    val expectedSucc = ("(apost()=-B&rpost()=rpre()) | " +
      "(v=0&(apost()=0&rpost()=rpre()) | " +
      "(-B<=a&a<=A&(r!=0&(w*r=v&((Abs(x-ox)>v^2/(2*B)+V()*(v/B)+(A/B+1)*(A/2*ep^2+ep*(v+V()))|Abs(y-oy)>v^2/(2*B)+V()*(v/B)+(A/B+1)*(A/2*ep^2+ep*(v+V())))&(apost()=a&rpost()=r))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only expectedAnte
    result.openGoals().head.sequent.succ should contain only expectedSucc

    report(expectedSucc, result, "RSS controller")
  }

  it should "find the correct controller monitor condition from the input model" in {
    val in = getClass.getResourceAsStream("examples/casestudies/robix/passivesafetyabs.key")
    val model = KeYmaeraXProblemParser(io.Source.fromInputStream(in).mkString)
    val modelplexInput = modelplexControllerMonitorTrafo(model, Variable("a"), Variable("r"))

    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(modelplexInput))))

    val expectedAnte = "v>=0 & (Abs(x-xo)>v^2/(2*B)+V()*(v/B)|Abs(y-yo)>v^2/(2*B)+V()*(v/B)) & r!=0 & dx^2+dy^2=1 & A>=0 & B>0 & V()>=0 & ep>0".asFormula
    val expectedSucc = ("dxo^2+dyo^2<=V()^2 & (apost()=-B & rpost()=rpre() | " +
      "                                       (v=0 & (apost()=0 & rpost()=rpre())" +
      "                                       |-B<=a&a<=A & (r!=0 & (w*r=v & ((Abs(x-xo)>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))|Abs(y-yo)>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))) & (apost()=a&rpost()=r))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante should contain only expectedAnte
    result.openGoals().head.sequent.succ should contain only expectedSucc
  }

  it should "find correct controller monitor condition without intermediate Optimization 1" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/rss13/passivesafety-ctrl.key"))
    val tactic = modelplexInPlace(useOptOne=false)(SuccPosition(0)) &
      (optimizationOne()(SuccPosition(0))*)
    val result = helper.runTactic(tactic, new RootNode(s))

    // with ordinary diamond test
    val expected = ("(xpost()=x&ypost()=y&vpost()=v&apost()=-B&wpost()=w&dxpost()=dx&dypost()=dy&rpost()=r&oxpost()=ox&oypost()=oy&tpost()=0) | " +
      "((v=0&(xpost()=x&ypost()=y&vpost()=v&apost()=0&wpost()=0&dxpost()=dx&dypost()=dy&rpost()=r&oxpost()=ox&oypost()=oy&tpost()=0)) | " +
      "(-B<=a&a<=A&(r!=0&(w*r=v&((Abs(x-ox)>v^2/(2*B)+V()*(v/B)+(A/B+1)*(A/2*ep^2+ep*(v+V()))|Abs(y-oy)>v^2/(2*B)+V()*(v/B)+(A/B+1)*(A/2*ep^2+ep*(v+V())))&(xpost()=x&ypost()=y&vpost()=v&apost()=a&wpost()=w&dxpost()=dx&dypost()=dy&rpost()=r&oxpost()=ox&oypost()=oy&tpost()=0))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "v>=0 & (Abs(x-ox)>v^2/(2*B) + V()*(v/B) | Abs(y-oy)>v^2/(2*B) + V()*(v/B)) & r!=0 & dx^2+dy^2=1 & A>=0 & B>0 & ep>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "RSS controller without intermediate Optimization 1")
  }

  it should "work using the command line interface" in {
    // command line main has to initialize the prover itself, so dispose all test setup first
    afterEach()

    val inputFileName = "keymaerax-webui/src/test/resources/examples/casestudies/robix/passivesafetyabs.key"
    val vars = "a,r"
    val outputFileName = File.createTempFile("passivesafetyabs", ".mx").getAbsolutePath
    KeYmaeraX.main(Array("-modelplex", inputFileName, "-vars", vars, "-out", outputFileName))

    val expectedFileContent = And("v>=0 & (Abs(x-xo)>v^2/(2*B)+V()*(v/B)|Abs(y-yo)>v^2/(2*B)+V()*(v/B)) & r!=0 & dx^2+dy^2=1 & A>=0 & B>0 & V()>=0 & ep>0".asFormula,
      ("dxo^2+dyo^2<=V()^2 & (apost()=-B & rpost()=rpre() | " +
      "(v=0 & (apost()=0 & rpost()=rpre())" +
      "| -B<=a&a<=A & (r!=0 & (w*r=v & ((Abs(x-xo)>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))|Abs(y-yo)>v^2/(2*B)+V()*v/B+(A/B+1)*(A/2*ep^2+ep*(v+V()))) & (apost()=a&rpost()=r))))))").asFormula)

    val actualFileContent = scala.io.Source.fromFile(outputFileName).mkString
    KeYmaeraXParser(actualFileContent) shouldBe expectedFileContent
  }

  "VSL modelplex in place" should "find correct controller monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/iccps12/vsl-ctrl.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))

    // with Modelplex diamond test
//    val expected = ("(x1_post()=x1&v1_post()=v1&a1_post()=-B&t_post()=0&vsl_post()=vsl&xsl_post()=xsl) | " +
//      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
//      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) -> " +
//      "x1_post()=x1&v1_post()=v1&a1_post()=-B&t_post()=0&vsl_post()=vsl&xsl_post()=xsl)) | " +
//      "((xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
//      "(xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) -> " +
//      "-B<=a1&a1<=A&(-B<=a1&a1<=A->(x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl) | " +
//      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
//      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) -> " +
//      "x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl))))) | " +
//      "(x1>=xsl&(x1>=xsl->-B<=a1&a1<=A&a1<=(v1-vsl)/ep & (-B<=a1&a1<=A&a1<=(v1-vsl)/ep -> " +
//      "(x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl) | " +
//      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
//      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) -> " +
//      "x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl))))))").asFormula

    // with ordinary diamond test
    val expected = ("(x1_post()=x1&v1_post()=v1&a1_post()=-B&t_post()=0&vsl_post()=vsl&xsl_post()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1_post()=x1&v1_post()=v1&a1_post()=-B&t_post()=0&vsl_post()=vsl&xsl_post()=xsl)) | " +
      "((xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1)&(-B<=a1&a1<=A & " +
      "((x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl))))) | " +
      "(x1>=xsl&(-B<=a1&a1<=A&a1<=(v1-vsl)/ep & " +
      "((x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl) | " +
      "(vsl>=0&xsl>=x1+(v1^2-vsl^2)/(2*B)+(A/B+1)*(A/2*ep^2+ep*v1) & " +
      "(x1_post()=x1&v1_post()=v1&a1_post()=a1&t_post()=0&vsl_post()=vsl&xsl_post()=xsl))))))").asFormula

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only
      "v1>=0&vsl>=0&x1<=xsl&2*B*(xsl-x1)>=v1^2-vsl^2&A>=0&B>0&ep>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only expected

    report(expected, result, "VSL controller")
  }

  ignore should "find correct model monitor condition" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/iccps12/vsl-mx.key"))
    val tactic = locateSucc(modelplexInPlace(useOptOne=true))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  /*
  ignore should "find correct model monitor condition when manually guided" in {
    val s = parseToSequent(getClass.getResourceAsStream("examples/casestudies/modelplex/iccps12/vsl-mx.key"))
    val p = SuccPosition(0)
    val tactic = debugT("Start") &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondChoiceT :: Nil)(p) &
      locateT(substitutionDiamondAssignT :: Nil)(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondChoiceT :: Nil)(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(substitutionDiamondAssignT :: Nil)(p) &
      locateT(substitutionDiamondAssignT :: Nil)(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondModelplexTestT :: Nil)(p) &
      locateT(diamondSeqT :: Nil)(p) &
      locateT(diamondAssignEqualT :: Nil)(p) &
      locateT(v2vAssignT :: Nil)(p) &
      locateT(diamondDiffSolve3DT :: Nil)(p) &
      debugT("Result")

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }
  */
}
