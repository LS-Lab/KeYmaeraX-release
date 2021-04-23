package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, Tool}

import scala.collection.immutable.IndexedSeq
import org.scalatest.LoneElement._
import org.scalatest.exceptions.TestFailedDueToTimeoutException

/**
 * Tests [[ToolTactics.fullQE]] and [[ToolTactics.partialQE]].
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class QETests extends TacticTestBase {

  "Implicit params" should "work for Mathematica" in withMathematica { qeTool =>
    proveBy("1=1".asFormula, ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  "Full QE" should "prove x>0 & y>0 |- x*y>0" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x>0".asFormula, "y>0".asFormula), IndexedSeq("x*y>0".asFormula)), ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "prove x^2<0 |-" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x^2<0".asFormula), IndexedSeq()), ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "fail on |-" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq()), ToolTactics.fullQE(qeTool))
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "fail on parsed decimal representations" in withMathematica { qeTool =>
    val result = proveBy("0.33333333333333 = 1/3".asFormula,ToolTactics.fullQE(qeTool))
    result.isProved shouldBe false
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "correct behavior (Z3)" in withZ3 { qeTool =>
    a [BelleThrowable] should be thrownBy proveBy("0.33333333333333 = 1/3".asFormula,ToolTactics.fullQE(qeTool))
  }

  it should "fail on internal decimal representations" in withMathematica { qeTool =>
    val result = proveBy(Equal(Number(0.33333333333333),Divide(Number(1),Number(3))),ToolTactics.fullQE(qeTool))
    result.isProved shouldBe false
    result.subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "fail (?) on internal decimal representations (2)" in withMathematica { qeTool =>
    // This isn't as bad as the above two
    proveBy(Equal(Number(1.0),Minus(Number(4),Number(3))),ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "fail x()=x" in withMathematica { qeTool =>
    proveBy("x()=x".asFormula, ToolTactics.fullQE(qeTool)).subgoals.loneElement shouldBe " ==> false".asSequent
  }

  it should "not choke on irrelevant predicates" in withMathematica { tool =>
    proveBy("p_() & q_() -> 2<3".asFormula,ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "close predicates if possible" in withMathematica { tool =>
    proveBy("p_() & q_() -> p_() | 2<3".asFormula,ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "not branch to be clever with predicates" in withMathematica { tool =>
    //@note otherwise may split too extensively; master makes up for it with autoMP
    the [TacticInapplicableFailure] thrownBy proveBy("(2<3->p(x)) -> p(x)".asFormula,ToolTactics.fullQE(tool)) should
      have message "The sequent mentions uninterpreted functions or predicates; attempted to prove without but failed. Please apply further manual steps to expand definitions and/or instantiate arguments."
  }

  it should "not fail when already proved" in withMathematica { tool =>
    proveBy("x>0 -> x>0".asFormula, prop & ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "not fail on duplicate formulas" in withMathematica { tool =>
    proveBy("x=2, x=2, true, x=2 ==> x>=2, x>=2, x+1>=3".asSequent, ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "not have soundness bug with decimal representations " in withMathematica { _ =>

    val pr = proveBy("false".asFormula,
      cut("1-3 * 0.33333333333333 = 0".asFormula) <( QE,
      cut("3 * 0.33333333333333 = 1 ".asFormula)  <( eqL2R(-1)(2) & QE,
         QE)))

    pr.isProved shouldBe false
    pr.subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "not hide equalities about interpreted function symbols" in withMathematica { _ =>
    proveBy("abs(x) = y -> x=y | x=-y".asFormula, QE) shouldBe 'proved
  }

  it should "rewrite equalities about uninterpreted function symbols" in withMathematica { _ =>
    proveBy("f(a,b) = 3 -> f(a,b)>2".asFormula, QE) shouldBe 'proved
  }

  it should "abort on test timeout" in { the [TestFailedDueToTimeoutException] thrownBy withMathematica ({ _ =>
    val s = "A()>=0, B()>0, V()>=0, ep()>0, -B()<=a, a<=A(), r!=0, w_0*r=v_0, abs(x_0-xo_0)>v_0^2/(2*B())+V()*v_0/B()+(A()/B()+1)*(A()/2*t^2+t*(v_0+V())), t_0=0, v_0>=0, dx_0^2+dy_0^2=1, r_0!=0, -t*V()<=xo-xo_0, xo-xo_0<=t*V(), -t*(v-a/2*t)<=x-x_0, x-x_0<=t*(v-a/2*t), v=v_0+a*t, dx^2+dy^2=1, t>=0, t<=ep(), v>=0 ==> v=0, abs(x-xo)>v^2/(2*B())+V()*(v/B())".asSequent
    proveBy(s, QE()) shouldBe 'proved
  }, 2) should have message "The code passed to failAfter did not complete within 2 seconds." }

  it should "not translate quantified predicates verbatim" in withMathematica { _ =>
    the [TacticInapplicableFailure] thrownBy proveBy("\\forall x p(x) ==> p(y)".asSequent, QE()) should
      have message "The sequent mentions uninterpreted functions or predicates; attempted to prove without but failed. Please apply further manual steps to expand definitions and/or instantiate arguments."
  }

  it should "not translate quantified functions verbatim" in withMathematica { _ =>
    the [TacticInapplicableFailure] thrownBy proveBy("\\forall x f(x)=0 ==> f(y)=0".asSequent, QE()) should
      have message "The sequent mentions uninterpreted functions or predicates; attempted to prove without but failed. Please apply further manual steps to expand definitions and/or instantiate arguments."
  }

  it should "be able to run QE's internal steps" in withMathematica { _ =>
    proveBy("x>z, y=0, z>y ==> x>=0".asSequent,
      BelleParser("applyEqualities; toSingleFormula; universalClosure(\"x::z::nil\", 1); rcf")) shouldBe 'proved
    proveBy("x>z, y=0, z>y ==> x>=0".asSequent,
      BelleParser("applyEqualities; toSingleFormula; universalClosure(\"nil\", 1); rcf")) shouldBe 'proved
  }

  it should "abbreviate differential symbols and differentials" in withMathematica { _ =>
    proveBy("x'>0 ==> x'>=0".asSequent, QE) shouldBe 'proved
    proveBy("==> (x')^2>=0".asSequent, QE) shouldBe 'proved
    proveBy("(f(x))'>0 ==> (f(x))'>=0".asSequent, QE) shouldBe 'proved
  }

  "QE with specific tool" should "succeed with Mathematica" in withMathematica { _ =>
    val tactic = TactixLibrary.QE(Nil, Some("Mathematica"))
    proveBy("x>0 -> x>=0".asFormula, tactic) shouldBe 'proved
  }

  it should "succeed with Z3" in withZ3 { _ =>
    val tactic = TactixLibrary.QE(Nil, Some("Z3"))
    proveBy("x>0 -> x>=0".asFormula, tactic) shouldBe 'proved
  }

  it should "fail on tool mismatch" in withMathematica { _ =>
    the [BelleThrowable] thrownBy proveBy("0=0".asFormula, TactixLibrary.QE(Nil, Some("Z3"))) should have message "QE requires Z3, but got None"
  }

  it should "switch between tools" in withDatabase { db =>
    val provider = MultiToolProvider(
      new Z3ToolProvider :: MathematicaToolProvider(ToolConfiguration.config("mathematica")) :: Nil)
    ToolProvider.setProvider(provider)
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>=0&\\exists s x*s^2>0 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(BelleParser("implyR(1); andR(1); <(QE(\"Z3\"), QE(\"Mathematica\"))"),
      BelleProvable(ProvableSig.startProof(ArchiveParser.parseAsFormula(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser(
      """implyR('R=="x>0->x>=0&\exists s x*s^2>0");
        |andR('R=="x>=0&\exists s x*s^2>0"); <(
        |  "x>=0": QE("Z3"),
        |  "\exists s x*s^2>0": QE("Mathematica")
        |)""".stripMargin)
    interpreter.kill()
  }

  it should "use the default tool" in withDatabase { db =>
    val provider = MultiToolProvider(
      new Z3ToolProvider :: MathematicaToolProvider(ToolConfiguration.config("mathematica")) :: Nil)
    ToolProvider.setProvider(provider)
    val modelContent = "ProgramVariables. R x. End. Problem. x>0 -> x>=0&x>=-1 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(BelleParser("implyR(1); andR(1); <(QE, QE)"),
      BelleProvable(ProvableSig.startProof(ArchiveParser.parseAsFormula(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser(
      """implyR('R=="x>0->x>=0&x>=(-1)");
        |andR('R=="x>=0&x>=(-1)"); <(
        |  "x>=0": QE,
        |  "x>=(-1)": QE
        |)""".stripMargin)
  }

  it should "switch between tools from parsed tactic" in {
    val provider = MultiToolProvider(
      new Z3ToolProvider :: MathematicaToolProvider(ToolConfiguration.config("mathematica")) :: Nil)
    ToolProvider.setProvider(provider)
    val tactic = BelleParser("andR(1); <(QE(\"Z3\"), andR(1) ; <(QE(\"Mathematica\"), QE))")
    proveBy("x>0 ==> x>=0&\\exists s x*s^2>0&x>=-2".asSequent, tactic) shouldBe 'proved
  }

  "QE with timeout" should "reset timeout when done" in withDatabase{ db => withQE { _ =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>1 -> x>0 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(QE(Nil, None, Some(7)), BelleProvable(ProvableSig.startProof(ArchiveParser.parseAsFormula(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser("QE(\"7\")")
  }}

  it should "omit timeout reset when no timeout" in withDatabase{ db => withQE { _ =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>1 -> x>0 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(QE, BelleProvable(ProvableSig.startProof(ArchiveParser.parseAsFormula(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser("QE")
  }}

  it should "use the right tool" in withDatabase{ db => withQE { tool: Tool =>
    val modelContent = "ProgramVariables. R x. End. Problem. x>1 -> x>0 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db),
      ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false)))
    interpreter(QE(Nil, Some(tool.name), Some(7)), BelleProvable(ProvableSig.startProof(ArchiveParser.parseAsFormula(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser("QE(\"" + tool.name + "\", \"7\")")
  }}

  it should "complain about the wrong tool" in withZ3 { _ =>
    the [BelleThrowable] thrownBy proveBy("x>1 -> x>0".asFormula, QE(Nil, Some("Mathematica"), Some(7))) should have message "QE requires Mathematica, but got None"
  }

  "CEX in QE" should "not fail QE when FindInstance fails" in withMathematica { tool =>
    withTemporaryConfig(Map(Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve")) {
      val fml = """(\forall w2 \exists w3 \forall w4 \exists w5 \forall w6 \exists w7 \forall w8 \exists w9 \forall w10
        #\exists w11 \forall w12 \exists w13 \forall w14 \exists w15 \forall w16 \exists w17 \forall w18 \exists w19 \forall w20
        #(w11*100*w12^2*w13^2*w14^4*w15^777*w16^(15/552)*w7^44*w18^8*w19^2*w20^20 + y^100*x^1000 <= y^100*x^999*w1*w2^2*w3^3*w4^4*w5^5*w6^6*w7^7*w8^8*w9^9*w10^10)) &
        #x^2 + y^2 != y^2 &
        #y^100*x^1000 + w1*w5*w7 <= y^100*x^999*w1*w2^2*w3^3*w4^4*w5^5*w6^6*w7^7*w8^8*w9^9*w10^10 &
        #y^2 + y^2 != y^2 &
        #y^100*x^1000 + w3*w7*w8<= y^100*x^999*w1*w2^2*w3^3*w4^4*w5^5*w6^6*w7^7*w8^8*w9^9*w10^10 &
        #w1^2 + y^2 != y^2 &
        #y^100*x^1000 + w1*w2*w3*w4*w7 <= y^100*x^999*w1*w2^2*w3^3*w4^4*w5^5*w6^6*w7^7*w8^8*w9^9*w10^10 &
        #z^2 + y^2 != y^2 &
        #9000 * y^1000/2*z <= z^12
        #-> x^2 + y^2 + w1^2 + z^2 > 0""".stripMargin('#').asFormula

      tool.setOperationTimeout(1)
      // CEX will fail, timeout from followup QE expected
      val ex = the[BelleThrowable] thrownBy proveBy(fml, QE)
      ex.getCause match {
        case c: MathematicaComputationAbortedException => c.getMessage should include("Resolve")
        case _ => throw ex
      }
    }
  }

  "Partial QE" should "not fail on |-" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq(), IndexedSeq()), ToolTactics.partialQE(qeTool)).
      subgoals.loneElement shouldBe "==> false".asSequent
  }

  it should "not forget assumptions on x^2>=0 |- y>1" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x^2>=0".asFormula), IndexedSeq("y>1".asFormula)), ToolTactics.partialQE(qeTool)).
      subgoals.loneElement shouldBe  "x^2>=0 ==> y>1".asSequent
  }

}
