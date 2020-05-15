package btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith.doubleNeg
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3.{chaseIndex, composeIndex, defaultFaxs, emptyTaxs, fullSimpTac}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.PrivateMethodTester

import scala.collection.immutable._

class SOSsolveTests extends TacticTestBase with PrivateMethodTester {
  val prob1 = ("!(-200 + 10 * t1uscore0dollarskuscore0 + vuscore2dollarskuscore0 = 0 &" +
    "t1uscore0dollarskuscore0 >= 0 &" +
    "stuscore2dollarskuscore0 = 0 &" +
    "-2000 * stuscore2dollarskuscore0 - 4000 * suscore2dollarskuscore0 -" +
    "  200 * stuscore2dollarskuscore0 * tuscore2dollarskuscore0 - 5 * tuscore2dollarskuscore0^2 +" +
    "  10 * stuscore2dollarskuscore0 * tuscore2dollarskuscore0^2 + zuscore2dollarskuscore0 = 0 &" +
    "tuscore2dollarskuscore0 >= 0 &" +
    "suscore2dollarskuscore0 >= 0 &" +
    "vuscore2dollarskuscore0 >= 0 &" +
    "zuscore2dollarskuscore0 >= 0 &" +
    "-200 * stuscore2dollarskuscore0 - 10 * tuscore2dollarskuscore0 +" +
    "  20 * stuscore2dollarskuscore0 * tuscore2dollarskuscore0 + vuscore2dollarskuscore0 = 0 &" +
    "t1uscore0dollarskuscore0 + tuscore2dollarskuscore0 < 0)").asFormula
  val polys1 = (
    "stuscore2dollarskuscore0," +
      "-200 + 10 * t1uscore0dollarskuscore0 + vuscore2dollarskuscore0," +
      "-200 * stuscore2dollarskuscore0 - 10 * tuscore2dollarskuscore0 + 20 * stuscore2dollarskuscore0 * tuscore2dollarskuscore0 + vuscore2dollarskuscore0," +
      "-2000 * stuscore2dollarskuscore0 - 4000 * suscore2dollarskuscore0 - 200 * stuscore2dollarskuscore0 * tuscore2dollarskuscore0 - 5 * tuscore2dollarskuscore0^2 + 10 * stuscore2dollarskuscore0 * tuscore2dollarskuscore0^2 + zuscore2dollarskuscore0," +
      "-GEQ11^2 + suscore2dollarskuscore0," +
      "-GEQ12^2 + t1uscore0dollarskuscore0," +
      "-GEQ13^2 + tuscore2dollarskuscore0," +
      "-GEQ14^2 + vuscore2dollarskuscore0," +
      "-GEQ15^2 +  zuscore2dollarskuscore0," +
      "-1 + GT16^2 * (-t1uscore0dollarskuscore0 - tuscore2dollarskuscore0)"
    ).split(',').map(_.asTerm).toList
  val vars1 = ("vuscore2dollarskuscore0, t1uscore0dollarskuscore0, stuscore2dollarskuscore0, zuscore2dollarskuscore0," +
    "tuscore2dollarskuscore0, suscore2dollarskuscore0, GEQ11, GEQ12, GEQ13, GEQ14, GEQ15, GT16").split(',').map(_.asTerm).toList

  "sosSolveTool" should "return the certificate" in withMathematica { _ =>
    val sosSolveTool = ToolProvider.sosSolveTool().getOrElse(throw new RuntimeException("no SOSSolveTool configured"))
    sosSolveTool.sosSolve(polys1, vars1, 1, None) shouldBe
      Left("1+20*GT16^2".asTerm,
        "1/10*(200*GT16^2+-20*GT16^2*tuscore2dollarskuscore0), -1/10*GT16^2, 1/10*GT16^2, 0, 0, 0, 0, 0, 0, -1".split(',').map(_.asTerm).toList)
  } /* to verify: cofactors * polys = sos */

  "SOSSolve" should "prove using the certificate" in withMathematica { _ =>
    val pp = new KeYmaeraXPrettierPrinter(100)
    TaylorModelTactics.Timing.tic()
    PolynomialArithV2.ring
    TaylorModelTactics.Timing.toc("Initialized PolynomialArithV2")
    proveBy(prob1, prop & SOSSolve.sossolve(1)) shouldBe 'proved
  }

  it should "do" in withMathematica { _ =>
    val fml = ("\\forall y \\forall x (true->1/2250*((x^6+-10*x*y+3*x^4*y^2+3*x^2*y^4+y^6)*(7865*x^4+-12*x^3*(787+280*y)+-24*x*y*(-360+y*(257+140*y))+9*y^2*(140+y*(-1312+765*y))+2*x^2*(-630+y*(-5288+7375*y)))+(-4+x^2+y^2)*(23595*x^8+-36*x^7*(787+280*y)+-864*x^5*y*(-30+y*(87+35*y))+12*x^6*(-315+4*y*(-661+1905*y))+30*x^4*y^2*(-126+y*(-3296+4425*y))+6*x^2*(-1725+2*y*(5065+2800*y+315*y^3+-8548*y^4+7130*y^5))+-10*x^3*(-2696+7865*y+54*y^3*(-96+y*(121+56*y)))+-18*x*y^2*(-4720+3825*y+4*y^3*(-360+y*(257+140*y)))+9*y^2*(-3650+3*y*(640+y^3*(140+y*(-1312+765*y))))))=0-((0+2*x^(2-1)*(2*(- 3/5+x)*(1-337/225*(- 3/5+x)^2+56/75*(- 3/5+x)*(- 4/5+y)-32/25*(- 4/5+y)^2)-y+1/2*x*(4-x^2-y^2))+2*y^(2-1)*(x+2*(1-337/225*(- 3/5+x)^2+56/75*(- 3/5+x)*(- 4/5+y)-32/25*(- 4/5+y)^2)*(- 4/5+y)+1/2*y*(4-x^2-y^2)))*(-5*x*y+1/2*(x^2+y^2)^3)+(-4+x^2+y^2)*(-5*(2*(- 3/5+x)*(1-337/225*(- 3/5+x)^2+56/75*(- 3/5+x)*(- 4/5+y)-32/25*(- 4/5+y)^2)-y+1/2*x*(4-x^2-y^2))*y+-5*x*(x+2*(1-337/225*(- 3/5+x)^2+56/75*(- 3/5+x)*(- 4/5+y)-32/25*(- 4/5+y)^2)*(- 4/5+y)+1/2*y*(4-x^2-y^2))+1/2*(3*(x^2+y^2)^(3-1)*(2*x^(2-1)*(2*(- 3/5+x)*(1-337/225*(- 3/5+x)^2+56/75*(- 3/5+x)*(- 4/5+y)-32/25*(- 4/5+y)^2)-y+1/2*x*(4-x^2-y^2))+2*y^(2-1)*(x+2*(1-337/225*(- 3/5+x)^2+56/75*(- 3/5+x)*(- 4/5+y)-32/25*(- 4/5+y)^2)*(- 4/5+y)+1/2*y*(4-x^2-y^2)))))))").asFormula
    val res = proveBy(fml,SaturateTactic(useAt(DerivedAxioms.doubleNegationAxiom, PosInExpr(1::Nil))(1) & notR(1)) &
      fullSimpTac(faxs = composeIndex(defaultFaxs,chaseIndex),taxs = emptyTaxs) &
      SaturateTactic(onAll(alphaRule | betaRule | ?(existsL('L) | closeF) /* @note: the '?' is because this can fail, because somehow 'L points to a wrong position? */ | closeF)) &
      onAll(PolynomialArith.normAnte) &
      onAll(?(PolynomialArith.ratTac)) &
      onAll(SOSSolve.sossolve(1, Some(5)))
    )
    println(new KeYmaeraXPrettierPrinter(100).stringify(res))
  }

  it should "try to prove stuff generated by QELogger" in withMathematica { _ =>
    var positive = 0
    var negative = 0
    def summaryString(posneg: Boolean, res: ProvableSig) =
      (if(posneg) "+" else "-") + "(" + positive + "/" + (positive + negative) + "= " + 1.0*positive/(positive + negative) + ")"// + res.toString.replace('\n', ' ')
    def isForall(fml: Formula) = fml.isInstanceOf[Forall]
    def processEntry(degree: Int, timeout: Int)(entry: (String, Sequent, Sequent)) = entry match {
      case (n, seq0, seq) =>
        println()
        println("testing..." + seq.toString.replace('\n', ' '))
        val preprocessed = proveBy(seq,
          SaturateTactic(useAt(DerivedAxioms.doubleNegationAxiom, PosInExpr(1::Nil))(1) & notR(1)) &
            fullSimpTac(faxs = composeIndex(defaultFaxs,chaseIndex),taxs = emptyTaxs) &
            SaturateTactic(onAll(alphaRule | betaRule | ?(existsL('L) | closeF) /* @note: the '?' is because this can fail, because somehow 'L points to a wrong position? */ | closeF)) &
            onAll(PolynomialArith.normAnte) &
            onAll(?(PolynomialArith.ratTac) /* @note: this fails too often */)
        )
        val outofscope = preprocessed.subgoals.flatMap(subgoal => subgoal.ante.find(isForall(_))).headOption
        if (outofscope.isDefined) {
          println("Out of scope: " + outofscope.get)
        } else {
          val res = try {
            println(preprocessed.subgoals.length + " subgoal(s):")
            println(preprocessed)
            proveBy(preprocessed, onAll(SOSSolve.sossolve(degree, Some(timeout))))
          } catch {
            case belleProofSearchControl: BelleProofSearchControl =>
              println("Failure: " + belleProofSearchControl.getMessage)
              preprocessed
            case belleThrowable: BelleThrowable if belleThrowable.getMessage.startsWith("[Bellerophon Runtime] Divisor must be a constant polynomial.") =>
              println("Out of scope because of division but could be in scope.")
              preprocessed
            case belleThrowable: BelleThrowable if belleThrowable.getMessage.startsWith("[Bellerophon Runtime] Exponent must be integer but normalizes to") =>
              println("Out of scope because of exponentiation but could be in scope?")
              preprocessed
            case ex =>
              print("Unexpected failure")
              val qeTry = proveBy(seq, QE)
              if (qeTry.isProved){
                println(".")
                println(ex)
                ???
              } else {
                println(" but QE can't solve it, either. So let's continue.")
                preprocessed
              }
          }
          if (res.isProved) {
            positive = positive + 1
            println(summaryString(true, res))
          }
          else {
            negative = negative + 1
            println(summaryString(false, res))
          }
        }
    }
    withTemporaryConfig(Map(Configuration.Keys.DEBUG -> "false")){
      QELogger.processLog(QELogger.parseStr, processEntry(1, 5), "C:\\Users\\fabia\\work\\keymaerax\\QELogger\\haveqe_20200121.txt")
    }
  }

}