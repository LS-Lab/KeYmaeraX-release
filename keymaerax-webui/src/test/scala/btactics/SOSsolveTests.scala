package btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArith.doubleNeg
import edu.cmu.cs.ls.keymaerax.btactics.SOSSolve.{SOSSolveAborted, SOSSolveNoSOS}
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
    proveBy(prob1, prop & PolynomialArith.prepareArith & SOSSolve.witnessSOS(1)) shouldBe 'proved
  }

  def isConstant(t: Term) : Boolean = t match {
    case t: BinaryCompositeTerm => isConstant(t.left) && isConstant(t.right)
    case t: UnaryCompositeTerm => isConstant(t.child)
    case n: Number => true
    case t: AtomicTerm => false
    case t: FuncOf => false
    case _ => ???
  }

  def denominators(t: Term) : Seq[Term] = t match {
    case Divide(a, b) => if(isConstant(b)) denominators(a) else Seq(b)++denominators(a)++denominators(b)
    case t: BinaryCompositeTerm => denominators(t.left)++denominators(t.right)
    case t: UnaryCompositeTerm => denominators(t.child)
    case t: AtomicTerm => Seq()
    case t: FuncOf => denominators(t.child)
    case _ => ???
  }
  def denominators(fml: Formula) : Seq[Term] = fml match {
    case fml: BinaryCompositeFormula => denominators(fml.left)++denominators(fml.right)
    case fml: ComparisonFormula => denominators(fml.left)++denominators(fml.right)
    case fml: UnaryCompositeFormula => denominators(fml.child)
    case fml: AtomicFormula => Seq()
    case fml: PredOf => denominators(fml.child)
    case fml: PredicationalOf => denominators(fml.child)
    case _ =>
      ???
  }
  def denominators(seq: Sequent) : Seq[Term] = (seq.ante++seq.succ).flatMap(denominators)

  lazy val preprocess = SaturateTactic(useAt(DerivedAxioms.doubleNegationAxiom, PosInExpr(1 :: Nil))(1) & notR(1)) &
    fullSimpTac(faxs = composeIndex(defaultFaxs, chaseIndex), taxs = emptyTaxs) &
    SaturateTactic(onAll(alphaRule | betaRule | ?(existsL('L) | closeF) /* @note: the '?' is because this can fail, because somehow 'L points to a wrong position? */ | closeF)) &
    onAll(PolynomialArith.normAnte)

  it should "try to prove stuff generated by QELogger" in withMathematica { _ =>
    var success = 0
    var aborted = 0
    var noSos = 0
    var ratTacFailure = 0
    var unknown = 0
    var outofScopeQuantifier = 0
    var outofScopePower = 0

    def isForall(fml: Formula) = fml.isInstanceOf[Forall]
    def processEntry(degree: Int, timeout: Int)(entry: (String, Sequent, Sequent)) = entry match {
      case (n, seq0, seq) =>
        val qeTry = proveBy(seq, QE)
        if (!qeTry.isProved) {
          println("skipping false goal: " + seq.toString.replace('\n', ' '))
        } else {
          println("testing..." + seq.toString.replace('\n', ' '))
          val preprocessed = proveBy(seq, preprocess)
          val outofscope = preprocessed.subgoals.flatMap(subgoal => subgoal.ante.find(isForall(_))).headOption
          if (outofscope.isDefined) {
            println("Out of scope: " + outofscope.get)
            outofScopeQuantifier = outofScopeQuantifier + 1
          } else {
            try {
              println(preprocessed.subgoals.length + " subgoal(s):")
              println(preprocessed)
              val res = for (subgoal <- preprocessed.subgoals) yield {
                val denoms = denominators(subgoal)
                if (denoms.isEmpty)
                  proveBy(subgoal, SOSSolve.witnessSOS(degree, Some(timeout)))
                else
                {
                  println("strengthen assumptions for preprocessing of rational functions")
                  proveBy(Sequent(subgoal.ante++denoms.map(NotEqual(_, Number(0))), subgoal.succ),
                    PolynomialArith.ratTac & OnAll(preprocess) & OnAll(SOSSolve.witnessSOS(degree, Some(timeout))))
                }
              }
              if (res.forall(_.isProved)) {
                println("Success.")
                success = success + 1
              }
            } catch {
              case SOSSolveAborted() =>
                println("Aborted.")
                aborted = aborted + 1
              case SOSSolveNoSOS() =>
                println("No SOS found.")
                noSos = noSos + 1
              case belleThrowable: BelleThrowable if belleThrowable.getMessage.startsWith("[Bellerophon Runtime] Divisor must be a constant polynomial.") =>
                println("Division was not handled by ratTac.")
                ratTacFailure = ratTacFailure + 1
              case belleThrowable: BelleThrowable if belleThrowable.getMessage.startsWith("[Bellerophon Runtime] Exponent must be integer but normalizes to") =>
                println("Out of scope because of exponentiation but could be in scope?")
                outofScopePower = outofScopePower + 1
              case ex =>
                print("Unexpected failure.")
                println(ex)
                unknown = unknown + 1
            }
            val expected = aborted + noSos + ratTacFailure
            println("Success   : " + success)
            println("Expected  : " + expected)
            println("Success   : " + (success * 100 / (success + expected)) + "%")

            println("Aborted(T): " + aborted)
            println("NoSOS(T)  : " + noSos)
            println("ratTacFail: " + ratTacFailure)
            println("OOS (Q)   : " + outofScopeQuantifier)
            println("NoSOS(F)  : " + outofScopePower)
            println("Unknown   : " + unknown)
          }
        }
    }
    withTemporaryConfig(Map(Configuration.Keys.DEBUG -> "false")){
      QELogger.processLog(QELogger.parseStr, processEntry(6, 30), "C:\\Users\\fabia\\work\\keymaerax\\QELogger\\haveqe_20200121.txt")
    }
  }

}