package btactics

import java.io.FileWriter

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
import edu.cmu.cs.ls.keymaerax.tools.MathematicaComputationAbortedException
import org.scalatest.PrivateMethodTester
import org.scalatest.time.{Hours, Span}

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
    SaturateTactic(onAll(?(alphaRule | betaRule | existsL('L) | closeF)
      /* @note it seems weird to have to use the ?, but there are cases where this fails with positions locating outside a goal.
      * Probably when none of the alternatives match the first subgoal...
      * */)) &
    onAll(PolynomialArith.normAnte)

  override def timeLimit = Span(24, Hours)

  it should "try to prove stuff generated by QELogger" in withMathematica { _ =>
    import java.text.SimpleDateFormat
    import java.util.Date
    import java.util.Calendar

    val logPath = Configuration.path(Configuration.Keys.QE_LOG_PATH)
    val dateStr = new SimpleDateFormat("yyyy-MM-dd-HH-mm").format(Calendar.getInstance.getTime)

    trait Status { val name: String; val message: String}
    final case object Success             extends Status { val name = "success"; val message = "Success."}
    final case object Aborted             extends Status { val name = "aborted"; val message = "Aborted, likely due to timeout."}
    final case object NoSOS               extends Status { val name = "nosos--"; val message = "No SOS found (internal error or degree bound exceeded?)."}
    final case object RatTacFailure       extends Status { val name = "rattac-"; val message = "Division was not handled by ratTac."}
    final case object Unknown             extends Status { val name = "unknown"; val message = "Unknown error - investigate exception trace!"}
    final case object OutOfScopeUniversal extends Status { val name = "nonuniv"; val message = "Out of scope, non-universal."}
    final case object OutOfScopePower     extends Status { val name = "nonpow-"; val message = "Out of scope, non-natural power."}
    final case object QEFalse             extends Status { val name = "qefalse"; val message = "QE reduces to false."}
    final case object QETimeout           extends Status { val name = "qeto---"; val message = "QE timed out."}

    class Counter(status: Status) {
      private var countVar = 0
      def count = countVar
      val fileName = logPath + "soslog-" + dateStr + "-" + status.name + ".txt"
      def log(n: String, concl: Sequent, subgoal: Sequent) : Unit = {
        QELogger.logSequent(concl, subgoal, n, fileName)
      }
      def inc() : Status = {
        println(status.message)
        countVar = countVar + 1
        status
      }
      def inc(n: String, concl: Sequent, subgoal: Sequent) : Status = {
        log(n, concl, subgoal)
        inc()
      }
    }
    val success = new Counter(Success)
    val aborted = new Counter(Aborted)
    val noSos = new Counter(NoSOS)
    val ratTacFailure = new Counter(RatTacFailure)
    val unknown = new Counter(Unknown)
    val outofScopeQuantifier = new Counter(OutOfScopeUniversal)
    val outofScopePower = new Counter(OutOfScopePower)
    val qeFalse = new Counter(QEFalse)
    val qeTimeout = new Counter(QETimeout)
    var i = 0

    val outfileName = logPath + "soslog-" + dateStr + "-timings.txt"
    val outfile = new java.io.File(outfileName)

    def isForall(fml: Formula) = fml.isInstanceOf[Forall]
    def processEntry(degree: Int, timeout: Int)(entry: (String, Sequent, Sequent)) = entry match {
      case (n, seq0, seq) =>
        val totalTimer = Timer()
        val qeTimer = Timer()
        val preprocTimer = Timer()
        val sosTimer = Timer()
        val witnessTimer = Timer()
        println(i + "/3034 (" + n + "): " + seq.toString.replace('\n', ' '))
        i = i + 1
        print("trying QE...")
        val qeTry = qeTimer.time {
          proveBy(seq, ?(QE(timeout = Some(timeout))))
        }
        val status = if (!qeTry.isProved) {
          if (qeTry.subgoals.exists(_.succ.contains(False))) {
            qeFalse.inc()
          } else {
            qeTimeout.inc(n, seq0, seq)
          }
        } else totalTimer.time {
          println("preprocessing...")
          val preprocessed = preprocTimer.time {
            proveBy(seq, preprocess)
          }
          val outofscope = preprocessed.subgoals.flatMap(subgoal => subgoal.ante.find(isForall(_))).headOption
          if (outofscope.isDefined) {
            outofScopeQuantifier.inc()
          } else {
            try {
              println(preprocessed.subgoals.length + " subgoal(s):")
              val res = for ((subgoal, subgoalN) <- preprocessed.subgoals.zipWithIndex) yield {
                println("Subgoal " + subgoalN + ": " + subgoal.ante.mkString(", ") + subgoal.succ.mkString(" ==> ", ", ", ""))
                val denoms = denominators(subgoal)
                if (denoms.isEmpty)
                  proveBy(subgoal, SOSSolve.witnessSOS(degree, Some(timeout), sosTimer, witnessTimer))
                else {
                  println("strengthen assumptions for preprocessing of rational functions...")
                  val noRat = preprocTimer.time {
                    proveBy(Sequent(subgoal.ante ++ denoms.map(NotEqual(_, Number(0))), subgoal.succ),
                      PolynomialArith.ratTac & OnAll(preprocess))
                  }
                  proveBy(noRat, OnAll(SOSSolve.witnessSOS(degree, Some(timeout), sosTimer, witnessTimer)))
                }
              }
              if (res.forall(_.isProved)) {
                success.inc()
              } else {
                ???
              }
            } catch {
              case SOSSolveAborted() =>
                aborted.inc(n, seq0, seq)
              case SOSSolveNoSOS() =>
                noSos.inc(n, seq0, seq)
              case belleThrowable: BelleThrowable if belleThrowable.getMessage.startsWith("[Bellerophon Runtime] Divisor must be a constant polynomial.") =>
                ratTacFailure.inc(n, seq0, seq)
              case belleThrowable: BelleThrowable if belleThrowable.getMessage.startsWith("[Bellerophon Runtime] Exponent must be integer but normalizes to") =>
                outofScopePower.inc(n, seq0, seq)
              case ex =>
                print("Unexpected failure:")
                println(ex)
                unknown.inc(n, seq0, seq)
            }
          }
        }
        println("Timings[ms]")
        println("  QE      : " + qeTimer.getTimeMs)
        println("    preproc : " + preprocTimer.getTimeMs)
        if (status == Success) {
          println("    SOSsolve: " + sosTimer.getTimeMs)
          println("    verify  : " + witnessTimer.getTimeMs)
          println("       witness/search: " + (witnessTimer.getTimeMs / sosTimer.getTimeMs))
          println("       prove/search  : " + ((preprocTimer.getTimeMs + witnessTimer.getTimeMs) / sosTimer.getTimeMs))
          println("  Sum       : " + (sosTimer.getTimeMs + witnessTimer.getTimeMs))
          println("  Total     : " + totalTimer.getTimeMs)
          println("    Accuracy: " + (sosTimer.getTimeMs + witnessTimer.getTimeMs) / totalTimer.getTimeMs)
          println("  Total/QE  : " + (totalTimer.getTimeMs / qeTimer.getTimeMs))
        }

        // log timings
        try {
          val f = outfile
          val parent = outfile.getParentFile
          if (parent != null) parent.mkdirs()
          val timers = Seq(qeTimer, totalTimer, preprocTimer, sosTimer, witnessTimer)
          val timings = Seq(status.name) ++ timers.map(timer => if (status==Success) timer.getTimeMs else 0.0)
          val fw = new FileWriter(f, true)
          fw.append(timings.mkString(" ") + "\n")
          fw.close()
        } catch {
          case ex: Exception =>
            ???
        }

        val expected = aborted.count + noSos.count + ratTacFailure.count
        println("Success  : " + success.count)
        println("Expected : " + expected)
        println("Success %: " + (success.count * 100 / (success.count + expected)) + "%")

        println("Aborted(T): " + aborted.count)
        println("NoSOS(T)  : " + noSos.count)
        println("non-universal: " + outofScopeQuantifier.count)
        println("non-natural power: " + outofScopePower.count)
        println("ratTacFail: " + ratTacFailure.count)
        println("Unknown   : " + unknown.count)
        println("QE false  : " + qeFalse.count)
        println("QE timeout: " + qeTimeout.count)
      }
    val logfilename = "haveqe_20200121.txt"

    withTemporaryConfig(Map(Configuration.Keys.DEBUG -> "false")){
      QELogger.processLog(QELogger.parseStr, processEntry(100, 1), logPath + logfilename)
    }
  }

}