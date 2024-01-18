/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import java.io.FileWriter
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.SOSSolve.{ExponentOutOfScopeFailure, NonUniversalOutOfScopeFailure, RatFormError, SOSSolveAborted, SOSSolveNoSOS, SOSWelldefinedDivisionFailure}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.IgnoreInBuildTest
import edu.cmu.cs.ls.keymaerax.tools.ext.SOSsolveTool.Witness
import org.scalatest.PrivateMethodTester
import org.scalatest.LoneElement._
import org.scalatest.time.{Days, Span}

import scala.collection.immutable._

class SOSsolveTests extends TacticTestBase with PrivateMethodTester {
  private lazy val prob1 = ("!(-200 + 10 * t10_0 + v2_0 = 0 &" +
    "t10_0 >= 0 &" +
    "st2_0 = 0 &" +
    "-2000 * st2_0 - 4000 * s2_0 -" +
    "  200 * st2_0 * t2_0 - 5 * t2_0^2 +" +
    "  10 * st2_0 * t2_0^2 + z2_0 = 0 &" +
    "t2_0 >= 0 &" +
    "s2_0 >= 0 &" +
    "v2_0 >= 0 &" +
    "z2_0 >= 0 &" +
    "-200 * st2_0 - 10 * t2_0 +" +
    "  20 * st2_0 * t2_0 + v2_0 = 0 &" +
    "t10_0 + t2_0 < 0)").asFormula
  private lazy val polys1 = (
    "st2_0," +
      "-200 + 10 * t10_0 + v2_0," +
      "-200 * st2_0 - 10 * t2_0 + 20 * st2_0 * t2_0 + v2_0," +
      "-2000 * st2_0 - 4000 * s2_0 - 200 * st2_0 * t2_0 - 5 * t2_0^2 + 10 * st2_0 * t2_0^2 + z2_0," +
      "-GEQ11^2 + s2_0," +
      "-GEQ12^2 + t10_0," +
      "-GEQ13^2 + t2_0," +
      "-GEQ14^2 + v2_0," +
      "-GEQ15^2 +  z2_0," +
      "-1 + GT16^2 * (-t10_0 - t2_0)"
    ).split(',').map(_.asTerm).toList
  private lazy val vars1 = ("v2_0, t10_0, st2_0, z2_0," +
    "t2_0, s2_0, GEQ11, GEQ12, GEQ13, GEQ14, GEQ15, GT16").split(',').map(_.asTerm).toList

  "sosSolveTool" should "return the certificate" in withMathematica { _ =>
    val sosSolveTool = ToolProvider.sosSolveTool().getOrElse(fail("no SOSSolveTool configured"))
    sosSolveTool.sosSolve(polys1, vars1, 1, None) shouldBe
      Witness("1+20*GT16^2".asTerm,
        "20*GT16^2+(-2)*GEQ13^2*GT16^2, 0, 0, 0, (-1)".split(',').map(_.asTerm).toList,
        List(
          (2,"v2_0","200+(-10)*t10_0","1"),
          (2,"t10_0","1/10*(200+(-200)*st2_0+(-10)*t2_0+20*st2_0*t2_0)", "(-10)"),
          (2,"z2_0","4000*s2_0+2000*st2_0+200*st2_0*t2_0+5*t2_0^2+(-10)*st2_0*t2_0^2","1"),
          (4,"t2_0","GEQ13^2","1"),
          (2,"s2_0","GEQ11^2","1")).map{case (i, a, b, c) => (i, a.asTerm, b.asTerm, c.asTerm)}
      )
  }

  "SOSSolve" should "prove using the certificate" in withMathematica { _ =>
    TaylorModelTactics.Timing.tic()
    PolynomialArithV2
    TaylorModelTactics.Timing.toc("Initialized PolynomialArithV2")
    proveBy(prob1, prop &
      SOSSolve.prepareArith &
      SOSSolve.witnessSOS(1, SOSSolve.lexicographicVariableOrdering)) shouldBe Symbol("proved")
  }

  "SOSSolve.sos()" should "find a certificate and prove" in withMathematica { _ =>
    proveBy(prob1, SOSSolve.sos()) shouldBe Symbol("proved")
  }

  it should "illustrate automatic and interactive treatment of division" in withMathematica { _ =>
    // a more or less arbitrary goal arising from the etcs case study
    val fml = "((A>=0&ep>=0&1>=0&1>0&sbsc>0&ms>0&g>0&-1<=0&0<=1&v_1<=vdes&0<=Tw&Tw<=A&v_1^2-d^2<=2*(1*sbsc/ms)*(m-z)&d>=0&t>=0&v>=0&t<=ep&v_1>=0&0<=ep->(1*Tw/1-(ms*0+ms*g*0)-((v*(1-1)+1)*sbsc+0))/ms=0+(Tw/ms-1*sbsc/ms)*1|m-z<=(v_1^2-d^2)/(2*1*sbsc/ms)+(A/ms/(1*sbsc/ms)+1)*(A/ms/2*ep^2+ep*v_1)|em=1))".asFormula
    import SOSSolve._
    // without handling rational functions: should produce a meaningful error message
    val ex1 = the [RatFormError] thrownBy proveBy(fml, sos())
    ex1.getMessage should include ("Try a RatForm strategy to eliminate rational functions.")

    // prove welldefinedness of divisions with sossolve
    proveBy(fml, sos(RatForm(true))) shouldBe Symbol("proved")

    // assume welldefinedness of divisions: fails, but gives a hint at how to fix:
    val ex2 = the [RatFormError] thrownBy proveBy(fml, sos(RatForm(false)))
    ex2.getMessage should include ("try to cut in '2*ms^2*sbsc > 0' or '2*ms^2*sbsc < 0'")

    // Manually (here also with sos) cut in the missing sign assumption
    proveBy(fml, prop & cut("2*ms^2*sbsc > 0".asFormula) & Idioms.<(
      sos(RatForm(false)),
      cut("ms>0&sbsc>0".asFormula) & Idioms.<(
        cohideOnlyL(Symbol("Llast")) & cohideOnlyR(Symbol("Rlast")) & sos(),
        prop & done
      )
    )) shouldBe Symbol("proved")
  }

  "ratFormAnte and elimRatForm" should "test" in withMathematica { _ =>
    val seq = "b > 0, x + y/b = 0, x - y/2 = 0, x / b + x + y/(2*b) = 0 ==> ".asSequent
    val ratFormPrv = proveBy(seq, SOSSolve.ratFormAnte)
    ratFormPrv.subgoals.loneElement shouldBe "b/1>0,(y+b*x)/b=0, (-y+2*x)/2=0, (y+2*x+2*b*x)/(2*b)=0 ==> ".asSequent

    // eliminate rational forms (with sign assumptions expected in the
    val ex = the [RatFormError] thrownBy proveBy(ratFormPrv, SOSSolve.elimRatForms(false))
    ex.getMessage should include ("try to cut in '2*b > 0' or '2*b < 0'")

    val prv = proveBy(ratFormPrv, cut("2*b>0".asFormula) & Idioms.<(skip, QE))
    val prv2 = proveBy(prv, SOSSolve.elimRatForms(false))
    prv2.subgoals.loneElement shouldBe "b>0, y+b*x=0, -y+2*x=0, y+2*x+2*b*x=0, 2*b>0 ==> ".asSequent

    val prv3 = proveBy(ratFormPrv, SOSSolve.elimRatForms(true))
    println(prv3)
    prv3.subgoals should contain theSameElementsInOrderAs List(
      "b>0, y+b*x=0, -y+2*x=0, y+2*x+2*b*x=0 ==> ".asSequent,
      "b>0, y+b*x=0, -y+2*x=0 ==> 2*b != 0".asSequent)
  }

}

/** Test SOSsolve on benchmark suites in the QELogger format */
@IgnoreInBuildTest
class SOSsolveQELoggerTests extends TacticTestBase with PrivateMethodTester {
    override def timeLimit = Span(365, Days)

  def isConstant(t: Term): Boolean = t match {
    case t: BinaryCompositeTerm => isConstant(t.left) && isConstant(t.right)
    case t: UnaryCompositeTerm => isConstant(t.child)
    case n: Number => true
    case t: AtomicTerm => false
    case t: FuncOf => false
    case _ => ???
  }

  def denominators(t: Term): Seq[Term] = t match {
    case Divide(a, b) => if (isConstant(b)) denominators(a) else Seq(b) ++ denominators(a) ++ denominators(b)
    case t: BinaryCompositeTerm => denominators(t.left) ++ denominators(t.right)
    case t: UnaryCompositeTerm => denominators(t.child)
    case t: AtomicTerm => Seq()
    case t: FuncOf => denominators(t.child)
    case _ => ???
  }

  def denominators(fml: Formula): Seq[Term] = fml match {
    case fml: BinaryCompositeFormula => denominators(fml.left) ++ denominators(fml.right)
    case fml: ComparisonFormula => denominators(fml.left) ++ denominators(fml.right)
    case fml: UnaryCompositeFormula => denominators(fml.child)
    case fml: AtomicFormula => Seq()
    case fml: PredOf => denominators(fml.child)
    case fml: PredicationalOf => denominators(fml.child)
    case _ =>
      ???
  }

  def denominators(seq: Sequent): Seq[Term] = (seq.ante ++ seq.succ).flatMap(denominators)

  "SOSSolve" should "try to prove stuff generated by QELogger" in withMathematica { _ =>
    import java.text.SimpleDateFormat
    import java.util.Date
    import java.util.Calendar

    val logPath = Configuration.path(Configuration.Keys.SOSSOLVE_LOG_PATH)
    val logfilename = logPath + Configuration(Configuration.Keys.SOSSOLVE_LOG_INPUT)
    val logtimeout = Configuration(Configuration.Keys.SOSSOLVE_LOG_TIMEOUT).toInt
    val variableOrdering = Configuration(Configuration.Keys.SOSSOLVE_VARIABLE_ORDERING) match {
      case "lexicographic" =>
        SOSSolve.lexicographicVariableOrdering
      case "preferAuxiliary" =>
        SOSSolve.preferAuxiliaryVariableOrdering
      case "deferAuxiliary" =>
        SOSSolve.deferAuxiliaryVariableOrdering
      case k => throw new IllegalArgumentException("Unknown key for variable ordering: " + k)
    }
    var lineCount = 0
    QELogger.processLog(_ => Some(()), { _: Unit => lineCount = lineCount + 1 } , logfilename)

    val dateStr = new SimpleDateFormat("yyyy-MM-dd-HH-mm").format(Calendar.getInstance.getTime)

    trait Status { val name: String; val message: String}
    final case object Success             extends Status { val name = "success"; val message = "Success."}
    final case object Aborted             extends Status { val name = "aborted"; val message = "Aborted, likely due to timeout."}
    final case object NoSOS               extends Status { val name = "nosos--"; val message = "No SOS found (internal error or degree bound exceeded?)."}
    final case object DivisorElimination  extends Status { val name = "divelim"; val message = "Division was not eliminated."}
    final case object DivisorWellDefined  extends Status { val name = "divwell"; val message = "Division could not be proved to be well-defined."}
    final case object Unknown             extends Status { val name = "unknown"; val message = "Unknown error - investigate exception trace!"}
    final case object OutOfScopeUniversal extends Status { val name = "nonuniv"; val message = "Out of scope, non-universal."}
    final case object OutOfScopePower     extends Status { val name = "nonpow-"; val message = "Out of scope, non-natural power."}
    final case object QEFalse             extends Status { val name = "qefalse"; val message = "QE reduces to false."}
    final case object SubgoalFalse        extends Status { val name = "prprcF-"; val message = "QE reduces to false after preprocessing - likely the result of eliminating an ill-defined division."}
    final case object SubgoalTimeout      extends Status { val name = "prprcTO"; val message = "QE timed out after preprocessing - likely the result of eliminating an ill-defined division."}
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
    val divisorElimination = new Counter(DivisorElimination)
    val divisorWelldefinedness = new Counter(DivisorWellDefined)
    val unknown = new Counter(Unknown)
    val outofScopeUniversal = new Counter(OutOfScopeUniversal)
    val outofScopePower = new Counter(OutOfScopePower)
    val qeFalse = new Counter(QEFalse)
    val subgoalFalse = new Counter(SubgoalFalse)
    val subgoalTimeout = new Counter(SubgoalTimeout)
    val qeTimeout = new Counter(QETimeout)
    var i = 0

    val outfileName = logPath + "soslog-" + dateStr + "-timings.txt"
    val outfile = new java.io.File(outfileName)

    def isForall(fml: Formula) = fml.isInstanceOf[Forall]

    val preprocessOnly = false

    def processEntry(degree: Int, variableOrdering: Ordering[Variable], timeout: Int)(entry: (String, Sequent, Sequent)): Unit = entry match {
      case (n, seq0, seq) =>
        val totalTimer = Timer()
        val qeTimer = Timer()
        val preprocTimer = Timer()
        val ratFormTimer = Timer()
        val sosTimer = Timer()
        val witnessTimer = Timer()
        println(s"$i/$lineCount($n): ${seq.toString.replace('\n', ' ')}")
        i = i + 1
        print("trying QE...")
        val qeTry = qeTimer.time {
          if(preprocessOnly)
            proveBy(True, closeT)
          else
            proveBy(seq, ?(QEX(None, Some(Number(timeout)))))
        }
        val status = if (!qeTry.isProved) {
          if (qeTry.subgoals.exists(_.succ.contains(False))) {
            qeFalse.inc()
          } else {
            qeTimeout.inc(n, seq0, seq)
          }
        } else totalTimer.time {
          try {
            val ratFormStrategy = SOSSolve.RatForm(true)
//            val ratFormStrategy = SOSSolve.NoRatForm
            println("preprocessing...")
            val preprocessed = preprocTimer.time {
              proveBy(seq, OnAll(SOSSolve.preprocess(ratFormStrategy)))
            }
            println("preprocessed.")
            val res = if(preprocessOnly)Seq() else for ((subgoal, subgoalN) <- preprocessed.subgoals.zipWithIndex) yield {
              println("Subgoal " + subgoalN + ": " + subgoal.ante.mkString(", ") + subgoal.succ.mkString(" ==> ", ", ", ""))
              proveBy(subgoal,
                SOSSolve.sos(ratFormStrategy,
                  Some(degree),
                  Some(variableOrdering),
                  Some(Some(timeout)),
                  sosTimer,
                  witnessTimer,
                  skipPreprocessing = true))
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
            case PolynomialArithV2.NonSupportedOperationInapplicability(_: PolynomialArithV2.NonSupportedExponentException) =>
              outofScopePower.inc(n, seq0, seq)
            case PolynomialArithV2.NonSupportedExponentException(_) =>
              outofScopePower.inc(n, seq0, seq)
            case SOSWelldefinedDivisionFailure(_) =>
              divisorWelldefinedness.inc(n, seq0, seq)
            case NonUniversalOutOfScopeFailure(_) =>
              outofScopeUniversal.inc(n, seq0, seq)
            case ExponentOutOfScopeFailure(_) =>
              outofScopeUniversal.inc(n, seq0, seq)
            case ex: Throwable =>
              print("Unexpected failure:")
              println(ex)
              unknown.inc(n, seq0, seq)
          }
        }
        println("Timings[ms]")
        println("  QE      : " + qeTimer.getTimeMs)
        println("    preproc : " + preprocTimer.getTimeMs)
        println("    ratForm : " + ratFormTimer.getTimeMs)
        if (status == Success) {
          println("    SOSsolve: " + sosTimer.getTimeMs)
          println("    verify  : " + witnessTimer.getTimeMs)
          println("       witness/search: " + (witnessTimer.getTimeMs / sosTimer.getTimeMs))
          println("       prove/search  : " + ((preprocTimer.getTimeMs + ratFormTimer.getTimeMs + witnessTimer.getTimeMs) / sosTimer.getTimeMs))
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
          val timers = Seq(qeTimer, totalTimer, preprocTimer, ratFormTimer, sosTimer, witnessTimer)
          val timings = Seq(status.name) ++ timers.map(timer => if (status==Success || timer==qeTimer) timer.getTimeMs else 0.0)
          val fw = new FileWriter(f, true)
          fw.append(timings.mkString(" ") + "\n")
          fw.close()
        } catch {
          case ex: Exception =>
            throw ex
        }

        val expected = aborted.count + noSos.count + divisorElimination.count + divisorWelldefinedness.count + unknown.count
        println("Success  : " + success.count)
        println("Expected : " + expected)
        if (success.count + expected > 0)
          println("Success %: " + (success.count * 100 / (success.count + expected)) + "%")

        println("Aborted(T): " + aborted.count)
        println("NoSOS(T)  : " + noSos.count)
        println("non-universal: " + outofScopeUniversal.count)
        println("non-natural power: " + outofScopePower.count)
        println("divisor elimination: " + divisorElimination.count)
        println("divisor welldefinedness: " + divisorWelldefinedness.count)
        println("subgoalFalse: " + subgoalFalse.count)
        println("subgoalTimeout: " + subgoalTimeout.count)
        println("Unknown   : " + unknown.count)
        println("QE false  : " + qeFalse.count)
        println("QE timeout: " + qeTimeout.count)
      }

//    val seq = "==>\\forall v \\forall m \\forall T (9>0&1>0&T>0&m < -(9/1)^(1/2)&v>-(9/1)^(1/2)&v < 0->v>=m)".asSequent
//    processEntry(10, SOSSolve.preferAuxiliaryVariableOrdering, 120)(("preferAuxiliary", seq, seq))
//    processEntry(10, SOSSolve.deferAuxiliaryVariableOrdering, 120)(("deferAuxiliary", seq, seq))
//    processEntry(10, SOSSolve.lexicographicVariableOrdering, 120)(("lexicographic", seq, seq))

    withTemporaryConfig(Map(Configuration.Keys.DEBUG -> "false")){
      QELogger.processLog(QELogger.parseStr, processEntry(10, variableOrdering, logtimeout), logfilename)
    }
  }

}

/** Convert QE Logs to Isabelle syntax */
@IgnoreInBuildTest
class ConvertQELogToIsabelle extends TacticTestBase with PrivateMethodTester {
  def paren(s: String) : String = "(" + s + ")"
  def printOp(op: String, left: String, right: String) : String = paren(left) + " " + op + " " + paren(right)
  def printOp(op: String, child: String) : String = op + paren(child)
  def printOp[A](f: A=>String, op: String, left: A, right: A) : String = printOp(op, f(left), f(right))
  def printOp[A](f: A=>String, op: String, child: A) : String = printOp(op, f(child))

  /* ugly, fully parenthesized and typed (except variables) Isabelle syntax */
  def subscript(x: String) : String = x.map("\\<^sub>" + _).mkString
  def variableToIsabelle(v: Variable, showType: Boolean) : String = v match {
    case BaseVariable(name, index, Real) =>
      val vString =
        name.replace("_", "\\<^sub>\\<p>") /* for /p/rivate */ +
          (index match {
            case None => ""
            case Some(i) => subscript(i.toString)
          })
      if (showType) paren(vString+"::real") else vString
    case _ => throw new IllegalArgumentException("variableToIsabelle: " + v)
  }
  case class ToIsabelleTermException(message: String) extends IllegalArgumentException(message)
  def toIsabelle(t: Term, typeReal: Boolean) : String = t match {
    case Plus(a, b) => printOp(toIsabelle(_:Term, typeReal), "+", a, b)
    case Minus(a, b) => printOp(toIsabelle(_:Term, typeReal), "-", a, b)
    case Times(a, b) => printOp(toIsabelle(_:Term, typeReal), "*", a, b)
    case Divide(a, b) =>
      if (typeReal) printOp(toIsabelle(_:Term, typeReal), "/", a, b)
      else
        throw ToIsabelleTermException("keymaerax_nonnatural_exponent")
    case Power(a, b) => printOp("^", toIsabelle(a, typeReal), toIsabelle(b, false))
    case Neg(a) => printOp(toIsabelle(_:Term, typeReal), "-", a)
    case Number(n) =>
      if (typeReal || (n.isValidInt && n.toIntExact >= 0))
        paren(n.toString + (if(typeReal) "::real" else "::nat"))
      else throw ToIsabelleTermException("keymaerax_nonnatural_number")
    case v : BaseVariable => if (typeReal) variableToIsabelle(v, false) else
      throw ToIsabelleTermException("keymaerax_variable_in_exponent")
    case v : DifferentialSymbol => toIsabelle(Differential(v.x), typeReal) : String
    case Differential(a) => printOp(toIsabelle(_:Term, typeReal), "(keymaerax_differential::real\\<Rightarrow>real)", a)
    case FuncOf(InterpretedSymbols.minF, Pair(a, b)) => "(min::real\\<Rightarrow>real\\<Rightarrow>real)"+paren(toIsabelle(a, typeReal))+paren(toIsabelle(b, typeReal))
    case FuncOf(InterpretedSymbols.maxF, Pair(a, b)) =>"(max::real\\<Rightarrow>real\\<Rightarrow>real)"+paren(toIsabelle(a, typeReal))+paren(toIsabelle(b, typeReal))
    case FuncOf(InterpretedSymbols.absF, a) =>"(abs::real\\<Rightarrow>real)"+paren(toIsabelle(a, typeReal))
    case _ => throw new IllegalArgumentException("toIsabelle(Term): " + t)
  }
  def toIsabelle(fml: Formula) : String = fml match {
    case True => "True"
    case False => "False"
    case Equal(a, b) => printOp(toIsabelle(_: Term, true), "=", a, b)
    case NotEqual(a, b) => printOp(toIsabelle(_: Term, true), "\\<noteq>", a, b)
    case GreaterEqual(a, b) => printOp(toIsabelle(_: Term, true), "\\<ge>", a, b)
    case Greater(a, b) => printOp(toIsabelle(_: Term, true), ">", a, b)
    case LessEqual(a, b) => printOp(toIsabelle(_: Term, true), "\\<le>", a, b)
    case Less(a, b) => printOp(toIsabelle(_: Term, true), "<", a, b)
    case Not(a) => printOp(toIsabelle(_:Formula), "\\<not>", a)
    case And(a, b) => printOp(toIsabelle(_:Formula), "\\<and>", a, b)
    case Or(a, b) => printOp(toIsabelle(_:Formula), "\\<or>", a, b)
    case Imply(a, b) => printOp(toIsabelle(_:Formula), "\\<longrightarrow>", a, b)
    case Equiv(a, b) => printOp(toIsabelle(_:Formula), "\\<longleftrightarrow>", a, b)
    case Forall(vs, a) => paren("\\<forall> " + vs.map(variableToIsabelle(_, true)).mkString(" ") + " . " + paren(toIsabelle(a)))
    case Exists(vs, a) => paren("\\<exists> " + vs.map(variableToIsabelle(_, true)).mkString(" ") + " . " + paren(toIsabelle(a)))
    case _ => throw new IllegalArgumentException("toIsabelle(Formula): " + fml)
  }
  def toIsabelle(filterFalse: Option[Int], entry: (String, Sequent, Sequent)) : String = entry match {
    case (s: String, _: Sequent, seq: Sequent) if (seq.ante.length == 0 && seq.succ.length == 1) =>
      val converted = try {
        s + "#" + toIsabelle(seq.succ(0)) + "\n"
      } catch {
        case ToIsabelleTermException(msg) => s + "#" + msg + "\n"
      }
      if (filterFalse.isDefined) {
        val qe = proveBy(seq, ?(QEX(None, filterFalse.map(Number(_)))))
        if (qe.subgoals.exists(_.succ.contains(False)))
          s + "#" + "keymaerax_qe_reduces_to_false\n"
        else converted
      } else converted
    case _ => throw new IllegalArgumentException("toIsabelle(logEntry)")
  }
  "toIsabelle" should "convert" in withMathematica { _ =>
    val fml = "(A>=0&ep>=0&1>=0&1>0&sbsc>0&ms>0&g>0&-1<=0&0<=1&v_1<=vdes&0<=Tw&Tw<=A&v_1^2-d^2<=2*(1*sbsc/ms)*(m-z)&d>=0&t>=0&v>=0&t<=ep&v_1>=0&0<=ep->(1*Tw/1-(ms*0+ms*g*0)-((v*(1-1)+1)*sbsc+0))/ms=0+(Tw/ms-1*sbsc/ms)*1|m-z<=(v_1^2-d^2)/(2*1*sbsc/ms)+(A/ms/(1*sbsc/ms)+1)*(A/ms/2*ep^2+ep*v_1)|em=1)".asFormula
    println(toIsabelle(fml))
  }

  "QE logs" should "convert to Isabelle" in withMathematica { _ =>
    val logPath = Configuration.path(Configuration.Keys.SOSSOLVE_LOG_PATH)
    val logfilename = logPath + Configuration(Configuration.Keys.SOSSOLVE_LOG_INPUT)
    val outfileName = logfilename + ".isabelle.txt"
    val outfile = new java.io.File(outfileName)
    val parent = outfile.getParentFile
    if (parent != null) parent.mkdirs()
    val fw0 = new FileWriter(outfile, false)
    fw0.write("")
    fw0.close()
    val fw = new FileWriter(outfile, true)
    var i = 0
    def writeToIsabelle(entry : (String, Sequent, Sequent)) : Unit = {
      i = i + 1
      println(i)
      fw.append(toIsabelle(Some(1), entry))
    }
    withTemporaryConfig(Map(Configuration.Keys.DEBUG -> "false")){
      QELogger.processLog(QELogger.parseStr, writeToIsabelle, logfilename)
    }
    fw.close()
  }

}
