package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.{AnnotationProofHint, PegasusProofHint}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.SlowTest

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaComputationAbortedException

import scala.collection.immutable.IndexedSeq
import org.scalatest.prop.TableDrivenPropertyChecks.forEvery
import org.scalatest.prop.Tables._
import org.scalatest.concurrent.Timeouts
import org.scalatest.time.SpanSugar._
import org.scalatest.LoneElement._

/**
 * Continuous invariant generation tests.
 */
class ContinuousInvariantTests extends TacticTestBase with Timeouts {
  val randomTrials = 500
  val randomComplexity = 6
  val rand = new RandomFormula()

  "Continuous invariant lookup" should "provide a simple invariant from annotations" in {
    val problem = "x>2 ==> [{x'=2}@invariant(x>1)]x>0".asSequent
    TactixLibrary.invGenerator(problem, SuccPos(0)) should contain theSameElementsInOrderAs(
      ("x>1".asFormula, Some(AnnotationProofHint(tryHard = true))) :: Nil)
  }

  it should "provide a conditional invariant from annotations" in {
    val problem = "x>2 ==> [{x'=2}@invariant(x>1, (x'=2 -> x>2), (x'=3 -> x>5))]x>0".asSequent
    TactixLibrary.invGenerator(problem, SuccPos(0)) should contain theSameElementsInOrderAs(
      ("x>1".asFormula, Some(AnnotationProofHint(tryHard = true))) :: ("x>2".asFormula, Some(AnnotationProofHint(tryHard = true))) :: Nil)
  }

  "Continuous invariant generation" should "generate a simple invariant" in withMathematica { _ =>
    val problem = "x>-1 & -2*x > 1 & -2*y > 1 & y>=-1 ==> [{x'=y,y'=x^5 - x*y}] x+y<=1".asSequent

    InvariantGenerator.differentialInvariantCandidates(problem, SuccPos(0)) should contain theSameElementsInOrderAs(
      ("x>-1".asFormula, None) :: ("-2*x>1".asFormula, None) :: ("-2*y>1".asFormula, None) ::
        ("y>=-1".asFormula, None) :: ("x^5<=(x+4*x^3)*y".asFormula, Some(PegasusProofHint(isInvariant = true, None))) ::
        ("y<=0".asFormula, Some(PegasusProofHint(isInvariant = true, None))) :: Nil)
  }

  it should "generate invariants for nonlinear benchmarks with Pegasus" taggedAs SlowTest in withMathematica { _ =>
    val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
      getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
    val annotatedInvariants: ConfigurableGenerator[Formula] = TactixLibrary.invGenerator match {
      case gen: ConfigurableGenerator[Formula] => gen
    }
    TactixLibrary.invGenerator = FixedGenerator(Nil)
    forEvery(Table(("Name", "Model"),
      entries.map(e => e.name -> e.model):_*).
      filter({ case (_, Imply(_, Box(_: ODESystem, _))) => true case _ => false })) {
      (name, model) =>
        println("\n" + name)
        val Imply(assumptions, succFml@Box(ode@ODESystem(_, _), _)) = model

        //@note the annotations in nonlinear.kyx are produced by Pegasus
        val invariants = InvariantGenerator.pegasusInvariants(
          Sequent(IndexedSeq(assumptions), IndexedSeq(succFml)), SuccPos(0))

        annotatedInvariants.products.get(ode) match {
          case Some(invs) =>
            invariants should contain theSameElementsInOrderAs invs
          case None =>
            //@note invariant generator did not produce an invariant before, not expected to produce one now. Test will
            // fail if invariant generator improves and finds an invariant.
            // In that case, add annotation to nonlinear.kyx.
            invariants shouldBe empty
        }
        println(name + " done")
    }
  }

  it should "fast-check invariants with LZZ" taggedAs SlowTest in withMathematica { tool =>
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT -> "-1")) {
      val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
        getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
      val annotatedInvariants: ConfigurableGenerator[Formula] = TactixLibrary.invGenerator match {
        case gen: ConfigurableGenerator[Formula] => gen
      }

      forEvery(Table(("Name", "Model"),
        entries.map(e => e.name -> e.model): _*).
        filter({ case (_, Imply(_, Box(_: ODESystem, _))) => true case _ => false })) {
        (name, model) =>
          println("\n" + name)
          val Imply(_, Box(ode@ODESystem(_, _), _)) = model
          annotatedInvariants.products.get(ode) match {
            case Some(invs) => tool.lzzCheck(ode, invs.reduce(And)) shouldBe true
            case None => // no invariant to fast-check
          }
          println(name + " done")
      }
    }
  }

  it should "consider constants when fast-checking invariants with LZZ" in withMathematica { tool =>
    withTemporaryConfig(Map(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT -> "5")) {
      val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial: Example 9a", io.Source.fromInputStream(
        getClass.getResourceAsStream("/keymaerax-projects/benchmarks/basic.kyx")).mkString).head

      a[MathematicaComputationAbortedException] should be thrownBy tool.lzzCheck(
        "{ x' = v, v' = -Kp()*(x-xr()) - Kd()*v }".asProgram.asInstanceOf[ODESystem],
        "5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()".asFormula)

      tool.lzzCheck(
        "{ x' = v, v' = -Kp()*(x-xr()) - Kd()*v }".asProgram.asInstanceOf[ODESystem],
        "c()>0 & Kp()=2 & Kd()=3 & 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()".asFormula) shouldBe true

      proveBy(entry.model.asInstanceOf[Formula], implyR(1) & dI()(1)) shouldBe 'proved
    }
  }

  it should "produce invariants that are provable with ODE" taggedAs SlowTest in withMathematica { _ =>
    withTemporaryConfig(Map(
        Configuration.Keys.ODE_TIMEOUT_FINALQE -> "300",
        Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT -> "60")) {
      val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
        getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
      forEvery(Table(("Name", "Model", "Tactic"), entries.
        filter(e => e.tactics.nonEmpty).
        map(e => (e.name, e.model, e.tactics.headOption.getOrElse("", BellePrettyPrinter(TactixLibrary.auto), TactixLibrary.auto)._3)): _*)) {
        (name, model, tactic) =>
          println("\n" + name + " with " + BellePrettyPrinter(tactic))
          failAfter(5 minutes) {
            proveBy(model.asInstanceOf[Formula], tactic) shouldBe 'proved
          }
          println(name + " done")
      }
    }
  }

  "Refute ODE" should "find a simple counterexample" in withMathematica { tool =>
    val cex = tool.refuteODE(
      "{x'=1}".asProgram.asInstanceOf[ODESystem],
      "x=1".asFormula :: Nil,
      "x=1".asFormula)
    cex shouldBe Some(Map("x".asVariable -> "1".asTerm))
  }

  it should "refute parametric ODEs" in withMathematica { tool =>
    val cex = tool.refuteODE(
      "{x'=v,v'=A()}".asProgram.asInstanceOf[ODESystem],
      "A()=1 & x=1".asFormula :: Nil,
      "x=1".asFormula)
    val aFunc = "A()".asTerm.asInstanceOf[FuncOf]

    cex shouldBe Some(Map("x".asVariable -> "1.0".asTerm,aFunc.func -> "1.0".asTerm,"v".asVariable -> "-1.0".asTerm))
  }

  it should "not refute true invariants" in withMathematica { tool =>
    val cex = tool.refuteODE(
      "{x'=y,y'=-x}".asProgram.asInstanceOf[ODESystem],
      "r()=s()&x^2+y^2=r()^2".asFormula :: Nil,
      "x^2+y^2=s()^2".asFormula)

    cex shouldBe None
  }

  it should "Fail for non-FOL assumptions" in withMathematica { tool =>

    a [IllegalArgumentException] should be thrownBy
      tool.refuteODE(
        "{x'=y,y'=-x}".asProgram.asInstanceOf[ODESystem],
        "r()=s()&x^2+y^2=r()^2".asFormula :: "[x:=x+1;]x=1".asFormula :: Nil,
        "x^2+y^2=s()^2".asFormula)
  }

  it should "refute as a tactic" in withMathematica { _ =>
    val fml = "x^2+y^2=r()^2 -> [{x'=y,y'=A()*x}] x^2+y^2=r()^2".asFormula
    proveBy(fml, implyR(1) & DifferentialTactics.cexCheck(1)).subgoals.loneElement shouldBe "==> false".asSequent
  }


//  it should "standalone test of pegasus + odeInvariant only" taggedAs SlowTest in withMathematica { _ =>
//    Configuration.set(Configuration.Keys.ODE_TIMEOUT_FINALQE, "180", saveToFile = false)
//    Configuration.set(Configuration.Keys.PEGASUS_INVGEN_TIMEOUT, "60", saveToFile = false)
//
//    val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
//      getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
//    var generated = 0
//    var success = 0
//    var total = 0
//    forEvery(Table(("Name", "Model", "Tactic"), entries.
//      map(e => (e.name, e.model, e.tactics)): _*)) {
//      (name, model, _) =>
//        println("\n" + name + " " + model)
//        try {
//          failAfter(3 minutes) {
//            total+=1
//            try {
//              val pr = proveBy(model.asInstanceOf[Formula], implyR(1) & odeInvariantAuto(1) & done)
//              success+=1
//              generated += 1
//            }
//            catch {
//              case ex: BelleThrowable =>
//                if(ex.getMessage.contains("Pegasus failed to generate an invariant"))
//                  println("Pegasus did not generate an invariant")
//                else {
//                  println(ex.getMessage)
//                  generated += 1
//                }
//            }
//          }
//          println(name + " done.")
//          println("Total: "+total+" Generated: "+generated+" Proved: ",success)
//        }
//        catch {
//          case ex: IllegalArgumentException =>
//            println(name + " not of expected form")
//        }
//    }
//    println("Total: "+total+" Generated: "+generated+" Proved: ",success)
//  }

}
