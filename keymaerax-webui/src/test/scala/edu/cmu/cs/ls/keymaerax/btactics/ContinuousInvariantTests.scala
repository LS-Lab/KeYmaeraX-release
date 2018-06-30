package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.DifferentialTactics.{diffCut, diffWeaken}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.{fail, _}
import edu.cmu.cs.ls.keymaerax.core._
import testHelper.KeYmaeraXTestTags.{IgnoreInBuildTest, SlowTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.{MathematicaComputationAbortedException, ToolException}
import testHelper.CustomAssertions._
import testHelper.KeYmaeraXTestTags

import scala.collection.immutable.IndexedSeq
import org.scalatest.LoneElement._
import org.scalatest.prop.TableDrivenPropertyChecks.forEvery
import org.scalatest.prop.Tables._
import org.scalatest.concurrent.Timeouts
import org.scalatest.time.SpanSugar._

/**
 * Continuous invariant generation tests.
 */
class ContinuousInvariantTests extends TacticTestBase with Timeouts {
  val randomTrials = 500
  val randomComplexity = 6
  val rand = new RandomFormula()

  "Continuous invariant generation" should "generate a simple invariant" in withMathematica { _ =>
    val problem = "x>-1 & -2*x > 1 & -2*y > 1 & y>=-1 ==> [{x'=y,y'=x^5 - x*y}] x+y<=1".asSequent

    InvariantGenerator.differentialInvariantCandidates(problem, SuccPos(0)) should contain theSameElementsInOrderAs(
      "x>-1".asFormula::"-2*x>1".asFormula::"-2*y>1".asFormula::"y>=-1".asFormula::
        "x^5<=(x+4*x^3)*y".asFormula::"y<=0".asFormula :: Nil)
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
        val Imply(assumptions, succFml@Box(ode@ODESystem(_, q), _)) = model

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
    Configuration.set(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT, "-1", saveToFile = false)

    val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
      getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
    val annotatedInvariants: ConfigurableGenerator[Formula] = TactixLibrary.invGenerator match {
      case gen: ConfigurableGenerator[Formula] => gen
    }

    forEvery(Table(("Name", "Model"),
      entries.map(e => e.name -> e.model):_*).
      filter({ case (_, Imply(_, Box(_: ODESystem, _))) => true case _ => false })) {
      (name, model) =>
        println("\n" + name)
        val Imply(_, Box(ode@ODESystem(_, q), _)) = model
        annotatedInvariants.products.get(ode) match {
          case Some(invs) => tool.lzzCheck(ode, invs.reduce(And)) shouldBe true
          case None => // no invariant to fast-check
        }
        println(name + " done")
    }
  }

  it should "consider constants when fast-checking invariants with LZZ" in withMathematica { tool =>
    Configuration.set(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT, "5", saveToFile = false)
    val entry = KeYmaeraXArchiveParser.getEntry("STTT Tutorial: Example 9a", io.Source.fromInputStream(
      getClass.getResourceAsStream("/keymaerax-projects/benchmarks/basic.kyx")).mkString).head

    a [MathematicaComputationAbortedException] should be thrownBy tool.lzzCheck(
      "{ x' = v, v' = -Kp()*(x-xr()) - Kd()*v }".asProgram.asInstanceOf[ODESystem],
      "5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()".asFormula)

    tool.lzzCheck(
      "{ x' = v, v' = -Kp()*(x-xr()) - Kd()*v }".asProgram.asInstanceOf[ODESystem],
      "c()>0 & Kp()=2 & Kd()=3 & 5/4*(x-xr())^2 + (x-xr())*v/2 + v^2/4 < c()".asFormula) shouldBe true

    proveBy(entry.model.asInstanceOf[Formula], implyR(1) & dI()(1)) shouldBe 'proved
  }

  it should "produce invariants that are provable with ODE" taggedAs SlowTest in withMathematica { _ =>
    Configuration.set(Configuration.Keys.ODE_TIMEOUT_FINALQE, "300", saveToFile = false)
    Configuration.set(Configuration.Keys.PEGASUS_INVCHECK_TIMEOUT, "60", saveToFile = false)

    val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
      getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
    forEvery(Table(("Name", "Model", "Tactic"), entries.
      filter(e => e.tactics.nonEmpty).
      map(e => (e.name, e.model, e.tactics.headOption.getOrElse("" -> TactixLibrary.auto)._2)): _*)) {
      (name, model, tactic) =>
        println("\n" + name + " with " + BellePrettyPrinter(tactic))
        failAfter(5 minutes) {
          proveBy(model.asInstanceOf[Formula], tactic) shouldBe 'proved
        }
        println(name + " done")
    }
  }

  it should "standalone test of pegasus + odeInvariant only" taggedAs SlowTest in withMathematica { _ =>
    Configuration.set(Configuration.Keys.ODE_TIMEOUT_FINALQE, "180", saveToFile = false)
    Configuration.set(Configuration.Keys.PEGASUS_INVGEN_TIMEOUT, "60", saveToFile = false)

    val entries = KeYmaeraXArchiveParser.parse(io.Source.fromInputStream(
      getClass.getResourceAsStream("/keymaerax-projects/benchmarks/nonlinear.kyx")).mkString)
    var generated = 0
    var success = 0
    var total = 0
    forEvery(Table(("Name", "Model", "Tactic"), entries.
      map(e => (e.name, e.model, e.tactics)): _*)) {
      (name, model, _) =>
        println("\n" + name + " " + model)
        try {
          failAfter(3 minutes) {
            total+=1
            try {
              val pr = proveBy(model.asInstanceOf[Formula], implyR(1) & odeInvariantAuto(1) & done)
              success+=1
              generated += 1
            }
            catch {
              case ex: BelleThrowable =>
                if(ex.getMessage.contains("Pegasus failed to generate an invariant"))
                  println("Pegasus did not generate an invariant")
                else {
                  println(ex.getMessage)
                  generated += 1
                }
            }
          }
          println(name + " done.")
          println("Total: "+total+" Generated: "+generated+" Proved: ",success)
        }
        catch {
          case ex: IllegalArgumentException =>
            println(name + " not of expected form")
        }
    }
    println("Total: "+total+" Generated: "+generated+" Proved: ",success)
  }

}
