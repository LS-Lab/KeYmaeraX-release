package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXTestLib.{CoasterStats, ComponentStats, countVars, doStats}
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.{CoasterXParser, CoasterXProver, CoasterXSpec, CoasterXTestLib}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.launcher._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.Mathematica

/** Command-line functionality of CoasterX, both for repeatability evaluation purposes and general usage
 *
  * @author Brandon Bohrer */
object CoasterXMain  {
  def withMathematica(testcode: Mathematica => Any) {
    val provider = new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  def proveComponent(name: String, doFormula:Boolean, doTactic:Boolean, willDoStats:Boolean, numRuns:Int):Unit = {
    val spec = new CoasterXSpec(1.0)
    // file shouldnt matter
    val straightLine = "([(0, 100), (1000, 100)], [('straight', (None,), None), ('straight', ((0, 500, 1000, 500),), 0.0)], 1.0, (0, 0, 0, 0))"
    val file = straightLine
    val parsed = CoasterXParser.parseFile(file).get
    val (align,alignFml) = spec.prepareFile(parsed)
    val env = spec.envelope(align)
    val specc = spec.fromAligned((align,alignFml),env)
    val specStr = KeYmaeraXPrettyPrinter.stringify(specc)
    val specLenKB = specStr.length / 1000.0
    val nVars = countVars(specc)

    val prFast = new CoasterXProver(spec,env, reuseComponents = false)
    val components =
      name match {
        case "straight" => List(("Straight", () => prFast.straightProof))
        case "q1" => List(("Q1", () => prFast.arcProofQ1))
        case "q2" => List(("Q2", () => prFast.arcProofQ2))
        case "q3" => List(("Q3", () => prFast.arcProofQ3))
        case "q4" => List(("Q4", () => prFast.arcProofQ4))
        case "all" =>
          List(("Straight", () => prFast.straightProof),
            ("Q1", () => prFast.arcProofQ1),
            ("Q2", () => prFast.arcProofQ2),
            ("Q3", () => prFast.arcProofQ3),
            ("Q4", () => prFast.arcProofQ4))
        case _ =>
          println("USAGE: You did not specify a valid component name after -component. Please specify q1,q2,q3,q4,straight, or all.")
          return
      }
    components.foreach({case (x,y) => doStats(x,y, doFormula, doTactic, willDoStats, numRuns)})
  }

  // @TODO: Check whether components have been proven yet, if not then prove them before timing the coaster
  def proveCoaster(filename:String ,
                   doFormula: Boolean,
                   doStats: Boolean,
                   compareReuse:Boolean,
                   feetPerUnit:Double,
                   velocity: Option[Double],
                   numRuns:Int):Unit = {
    val fileContents = scala.io.Source.fromFile(filename).getLines().mkString("\n")
    val proof = CoasterXTestLib.prover(fileContents, "Coaster From Command Line", doFast = !compareReuse,NUM_RUNS = numRuns, feetPerUnit = feetPerUnit, velocity = velocity,
      doFormula = doFormula,  doStats = doStats)
    assert(proof.isProved, "CoasterX prover did not prove model :'( ")
  }

  def printTable2():Unit = {
    val numRuns = 10
    val coastersToTest:List[(String, Double)] = List(
      (CoasterXTestLib.exampleFile1, 1.0),
      (CoasterXTestLib.byrc, 0.08333333333),
      (CoasterXTestLib.lilPhantom, 1.0),
      (CoasterXTestLib.phantomsRevenge, 2.0),
      (CoasterXTestLib.elToro,1.0)
    )
    var coasterStats:List[CoasterStats] = Nil
    var componentStats:List[ComponentStats] = Nil

    coastersToTest.foreach { case (coast:String, feetPerUnit) =>
      val fileContents = scala.io.Source.fromFile(coast).getLines().mkString("\n")
      val proof = CoasterXTestLib.prover(fileContents, "Coaster From Command Line", doFast = false, NUM_RUNS = numRuns,
        feetPerUnit = feetPerUnit, velocity = None, doFormula = true, doStats = true, Some({case cs => coasterStats = cs :: coasterStats; cs.proof}))
      assert(proof.isProved, "CoasterX prover did not prove model :'( ")
    }
    val spec = new CoasterXSpec(1.0)
    val parsed = CoasterXParser.parseFile(CoasterXTestLib.straightLine).get
    val (align,alignFml) = spec.prepareFile(parsed)
    val env = spec.envelope(align)
    val prFast = new CoasterXProver(spec,env, reuseComponents = false)
    val componentsToTest:List[(String, (() => ProvableSig))] = List(
      ("straight", () => prFast.straightProof),
      ("Q1", () => prFast.arcProofQ1),
      ("Q2", () => prFast.arcProofQ2),
      ("Q3", () => prFast.arcProofQ3),
      ("Q4", () => prFast.arcProofQ4)
    )
    componentsToTest.foreach({case (name, f) =>
        doStats(name, f, doFormula = true, doTactic = true, willDoStats = true, numRuns = numRuns, Some({case cs => componentStats = cs :: componentStats}))
    })

    // Begin printing
    println("Model\tSections\tVars\tTime(s)\tTime-NoReuse(s)\tSpeedup(%)\tSteps\tSize(KB)")
    coasterStats.foreach{case CoasterStats(name,env,nSections,nVars,fastTimes,fastMean,slowTimes,slowMean,stepsFast,stepsSlow,speedupPercent,proof,size) =>
      println(s"$name\t$nSections\t$nVars\t$fastMean\t$slowMean\t$speedupPercent\t$stepsFast\t$size")
    }
    println("")
    println("Comp.\tVars\tTime(s)\tSteps\tSize(KB)")
    componentStats.foreach{case ComponentStats(name,alltimes,meantime,steps,vars,size,tac,seq) =>
      println(s"$name\t$vars\t$meantime\t$steps\t$size")
    }
  }

  def main(options:Map[Symbol,Any]):Unit = {
    withMathematica(qeTool => {
    options('coasterxMode) match {
      case "component" =>
        val componentName:String = options('in).asInstanceOf[String]
        val doFormula = options.get('doFormula).nonEmpty
        val doTactic = options.get('doTactic).nonEmpty
        val doStats = options.get('doStats).nonEmpty
        val numRuns = options.getOrElse('numRuns, "1").asInstanceOf[String].toInt
        proveComponent(componentName, doFormula = doFormula, doTactic = doTactic, willDoStats = doStats, numRuns)
      case "coaster" =>
        val fileName:String = options('in).asInstanceOf[String]
        val doFormula = options.get('doFormula).nonEmpty
        val doStats = options.get('doStats).nonEmpty
        val feetPerUnit = options('feetPerUnit).asInstanceOf[String]
        val compareReuse = options.get('compareReuse).nonEmpty
        val velocity = options.get('velocity).asInstanceOf[Option[String]]
        val numRuns = options.getOrElse('numRuns, "1").asInstanceOf[String].toInt
        proveCoaster(fileName, doFormula = doFormula, doStats = doStats, compareReuse = compareReuse, feetPerUnit.toDouble, velocity.map(_.toDouble), numRuns)
      case "table2" => printTable2()
    }
  })
  }
}
