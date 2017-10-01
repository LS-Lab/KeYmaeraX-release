package edu.cmu.cs.ls.keymaerax.btactics.coasterx

/** Command-line functionality of CoasterX, both for repeatability evaluation purposes and general usage
  * @author Brandon Bohrer */
object CoasterXMain {
  def proveComponent(name: String, doFormula:Boolean, doTactic:Boolean, doStats:Boolean, numRuns:Int):Unit = {

  }

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

  }

  def main(options:Map[Symbol,Any]):Unit = {
    options('coasterxMode) match {
      case "component" =>
        val componentName:String = options('in).asInstanceOf[String]
        val doFormula = options.get('doFormula).nonEmpty
        val doTactic = options.get('doTactic).nonEmpty
        val doStats = options.get('doStats).nonEmpty
        val numRuns = options.getOrElse('numRuns, "1").asInstanceOf[String].toInt
        proveComponent(componentName, doFormula = doFormula, doTactic = doTactic, doStats = doStats, numRuns)
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
  }
}
