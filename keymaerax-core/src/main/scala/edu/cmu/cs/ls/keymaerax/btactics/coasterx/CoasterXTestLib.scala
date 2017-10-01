package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.File
import edu.cmu.cs.ls.keymaerax.core.{Formula, Number, StaticSemantics}

object CoasterXTestLib {
  def timeSecs[T](f:(() => T)):Double = {
    val early = System.currentTimeMillis()
    val res = f()
    val late = System.currentTimeMillis()
    (late - early) / 1000.0
  }

  def countVars(fml:Formula):Int = {
    val ss = StaticSemantics(fml)
    val theSet = (ss.bv ++ ss.fv).toSet ++ StaticSemantics.symbols(fml)
    theSet.size
  }

  def mean(xs:List[Double]):Double = {
    xs match {
      case Nil => 0.0
      case _ => (xs.foldLeft(0.0){(x,y) => x+y})/xs.length
    }
  }

  def setVelocity(f:File, v:Double):File = {
    val (w,x,_y,z) = f
    (w,x,Number(v),z)
  }

  // feetPerUnit = feetPerUnit, velocity = velocity, doFormula = doFormula, doTactic = doTactic, doStats = doStats)
  def prover(file:String, name:String, doFast:Boolean = false, NUM_RUNS:Int = 1, feetPerUnit:Double,
             velocity:Option[Double], doFormula:Boolean, doStats:Boolean):ProvableSig = {
    val spec = new CoasterXSpec(feetPerUnit)
    val parsedRaw = CoasterXParser.parseFile(file).get
    val parsed =
      velocity match {
        case Some(vFeetPerSecond) => setVelocity(parsedRaw, vFeetPerSecond/feetPerUnit)
        case None => parsedRaw
      }
    val (align,alignFml) = spec.prepareFile(parsed)
    val env = spec.envelope(align)
    val specc = spec.fromAligned((align,alignFml),env)
    val specStr = KeYmaeraXPrettyPrinter.stringify(specc)
    val specLenKB = specStr.length / 1000.0
    val nSections = spec.countSections(align)
    val nVars = countVars(specc)

    val prFast = new CoasterXProver(spec,env, reuseComponents = true)
    val prSlo = new CoasterXProver(spec,env, reuseComponents = false)

    var resFast:Option[ProvableSig] = None
    var resSlo:Option[ProvableSig] = None
    var sloTimes:List[Double] = Nil
    var fastTimes:List[Double] = Nil
    for(i <- 0 until NUM_RUNS) {
      fastTimes = timeSecs { case () => resFast = Some(prFast(file)) } :: fastTimes
      prFast.resetLemmaDB()
      if(!doFast){
        sloTimes = timeSecs { case () => resSlo = Some(prSlo(file)) } :: sloTimes
        prSlo.resetLemmaDB()
      }
    }

    val fastMean = mean(fastTimes)
    val sloMean = mean(sloTimes)
    val percentDiffAvg = ((sloMean-fastMean)/fastMean)*100.0
    val speedUpText =
      if(doFast) {
        "Running tests with component reuse only, no comparison of component reuse speedup"
      }
      else if(percentDiffAvg > 0) {
        s"Component Reuse Speedup (i.e. (hi-lo)/lo in %): $percentDiffAvg"
      } else {
        s"Component Reuse Slowdown (i.e. (hi-lo)/lo in %): $percentDiffAvg"
      }
    println("********** TEST RESULTS FOR " + name + " ***************")
    env.printLoudly()
    if(doStats) {
      println("Number of track section in design: " + nSections)
      println("Total #variables in formula: " + nVars)
      println("All Times with Reuse (seconds): " + fastTimes)
      println("Avg Time with Reuse (seconds): " + fastMean)
      println("All Times without Reuse (seconds): " + sloTimes)
      println("Avg Time without Reuse (seconds): " + sloMean)
      println("Number of proof steps with Reuse: " + resFast.get.steps)
      println("Number of proof steps without Reuse: " + resSlo.getOrElse(resFast.get).steps)
      println(speedUpText)
    }
    resFast.get
  }

  def doStats(name:String, f:()=>ProvableSig) = {
    var res:Option[ProvableSig] = None
    val theTime = timeSecs({case () => res = Some(f())})
    val steps = res.get.steps
    val vars = countVars(res.get.conclusion.toFormula)
    val size = KeYmaeraXPrettyPrinter.stringify(res.get.conclusion.toFormula).length/1000.0
    println("**** Stats for " + name + "****")
    println("Time (secs): " + theTime)
    println("Proof steps: " + steps)
    println("Total vars: " + vars)
    println("Fml size: " + size)
  }
}
