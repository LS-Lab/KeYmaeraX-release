package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.File
import edu.cmu.cs.ls.keymaerax.core.{Formula, Number, StaticSemantics}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

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

  val DEBUG = false
  // @TODO: Implement
  val tacticMap:Map[String,BelleExpr] = Map(
    "q1" -> {
      TactixLibrary.unfoldProgramNormalize &
      dC("dx=-(cy()-y)/r()".asFormula)(1) <(nil, dI()(1)) &
      dC("dy=(cx()-x)/r()".asFormula)(1) <(nil, dI()(1)) &
      dC("v^2=v0()^2+2*yGlobal()*g()-2*y*g()".asFormula)( 1)  <(nil, dI()(1)) &
      dC("v>0".asFormula)(1) <(nil, ODE(1)) &
      dC("(x-cx())^2 + (y-cy())^2 = r()^2".asFormula)(1) <(nil, ODE(1)) &
      ODE(1)
    },
    "q2" -> {
      TactixLibrary.unfoldProgramNormalize
      dC(s"dx^2 + dy^2 = 1".asFormula)(1)    <(nil, dI()(1)) &
      dC(s"dx=(y-cy())/r()".asFormula)(1) <(nil, dI()(1)) &
      dC(s"dy=-(x-cx())/r()".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"v^2=v0()^2+2*yGlobal()*g()-2*y*g()".asFormula)('R) <(nil, dI()(1)) &
      dC(s"(v^2)/2 > g()*(y1() - y)".asFormula)(1) <(nil, dI()(1)) &
      dC("v>0".asFormula)('R) &
      nil <(nil, dC("2*v!=0".asFormula)(1)) &
      nil <(nil, dG(s"{a'=((dy*g())/(2*v))*a+0}".asDifferentialProgram, Some("a^2*v=1".asFormula))(1), nil) &
      nil <(nil, existsR("(1/v)^(1/2)".asTerm)(1), nil) &
      nil <(nil, dI()(1), nil) &
      nil <(nil, ODE(1)) &
      ODE(1)

    },
    "q3" -> {
      dC("dx=-(y-cy())/r()".asFormula)(1) <(nil, dI()(1)) &
        dC("dy=(x-cx())/r()".asFormula)(1) <(nil, dI()(1)) &
        dC("v^2=v0()^2+2*yGlobal()*g()-2*y*g()".asFormula)( 1)  <(nil, dI()(1)) &
        dC("v>0".asFormula)(1) <(nil, ODE(1)) &
        dC("(x-cx())^2 + (y-cy())^2 = r()^2".asFormula)(1) <(nil, ODE(1)) &
        ODE(1)
    },
    "q4" -> {
      dC(s"dx=-(y-cy())/r()".asFormula)(1)  <(nil, dI()(1)) &
      dC(s"dy=(x-cx())/r()".asFormula)( 1)  <(nil, ODE(1)) &
      dC(s"cx()<=x".asFormula)(1)  <(nil, ODE(1)) &
      dC(s"g() > 0".asFormula)(1) <(nil, dI()(1)) &
      dC(s"v^2=v0()^2+2*yGlobal()*g()-2*y*g()".asFormula)(1) <(nil, dI()(1)) &
      dC(s"(cx()-x)^2+(cy()-y)^2=r()^2".asFormula)(1) <(nil, DebuggingTactics.debug("This dI is slow", doPrint = DEBUG) & dI()(1)) &
      dC(s"y < cy()".asFormula)(1) <(nil,
        dC(s"2*(y-cy())*r()!=0".asFormula)(1)  <(
          dG(s"{a'=(cx()-x)*v/(2*(y-cy())*r())*a+0}".asDifferentialProgram, Some(s"a^2*(y-cy())=-1".asFormula))(1) &
            existsR(s"(-1/(y-cy()))^(1/2)".asTerm)(1) &
            ODE(1),
          ODE(1)
        )
      ) &
      dC(s"(v^2)/2 > g()*(y1() - y)".asFormula)(1) <(nil, ODE(1)) &
      dC(s"v>0".asFormula)(1)  <(nil,
        dC(s"2*v!=0".asFormula)(1)  <(
          dG(s"{a'=((dy*g())/(2*v))*a+0}".asDifferentialProgram, Some("a^2*v=1".asFormula))(1) &
            existsR("(1/v)^(1/2)".asTerm)(1) &
            dI()(1),
          ODE(1)
        )
      ) &
      ODE(1)
    },
    //@TODO: Replace with "master" and see what happens
    "straight" -> {
      solve(1) & allR(1) & implyR(1) & implyR(1) &
      implyL(-2)  <(
        hideR(1) & QE,
        master()
      )
    }
  )

  def doStats(name:String, f:()=>ProvableSig, doFormula:Boolean, doTactic:Boolean, willDoStats:Boolean, numRuns:Int):Unit = {
    var res:Option[ProvableSig] = None
    var allTimes:List[Double] = List()
    for(i <- 0 until numRuns) {
      allTimes = timeSecs({case () => res = Some(f())}) :: allTimes
    }
    val steps = res.get.steps
    val vars = countVars(res.get.conclusion.toFormula)
    val size = KeYmaeraXPrettyPrinter.stringify(res.get.conclusion.toFormula).length/1000.0
    println("**** Test results for component " + name + "****")
    if(willDoStats) {
      println("All Times (secs): " + allTimes)
      println("Average time" + mean(allTimes))
      println("Proof steps: " + steps)
      println("Total vars: " + vars)
      println("Fml size (KB): " + size)
    }
    //@TODO: Actually use these in the prover implementation
    if(doTactic) {
      println("Component tactic: " + tacticMap(name))
    }
    if(doFormula) {
      println("Component formula (sequent): " + res.get.conclusion)
    }
  }
}
