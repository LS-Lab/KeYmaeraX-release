package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.{QEFileLogListener, QELogListener, StopwatchListener}
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleInterpreter, DependentTactic, Interpreter, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXTestLib.{CoasterStats, ComponentStats, countVars, doStats}
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.{CoasterXParser, CoasterXProver, CoasterXSpec, CoasterXTestLib}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.launcher._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.Mathematica
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.hydra.HyDRAInitializer._
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DBAbstractionObj, HyDRAInitializer, StringToVersion}
import edu.cmu.cs.ls.keymaerax.launcher.KeYmaeraX.shutdownProver
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory

import scala.collection.immutable.Nil

/** Command-line functionality of CoasterX, both for repeatability evaluation purposes and general usage
 *
  * @author Brandon Bohrer */
object CoasterXMain {
  private type OptionMap = Map[Symbol, Any]
  private var interpreters: List[Interpreter] = _

  private val LOG_EARLIEST_QE = Configuration(Configuration.Keys.LOG_ALL_FO) == "true"
  private val LOG_QE = Configuration(Configuration.Keys.LOG_QE) == "true"
  private val LOG_QE_DURATION = Configuration(Configuration.Keys.LOG_QE_DURATION) == "true"

  protected val qeLogPath: String = Configuration.path(Configuration.Keys.QE_LOG_PATH)
  private val allPotentialQEListener = new QEFileLogListener(qeLogPath + "wantqe.txt", (p, _) => { p.subgoals.size == 1 && p.subgoals.head.isFOL })
    private val qeListener = new QEFileLogListener(qeLogPath + "haveqe.txt", (_, t) => t match { case DependentTactic("rcf") => true case _ => false })
    protected val qeDurationListener = new StopwatchListener((_, t) => t match {
    case DependentTactic("QE") => true
    case DependentTactic("smartQE") => true
    case _ => false
  })

  protected def registerInterpreter[T <: Interpreter](i: T): T = {
    interpreters = interpreters :+ i
    i
  }

  def beforeStuff = {
    interpreters = Nil
    val listeners = (if (LOG_QE) qeListener::Nil else Nil) ++
      (if (LOG_EARLIEST_QE) allPotentialQEListener::Nil else Nil) ++
      (if (LOG_QE_DURATION) qeDurationListener::Nil else Nil)
    BelleInterpreter.setInterpreter(registerInterpreter(SequentialInterpreter(listeners)))
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXNoContractPrettyPrinter)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
    ToolProvider.setProvider(new NoneToolProvider())
  }

  var haveStuffed = false
  def withMathematica(testcode: Mathematica => Any) {
    if(!haveStuffed){ beforeStuff ; haveStuffed=true}
    val provider = new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    testcode(provider.tool())
  }

  def proveComponent(name: String, doFormula:Boolean, doTactic:Boolean, willDoStats:Boolean, numRuns:Int, debugLevel:Int):Unit = {
    val spec = new CoasterXSpec(1.0, debugLevel)
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

    val prFast = new CoasterXProver(spec,env, reuseComponents = false, debugLevel = debugLevel, useNaive = false)
    val components =
      name match {
        case "lineup" => List(("lineup", () => prFast.straightProofUp))
          // @TODO Reverse-direction components
        case "linedown" => List(("linedown", () => prFast.straightProofDown))
        case "q1" => List(("Q1", () => prFast.arcProofQ1))
        case "q2" => List(("Q2", () => prFast.arcProofQ2))
        case "q3" => List(("Q3", () => prFast.arcProofQ3))
        case "q4" => List(("Q4", () => prFast.arcProofQ4))
        case "q1ccw" => List(("Q1ccw", () => prFast.arcProofQ1CCW))
        case "q2ccw" => List(("Q2ccw", () => prFast.arcProofQ2CCW))
        case "q3cw" => List(("Q3cw", () => prFast.arcProofQ3CW))
        case "q4cw" => List(("Q4cw", () => prFast.arcProofQ4CW))
        case "all" =>
          List(("lineup", () => prFast.straightProofUp),
            ("linedown", () => prFast.straightProofDown),
            ("Q1", () => prFast.arcProofQ1),
            ("Q2", () => prFast.arcProofQ2),
            ("Q3", () => prFast.arcProofQ3),
            ("Q4", () => prFast.arcProofQ4),
            ("Q1CCW", () => prFast.arcProofQ1CCW),
            ("Q2CCW", () => prFast.arcProofQ2CCW),
            ("Q3CW", () => prFast.arcProofQ3CW),
            ("Q4CW", () => prFast.arcProofQ4CW)
          )
        case _ =>
          println("USAGE: You did not specify a valid component name after -component. Please specify q1,q2,q3,q4,line, or all.")
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
                   numRuns:Int,
                   debugLevel:Int,
                   useNaive:Boolean):Unit = {
    val fileContents = scala.io.Source.fromFile(filename).getLines().mkString("\n")
    val proof = CoasterXTestLib.prover(fileContents, "Coaster From Command Line", doFast = !compareReuse,NUM_RUNS = numRuns, feetPerUnit = feetPerUnit, velocity = velocity,
      doFormula = doFormula,  doStats = doStats, debugLevel = debugLevel, useNaive = useNaive)
    assert(proof.isProved, "CoasterX prover did not prove model :'( ")
  }

  def printTable2(numRuns:Int, debugLevel:Int):Unit = {
    val coastersToTest:List[(String, Double,String)] = List(
      (CoasterXTestLib.exampleFile1, 1.0,    "top thrill drag "),
      (CoasterXTestLib.byrc, 0.08333333333,  "gregg backyard  "),
      (CoasterXTestLib.lilPhantom, 0.04177777777,      "lil' phantom    "),
      (CoasterXTestLib.phantomsRevenge, 2.0, "phantoms revenge"),
      (CoasterXTestLib.steelPhantom, 2.0,    "steel phantom   "),
      (CoasterXTestLib.elToro,2.0,           "el toro         ")
    )
    var coasterStats:List[CoasterStats] = Nil
    var componentStats:List[ComponentStats] = Nil

    val spec = new CoasterXSpec(1.0, debugLevel)
    val parsed = CoasterXParser.parseFile(CoasterXTestLib.straightLine).get
    val (align,alignFml) = spec.prepareFile(parsed)
    val env = spec.envelope(align)
    val prFast = new CoasterXProver(spec,env, reuseComponents = false, debugLevel = debugLevel, useNaive = false)
    val componentsToTest:List[(String, (() => ProvableSig))] = List(
      ("lineup", () => prFast.straightProofUp),
      ("linedown", () => prFast.straightProofDown),
      ("Q1", () => prFast.arcProofQ1),
      ("Q2", () => prFast.arcProofQ2),
      ("Q3", () => prFast.arcProofQ3),
      ("Q4", () => prFast.arcProofQ4),
      ("Q1CCW", () => prFast.arcProofQ1CCW),
      ("Q2CCW", () => prFast.arcProofQ2CCW),
      ("Q3CW", () => prFast.arcProofQ3CW),
      ("Q4CW", () => prFast.arcProofQ4CW)

    )
    componentsToTest.foreach({case (name, f) =>
        doStats(name, f, doFormula = true, doTactic = true, willDoStats = true, numRuns = numRuns, Some({case cs => componentStats = cs :: componentStats}))
    })

    coastersToTest.foreach { case (coast:String, feetPerUnit,name) =>
      val proof = CoasterXTestLib.prover(coast, name, doFast = false, NUM_RUNS = numRuns,
        feetPerUnit = feetPerUnit, velocity = None, doFormula = true, doStats = true, Some({case cs => coasterStats = cs :: coasterStats; cs.proof}),
        debugLevel = debugLevel)
      assert(proof.isProved, "CoasterX prover did not prove model :'( ")
    }

    // Begin printing
    println("Model\tSections\tVars\tTime(s)\tNoReuse(s)\tSpeedup(%)\t\t\tSteps\tSize(KB)")
    coasterStats.foreach{case CoasterStats(name,env,nSections,nVars,fastTimes,fastMean,slowTimes,slowMean,stepsFast,stepsSlow,speedupPercent,proof,size) =>
      println(s"$name\t$nSections\t$nVars\t$fastMean%1.2f\t$slowMean%1.2f\t$speedupPercent%1.2f\t$stepsFast\t$size%1.1f")
    }
    println("")
    println("Comp.\tVars\tTime(s)\tSteps\tSize(KB)")
    componentStats.foreach{case ComponentStats(name,alltimes,meantime,steps,vars,size,tac,seq) =>
      println(s"$name\t$vars%1.2f\t$meantime\t$steps\t$size%1.1f")
    }
  }

  def init(): Unit = {
    val database = DBAbstractionObj.defaultDatabase
    val args = Array[String]()
    val options = nextOption(Map('commandLine -> args.mkString(" ")), args.toList)

    //@note setup interpreter
    BelleInterpreter.setInterpreter(SequentialInterpreter())
    //@note pretty printer setup must be first, otherwise derived axioms print wrong
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXNoContractPrettyPrinter)
    // connect invariant generator to tactix library
    val generator = new ConfigurableGenerator[Formula]()
    TactixLibrary.invGenerator = generator
    KeYmaeraXParser.setAnnotationListener((p:Program,inv:Formula) => generator.products += (p->inv))

    println("Connecting to arithmetic tools...")

    try {
      val preferredTool = preferredToolFromConfig
      val config = configFromDB(options, database, preferredTool)
      createTool(options, config, preferredTool)
    } catch {
      //@todo add e to log here and in other places
      case e:Throwable => println("===> WARNING: Failed to initialize Mathematica. " + e)
        println("You should configure settings in the UI and restart KeYmaera X.")
        println("Or specify the paths to the libraries for your system explicitly from command line by running\n" +
          "  java -jar keymaerax.jar -mathkernel pathtokernel -jlink pathtojlink")
        println("Current configuration:\n" + edu.cmu.cs.ls.keymaerax.tools.diagnostic)
        e.printStackTrace()
    }

    println("Updating lemma caches...")

    try {
      //Delete the lemma database if KeYmaera X has been updated since the last time the database was populated.
      val cacheVersion = LemmaDBFactory.lemmaDB.version()
      if(StringToVersion(cacheVersion) < StringToVersion(edu.cmu.cs.ls.keymaerax.core.VERSION))
        LemmaDBFactory.lemmaDB.deleteDatabase()
      //Populate the derived axioms database.
      DerivedAxioms.prepopulateDerivedLemmaDatabase()
    } catch {
      case e : Exception =>
        println("===> WARNING: Could not prepopulate the derived lemma database. This is a critical error -- the UI will fail to work! <===")
        println("You should configure settings in the UI and restart KeYmaera X")
        e.printStackTrace()
    }

  }

  def nextOption(map: OptionMap, list: List[String]): OptionMap = list match {
    case Nil => map
    case "-tool" :: value :: tail => nextOption(map ++ Map('tool -> value), tail)
    case "-ui" :: tail => nextOption(map, tail)
    case "-launch" :: tail => nextOption(map, tail)
    case option :: tail => println("[Warning] Unknown option " + option + "\n\n" /*+ usage*/); nextOption(map, tail)
  }

  private def createTool(options: OptionMap, config: ToolProvider.Configuration, preferredTool: String): Unit = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    val provider = tool.toLowerCase() match {
      case "mathematica" => new MathematicaToolProvider(config)
      case "z3" => new Z3ToolProvider
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
    ToolProvider.setProvider(provider)
    assert(provider.tools().forall(_.isInitialized), "Tools should be initialized after init()")
  }

  private def configFromDB(options: OptionMap, db: DBAbstraction, preferredTool: String): ToolProvider.Configuration = {
    val tool: String = options.getOrElse('tool, preferredTool).toString
    tool.toLowerCase() match {
      case "mathematica" => mathematicaConfig
      case "z3" => Map.empty
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  private def preferredToolFromConfig: String = {
    Configuration.getOption(Configuration.Keys.QE_TOOL).getOrElse(throw new Exception("No preferred tool"))
  }

  private def mathematicaConfig: ToolProvider.Configuration = {
    getMathematicaLinkName match {
      case Some(l) => getMathematicaLibDir match {
        case Some(libDir) => Map("linkName" -> l, "libDir" -> libDir)
        case None => Map("linkName" -> l)
      }
      case None => DefaultConfiguration.defaultMathematicaConfig
    }
  }

  private def getMathematicaLinkName: Option[String] = {
    Configuration.getOption(Configuration.Keys.MATHEMATICA_LINK_NAME)
  }

  private def getMathematicaLibDir: Option[String] = {
    Configuration.getOption(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
  }


  def main(options:Map[Symbol,Any]):Unit = {
    init()
    withMathematica(qeTool => {
    options('coasterxMode) match {
      case "component" =>
        val componentName:String = options('in).asInstanceOf[String]
        val doFormula = options.get('doFormula).nonEmpty
        val doTactic = options.get('doTactic).nonEmpty
        val doStats = options.get('doStats).nonEmpty
        val numRuns = options.getOrElse('numRuns, "1").asInstanceOf[String].toInt
        val debugLevel = options.getOrElse('debugLevel, "1").asInstanceOf[String].toInt
        proveComponent(componentName, doFormula = doFormula, doTactic = doTactic, willDoStats = doStats, numRuns, debugLevel)
      case "coaster" =>
        val fileName:String = options('in).asInstanceOf[String]
        val doFormula = options.get('doFormula).nonEmpty
        val doStats = options.get('doStats).nonEmpty
        val useNaive = options.get('naiveArith).nonEmpty
        val feetPerUnit = options('feetPerUnit).asInstanceOf[String]
        val compareReuse = options.get('compareReuse).nonEmpty
        val velocity = options.get('velocity).asInstanceOf[Option[String]]
        val numRuns = options.getOrElse('numRuns, "1").asInstanceOf[String].toInt
        val debugLevel = options.getOrElse('debugLevel, "1").asInstanceOf[String].toInt
        proveCoaster(fileName, doFormula = doFormula, doStats = doStats, compareReuse = compareReuse, feetPerUnit.toDouble, velocity.map(_.toDouble), numRuns, debugLevel = debugLevel, useNaive = useNaive)
      case "table" =>
        val numRuns = options.getOrElse('numRuns, "1").asInstanceOf[String].toInt
        val debugLevel = options.getOrElse('debugLevel, "1").asInstanceOf[String].toInt
        printTable2(numRuns, debugLevel)
    }
  })
  }
}
