package edu.cmu.cs.ls.keymaerax.launcher

import java.io.PrintWriter

import com.sun.org.apache.xalan.internal.xsltc.compiler.util.ClassGenerator
import edu.cmu.cs.ls.keymaerax.core.{And, Formula, Sequent, Variable}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXProblemParser, KeYmaeraXParser}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.ModelPlex.{modelplexControllerMonitorTrafo, modelplexInPlace}
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import edu.cmu.cs.ls.keymaerax.codegen.{CGenerator, SpiralGenerator}


import scala.collection.immutable
import scala.reflect.runtime._
import scala.tools.reflect.{ToolBoxError, ToolBox}
import scala.util.Random

/**
 * Command-line interface for KeYmaera X.
 * @author Stefan Mitsch
 * @author aplatzer
 * @author Ran Ji
 */
object KeYmaeraX {

  /** KeYmaera X version number */
  val VERSION = "4.0a2"

  private type OptionMap = Map[Symbol, Any]

  private val usage = "KeYmaera X Prover" + " " + VERSION +
    """
      |
      |Usage: java -Xss20M -jar KeYmaeraX.jar
      |  -prove filename -tactic filename [-out filename] |
      |  -modelplex filename [-vars var1,var2,...,varn] [-out filename] |
      |  -codegen filename -format C|Spiral [-vars var1,var2,...,varn] [-out filename] |
      |  -ui [filename] [web server options]
      |
      |Additional options:
      |  -ui [opt] optional arguments [opts] are passed to the web user interface
      |            that -ui starts, opening the given file (if any)
      |  -mathkernel MathKernel(.exe) path to the Mathematica kernel executable
      |  -jlink path/to/jlinkNativeLib path to the J/Link native library directory
      |  -verify   check the resulting proof certificate (recommended)
      |  -noverify skip checking proof certificates after proof search
      |  -interval guard real arithmetic by interval arithmetic in float point (recommended)
      |  -nointerval  skip interval arithmetic presuming no floating point rounding occurs
      |  -interactive starts a simple command-line prover if -prove fails
      |  -lax      enable lax mode with more flexible parser input and printer output etc.
      |  -strict   enable strict mode with no flexibility in prover
      |  -debug    enable debug mode with more exhaustive messages
      |  -nodebug  disable debug mode to suppress intermediate messages
      |  -help     Display this usage information
      |  -license  Show license agreement for using this software
      |
      |Copyright (c) Carnegie Mellon University.
      |Use option -license for the license conditions for using this software.
      |""".stripMargin

  def main (args: Array[String]): Unit = {
    println("KeYmaera X Prover\n" +
      "Use option -help for usage and license information")
    if (args.length == 0) launchUI(args)
    if (args.length > 0 && (args(0)=="-help" || args(0)=="--help" || args(0)=="-h")) {println(usage); sys.exit(1)}
    else {
      def makeVariables(varNames: Array[String]): Array[Variable] = {
        varNames.map(vn => KeYmaeraXParser(vn) match {
          case v: Variable => v
          case v => throw new IllegalArgumentException("String " + v + " is not a valid variable name")
        })
      }

      def nextOption(map: OptionMap, list: List[String]): OptionMap = {
        list match {
          case Nil => map
          case "-help" :: _ => {
            println(usage); sys.exit(1)
          }
          case "-license" :: _ => {
            println(license); sys.exit(1)
          }
          // actions
          case "-prove" :: value :: tail => nextOption(map ++ Map('mode -> "prove", 'in -> value), tail)
          case "-modelplex" :: value :: tail => nextOption(map ++ Map('mode -> "modelplex", 'in -> value), tail)
          case "-codegen" :: value :: tail => nextOption(map ++ Map('mode -> "codegen", 'in -> value), tail)
          case "-ui" :: tail => launchUI(tail.toArray); map ++ Map('mode -> "ui")
          // action options
          case "-out" :: value :: tail => nextOption(map ++ Map('out -> value), tail)
          case "-vars" :: value :: tail => nextOption(map ++ Map('vars -> makeVariables(value.split(","))), tail)
          case "-format" :: value :: tail => nextOption(map ++ Map('format -> value), tail)
          case "-tactic" :: value :: tail => nextOption(map ++ Map('tactic -> value), tail)
          case "-interactive" :: tail => nextOption(map ++ Map('interactive -> true), tail)
          // aditional options
          case "-mathkernel" :: value :: tail => nextOption(map ++ Map('mathkernel -> value), tail)
          case "-jlink" :: value :: tail => nextOption(map ++ Map('jlink -> value), tail)
          case "-verify" :: tail => require(!map.contains('verify)); nextOption(map ++ Map('verify -> true), tail)
          case "-noverify" :: tail => require(!map.contains('verify)); nextOption(map ++ Map('verify -> false), tail)
          case "-interval" :: tail => require(!map.contains('interval)); nextOption(map ++ Map('interval -> true), tail)
          case "-nointerval" :: tail => require(!map.contains('interval)); nextOption(map ++ Map('interval -> false), tail)
          // global options
          case "-lax" :: tail => System.setProperty("LAX", "true"); nextOption(map, tail)
          case "-strict" :: tail => System.setProperty("LAX", "false"); nextOption(map, tail)
          case "-debug" :: tail => System.setProperty("DEBUG", "true"); nextOption(map, tail)
          case "-nodebug" :: tail => System.setProperty("DEBUG", "false"); nextOption(map, tail)
          case option :: tail => println("Unknown option " + option + "\n" + usage); sys.exit(1)
        }
      }

      //@note 'commandLine is only passed in to preserve evidence of what generated the output.
      val options = nextOption(Map('commandLine -> args.mkString(" ")), args.toList)
      require(options.contains('mode), usage + "\narguments: " + args.mkString("  "))

      if (options.get('mode) != Some("ui")) {
        try {
          initializeProver(options)

          //@todo allow multiple passes by filter architecture: -prove bla.key -tactic bla.scal -modelplex -codegen -format C
          options.get('mode) match {
            case Some("prove") => prove(options)
            case Some("modelplex") => modelplex(options)
            case Some("codegen") => codegen(options)
            case Some("ui") => assert(false, "already handled above since no prover needed"); ???
          }
        }
        finally {
          shutdownProver()
        }
      }
    }
  }

  def initializeProver(options: OptionMap) = {
    val mathematicaConfig =
      if (options.contains('mathkernel) && options.contains('jlink)) Map("linkName" -> options.get('mathkernel).get.toString,
                                                                         "libDir" -> options.get('jlink).get.toString)
      else DefaultConfiguration.defaultMathematicaConfig

    require(mathematicaConfig.contains("linkName") && mathematicaConfig.contains("libDir"),
      if (!options.contains('mathkernel)) "Cannot find Mathematica at default location, please use command line options\n" + usage)

    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)

    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  //@todo Runtime.getRuntime.addShutdownHook??
  def shutdownProver() = {
    if (Tactics.KeYmaeraScheduler != null) {
      Tactics.KeYmaeraScheduler.shutdown()
      Tactics.KeYmaeraScheduler = null
    }
    if (Tactics.MathematicaScheduler != null) {
      Tactics.MathematicaScheduler.shutdown()
      Tactics.MathematicaScheduler = null
    }
  }

  /** Exit gracefully */
  private def exit(status: Int): Unit = {shutdownProver(); sys.exit(status)}

  /** Generate a header stamping the source of a generated file */
  //@todo Of course this has a security attack for non-letter characters like end of comments from command line
  private def stampHead(options: OptionMap): String = "/* @evidence: generated by KeYmaeraX " + VERSION + " " + options.getOrElse('commandLine, "<unavailable>") + " */\n\n"


  /**
   * Prove given input file (with given tactic) to produce a lemma.
   * {{{KeYmaeraXLemmaPrinter(Prover(tactic)(KeYmaeraXProblemParser(input)))}}}
   * @param options
   * @todo tactic should default to master and builtin tactic names at least from ExposedTacticsLibrary should be accepted (without file extension)
   */
  def prove(options: OptionMap) = {
    require(options.contains('in), usage)
    require(options.contains('tactic), usage)

    val tacticFileName = options.get('tactic).get.toString
    val tacticSource = scala.io.Source.fromFile(tacticFileName).mkString

    val cm = universe.runtimeMirror(getClass.getClassLoader)
    val tb = cm.mkToolBox()
    val tacticGenerator = tb.eval(tb.parse(tacticSource)).asInstanceOf[() => Tactic]

    val tactic = tacticGenerator()

    // KeYmaeraXLemmaPrinter(Prover(tactic)(KeYmaeraXProblemParser(input)))
    val inputFileName = options.get('in).get.toString
    val input = scala.io.Source.fromFile(inputFileName).mkString
    val inputModel = KeYmaeraXProblemParser(input)
    val inputSequent = Sequent(Nil, immutable.IndexedSeq[Formula](), immutable.IndexedSeq(inputModel))

    val pw = new PrintWriter(options.getOrElse('out, inputFileName + ".proof").toString)

    //@todo turn the following into a transformation as well. The natural type is Prover: Tactic=>(Formula=>Provable) which however always forces 'verify=true. Maybe that's not bad.
    val rootNode = new RootNode(inputSequent)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, rootNode))

    if (rootNode.isClosed()) {
      assert(rootNode.openGoals().isEmpty)
      if (options.getOrElse('verify, false).asInstanceOf[Boolean]) {
        val witness = rootNode.provableWitness
        val proved = witness.proved
        //@note assert(witness.isProved, "Successful proof certificate") already checked in line above
        assert(inputSequent == proved, "Proved the original problem and not something else")
        println("Proof certificate: Passed")
      } else {
        println("Proof certificate: Skipped extraction of proof certificate from proof search\n (use -verify to generate and check proof certificate)")
      }
      //@todo Printing of Provable as text should be somewhere in LemmaDB functionalities.
      //@note printing original input rather than a pretty-print of proved ensures that @invariant annotations are preserved for reproves.
      val evidence =
        s"""Tool.
          |  input "$input"
          |  tactic "${scala.io.Source.fromFile(tacticFileName).mkString}"
          |  proof ""
          |End.
          |""".stripMargin
      //@note pretty-printing the result of parse ensures that the lemma states what's actually been proved.
      assert(KeYmaeraXParser(KeYmaeraXPrettyPrinter(inputModel)) == inputModel, "parse of print is identity")
      //@todo why is this of the form bla <-> true instead of just bla?
      val lemmaContent =
        s"""Lemma "${inputFileName.substring(inputFileName.lastIndexOf('/')+1)}".
          |  (${KeYmaeraXPrettyPrinter(inputModel)}) <-> true
          |End.
          |""".stripMargin

      //@todo ensure that reparse of this lemma is as expected
      pw.write(stampHead(options))
      pw.write("/* @evidence: parse of print of result of a proof */\n\n")
      pw.write(lemmaContent + evidence)
      pw.close()
    } else {
      assert(!rootNode.isClosed())
      assert(rootNode.openGoals().nonEmpty)
      println("==================================")
      println("Tactic did not finish the proof    open goals: " + rootNode.openGoals().size)
      println("==================================")
      printOpenGoals(rootNode)
      println("==================================")
      if (options.getOrElse('interactive,false)==true) {
        interactiveProver(rootNode)
      } else {
        System.err.println("Incomplete proof: tactic did not finish the proof")
        //@note PrintWriter above has already emptied the output file
        pw.close()
        exit(-1)
      }
    }
  }

  /**
   * ModelPlex monitor synthesis for the given input files
   * {{{KeYmaeraXPrettyPrinter(ModelPlex(vars)(KeYmaeraXProblemParser(input))}}}
   * @param options in describes input file name, vars describes the list of variables, out describes the output file name.
   */
  def modelplex(options: OptionMap) = {
    require(options.contains('in), usage)

    // KeYmaeraXPrettyPrinter(ModelPlex(vars)(KeYmaeraXProblemParser(input))
    val inputFileName = options.get('in).get.toString
    val input = scala.io.Source.fromFile(inputFileName).mkString
    val inputModel = KeYmaeraXProblemParser(input)
    val verifyOption = options.getOrElse('verify, true).asInstanceOf[Boolean]

    val pw = new PrintWriter(options.getOrElse('out, inputFileName + ".mx").toString)

    val outputFml = if (options.contains('vars))
      ModelPlex(options.get('vars).get.asInstanceOf[Array[Variable]].toList, verifyOption)(inputModel)
    else
      ModelPlex(inputModel, verifyOption)
    val output = KeYmaeraXPrettyPrinter(outputFml)

    val reparse = KeYmaeraXParser(output)
    assert(reparse == outputFml, "parse of print is identity")
    pw.write(stampHead(options))
    pw.write("/* @evidence: parse of print of ModelPlex proof output */\n\n")
    pw.write(output)
    pw.close()
  }



  /**
   * Code generation
   * {{{CGenerator()(input)}}}
   */
  def codegen(options: OptionMap) = {
    require(options.contains('in), usage)
    require(options.contains('format), usage)

    val inputFileNameMx = options.get('in).get.toString
    val input = scala.io.Source.fromFile(inputFileNameMx).mkString
    val inputFormula = KeYmaeraXParser(input)
    val inputFileName = inputFileNameMx.substring(0, inputFileNameMx.length-".mx".length)

    if (options.getOrElse('interval, true).asInstanceOf[Boolean]) {
      //@todo check that when assuming the output formula as an additional untrusted lemma, the Provable isProved.
      System.err.println("Cannot yet augment compiled code with interval arithmetic to guard against floating-point roundoff errors\n(use -nointerval instead)")

      println("Interval arithmetic: unfinished")
      System.err.println("Interval arithmetic: unfinished")
      //@todo wipe out output file PrintWriter above has already emptied the output file
      //@todo pw.close()
      sys.exit(-1)
      // TODO what to to when proof cannot be checked?
    } else {
      println("Interval arithmetic: Skipped interval arithmetic generation\n(use -interval to guard against floating-point roundoff errors)")
    }

    if(options.get('format).get.toString == "C") {
      val vars: List[Variable] =
        if(options.contains('vars)) options.get('vars).get.asInstanceOf[Array[Variable]].toList
        else Nil
      val output = CGenerator(inputFormula, vars, inputFileName)
      val pw = new PrintWriter(options.getOrElse('out, inputFileName + ".c").toString)
      pw.write(stampHead(options))
      pw.write("/* @evidence: print of CGenerator of input */\n\n")
      pw.write(output)
      pw.close()
    } else if(options.get('format).get.toString == "Spiral") {
      var outputG = ""
      if (options.contains('vars)) {
        val output = SpiralGenerator(inputFormula, options.get('vars).get.asInstanceOf[Array[Variable]].toList, inputFileName)
        outputG = output._1
        val outputH = output._2
        val pwG = new PrintWriter(options.getOrElse('out, inputFileName + ".g").toString)
        pwG.write(stampHead(options))
        pwG.write(outputG)
        pwG.close()
        val pwH = new PrintWriter(options.getOrElse('out, inputFileName + ".h").toString)
        pwH.write(stampHead(options))
        pwH.write(outputH)
        pwH.close()
      } else {
        outputG = SpiralGenerator(inputFormula, inputFileName)
        val pwG = new PrintWriter(options.getOrElse('out, inputFileName + ".g").toString)
        pwG.write(stampHead(options))
        pwG.write(outputG)
        pwG.close()
      }
    } else throw new IllegalArgumentException("-format C or -format Spiral should be specified as a command line argument")
  }


  /** Launch the web user interface */
  def launchUI(args: Array[String]): Unit = {
    Main.main(args)
  }

  // helpers

  /** Print brief information about all open goals in the proof tree under node */
  def printOpenGoals(node: ProofNode): Unit = node.openGoals().foreach(g => printNode(g))

  /** Print brief information about the given node */
  def printNode(node: ProofNode): Unit =
    println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " ===\n  " +
      (if (node.isClosed) "Closed Goal: " else if (node.children.isEmpty) "Open Goal: " else "Inner Node: ") +
      node.sequent.toString() + "\n" +
      "  \tdebug: " + node.tacticInfo.infos.getOrElse("debug", "<none>") + "\n")

  /** Print elaborate information about the given node */
  def elaborateNode(node: ProofNode): Unit = {
    println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " ===  " +
      (if (node.isClosed) "Closed Goal: " else if (node.children.isEmpty) "Open Goal: " else "Inner Node: ") +
      "\tdebug: " + node.tacticInfo.infos.getOrElse("debug", "<none>") +
      "\n" +
      (1 to node.sequent.ante.length).
        map(i => -i + ":  " + node.sequent.ante(i-1).prettyString + "\t" + node.sequent.ante(i-1).getClass.getSimpleName).mkString("\n") +
      "\n  ==>\n" +
      (1 to node.sequent.succ.length).
        map(i => +i + ":  " + node.sequent.succ(i-1).prettyString + "\t" + node.sequent.succ(i-1).getClass.getSimpleName).mkString("\n") +
      "\n")
  }

  private val interactiveUsage = "Type a tactic command to apply to the current goal.\n" +
    "skip - ignore the current goal for now and skip to the next goal.\n" +
    "goals - list all open goals.\n" +
    "goal i - switch to goal number i\n" +
    "exit - quit the prover (or hit Ctrl-C any time).\n" +
    "help - will display this usage information.\n" +
    "Tactics will be reported back when a branch closes but may need cleanup.\n"
  /** KeYmaera C: A simple interactive command-line prover */
  private def interactiveProver(root: ProofNode): ProofNode = {
    val commands = io.Source.stdin.getLines()
    val cm = universe.runtimeMirror(getClass.getClassLoader)
    val tb = cm.mkToolBox()
    println("KeYmaera X Interactive Command-line Prover\n" +
      "If you are looking for the more convenient web user interface,\nrestart with option -ui\n")
    println(interactiveUsage)

    while (!root.isClosed()) {
      assert(!root.openGoals().isEmpty, "proofs that are not closed must have open goals")
      println("Open Goals: " + root.openGoals.size)
      var node = root.openGoals().head
      println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " ===\n")
      var tacticLog = ""
      assert(!node.isClosed, "open goals are not closed")
      while (!node.isClosed()) {
        elaborateNode(node) //printNode(node)
        System.out.flush()
        commands.next().trim match {
          case "" =>
          case "help" => println(interactiveUsage)
          case "exit" => exit(5)
          case "goals" => val open = root.openGoals()
            (1 to open.length).map(g => {println("Goal " + g); elaborateNode(open(g-1))})
          case it if it.startsWith("goal ") => try {
            val g = it.substring("goal ".length).toInt
            if (1<=g&&g<=root.openGoals().size) node = root.openGoals()(g-1)
            else println("No such goal: "+ g)
          } catch {case e: NumberFormatException => println(e)}
          case "skip" =>
            if (root.openGoals().size >= 2) {
              //@todo skip to the next goal somewhere on the right of node, not to a random goal
              //@todo track this level skipping by closing and opening parentheses in the log
              var nextGoal = new Random().nextInt(root.openGoals().length)
              assert(0 <= nextGoal && nextGoal < root.openGoals().size, "random in range")
              node = if (root.openGoals()(nextGoal) != node)
                root.openGoals()(nextGoal)
              else {
                val otherGoals = (root.openGoals() diff List(node))
                assert(otherGoals.length == root.openGoals().length - 1, "removing one open goal decreases open goal count by 1")
                nextGoal = new Random().nextInt(otherGoals.length)
                assert(0 <= nextGoal && nextGoal < otherGoals.size, "random in range")
                otherGoals(nextGoal)
              }
            } else {
              println("No other open goals to skip to")
            }
          case command: String =>
            try {
              //@note security issue since executing arbitrary input unsanitized
              val tacticGenerator = tb.eval(tb.parse(tacticParsePrefix + command + tacticParseSuffix)).asInstanceOf[() => Tactic]
              val tactic = tacticGenerator()
              tacticLog += "& " + command + "\n"
              Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, node))
              // walk to the next open subgoal
              // continue walking if it has leaves
              while (!node.isClosed() && !node.children.isEmpty && !node.children.head.subgoals.isEmpty)
                node = node.children.head.subgoals(0)
              //@todo make sure to walk to siblings ultimately
            }
            catch {
              case e: ToolBoxError => println("Command failed: " + e + "\n"); System.out.flush()
            }
        }
      }
      assert(node.isClosed())
      println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " === CLOSED")
      println(tacticLog)
    }
    root
  }

  //@todo import namespace of the user tactic *object* passed in -tactic
  private val tacticParsePrefix =
    """
      |import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
      |import edu.cmu.cs.ls.keymaerax.tactics.Tactics.Tactic
      |import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
      |import edu.cmu.cs.ls.keymaerax.tactics.BranchLabels._
      |import edu.cmu.cs.ls.keymaerax.tactics._
      |class InteractiveLocalTactic extends (() => Tactic) {
      |  def apply(): Tactic = {
      |
    """.stripMargin

  private val tacticParseSuffix =
    """
      |  }
      |}
      |new InteractiveLocalTactic()
    """.stripMargin


  private val license: String =
    """
      |KeYmaera X
      |SOFTWARE LICENSE AGREEMENT
      |ACADEMIC OR NON-PROFIT ORGANIZATION NONCOMMERCIAL RESEARCH USE ONLY
      |
      |BY USING THE SOFTWARE, YOU ARE AGREEING TO THE TERMS OF THIS LICENSE
      |AGREEMENT. IF YOU DO NOT AGREE WITH THESE TERMS, YOU MAY NOT USE OR
      |DOWNLOAD THE SOFTWARE.
      |
      |This is a license agreement ("Agreement") between your academic
      |institution or non-profit organization or self (called "Licensee" or
      |"You" in this Agreement) and Carnegie Mellon University (called
      |"Licensor" in this Agreement). All rights not specifically granted
      |to you in this Agreement are reserved for Licensor.
      |
      |RESERVATION OF OWNERSHIP AND GRANT OF LICENSE:
      |
      |Licensor retains exclusive ownership of any copy of the Software (as
      |defined below) licensed under this Agreement and hereby grants to
      |Licensee a personal, non-exclusive, non-transferable license to use
      |the Software for noncommercial research purposes, without the right
      |to sublicense, pursuant to the terms and conditions of this
      |Agreement. As used in this Agreement, the term "Software" means (i)
      |the executable file made accessible to Licensee by Licensor pursuant
      |to this Agreement, inclusive of backups, and updates permitted
      |hereunder or subsequently supplied by Licensor, including all or any
      |file structures, programming instructions, user interfaces and
      |screen formats and sequences as well as any and all documentation
      |and instructions related to it.
      |
      |CONFIDENTIALITY: Licensee acknowledges that the Software is
      |proprietary to Licensor, and as such, Licensee agrees to receive all
      |such materials in confidence and use the Software only in accordance
      |with the terms of this Agreement. Licensee agrees to use reasonable
      |effort to protect the Software from unauthorized use, reproduction,
      |distribution, or publication.
      |
      |COPYRIGHT: The Software is owned by Licensor and is protected by
      |United States copyright laws and applicable international treaties
      |and/or conventions.
      |
      |PERMITTED USES: The Software may be used for your own noncommercial
      |internal research purposes. You understand and agree that Licensor
      |is not obligated to implement any suggestions and/or feedback you
      |might provide regarding the Software, but to the extent Licensor
      |does so, you are not entitled to any compensation related thereto.
      |
      |BACKUPS: If Licensee is an organization, it may make that number of
      |copies of the Software necessary for internal noncommercial use at a
      |single site within its organization provided that all information
      |appearing in or on the original labels, including the copyright and
      |trademark notices are copied onto the labels of the copies.
      |
      |USES NOT PERMITTED: You may not modify, translate, reverse engineer,
      |decompile, disassemble, distribute, copy or use the Software except
      |as explicitly permitted herein. Licensee has not been granted any
      |trademark license as part of this Agreement and may not use the name
      |or mark "KeYmaera X", "Carnegie Mellon" or any renditions thereof
      |without the prior written permission of Licensor.
      |
      |You may not sell, rent, lease, sublicense, lend, time-share or
      |transfer, in whole or in part, or provide third parties access to
      |prior or present versions (or any parts thereof) of the Software.
      |
      |ASSIGNMENT: You may not assign this Agreement or your rights
      |hereunder without the prior written consent of Licensor. Any
      |attempted assignment without such consent shall be null and void.
      |
      |TERM: The term of the license granted by this Agreement is from
      |Licensee's acceptance of this Agreement by clicking "I Agree" below
      |or by using the Software until terminated as provided below.
      |
      |The Agreement automatically terminates without notice if you fail to
      |comply with any provision of this Agreement. Licensee may terminate
      |this Agreement by ceasing using the Software. Upon any termination
      |of this Agreement, Licensee will delete any and all copies of the
      |Software. You agree that all provisions which operate to protect the
      |proprietary rights of Licensor shall remain in force should breach
      |occur and that the obligation of confidentiality described in this
      |Agreement is binding in perpetuity and, as such, survives the term
      |of the Agreement.
      |
      |FEE: Provided Licensee abides completely by the terms and conditions
      |of this Agreement, there is no fee due to Licensor for Licensee's
      |use of the Software in accordance with this Agreement.
      |
      |DISCLAIMER OF WARRANTIES: THE SOFTWARE IS PROVIDED "AS-IS" WITHOUT
      |WARRANTY OF ANY KIND INCLUDING ANY WARRANTIES OF PERFORMANCE OR
      |MERCHANTABILITY OR FITNESS FOR A PARTICULAR USE OR PURPOSE OR OF
      |NON-INFRINGEMENT. LICENSEE BEARS ALL RISK RELATING TO QUALITY AND
      |PERFORMANCE OF THE SOFTWARE AND RELATED MATERIALS.
      |
      |SUPPORT AND MAINTENANCE: No Software support or training by the
      |Licensor is provided as part of this Agreement.
      |
      |EXCLUSIVE REMEDY AND LIMITATION OF LIABILITY: To the maximum extent
      |permitted under applicable law, Licensor shall not be liable for
      |direct, indirect, special, incidental, or consequential damages or
      |lost profits related to Licensee's use of and/or inability to use
      |the Software, even if Licensor is advised of the possibility of such
      |damage.
      |
      |EXPORT REGULATION: Licensee agrees to comply with any and all
      |applicable U.S. export control laws, regulations, and/or other laws
      |related to embargoes and sanction programs administered by the
      |Office of Foreign Assets Control.
      |
      |SEVERABILITY: If any provision(s) of this Agreement shall be held to
      |be invalid, illegal, or unenforceable by a court or other tribunal
      |of competent jurisdiction, the validity, legality and enforceability
      |of the remaining provisions shall not in any way be affected or
      |impaired thereby.
      |
      |NO IMPLIED WAIVERS: No failure or delay by Licensor in enforcing any
      |right or remedy under this Agreement shall be construed as a waiver
      |of any future or other exercise of such right or remedy by Licensor.
      |
      |GOVERNING LAW: This Agreement shall be construed and enforced in
      |accordance with the laws of the Commonwealth of Pennsylvania without
      |reference to conflict of laws principles. You consent to the
      |personal jurisdiction of the courts of this County and waive their
      |rights to venue outside of Allegheny County, Pennsylvania.
      |
      |ENTIRE AGREEMENT AND AMENDMENTS: This Agreement constitutes the sole
      |and entire agreement between Licensee and Licensor as to the matter
      |set forth herein and supersedes any previous agreements,
      |understandings, and arrangements between the parties relating hereto.
      |
    """.stripMargin
}
