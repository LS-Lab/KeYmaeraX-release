/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import java.io.File

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import org.scalatest.events.{Event, TestFailed, TestIgnored, TestSucceeded}
import org.scalatest.{Args, Reporter, Suite}

import scala.collection.mutable

/**
  * Standalone command line runner for the ACAS X test suite.
  */
object AcasXRunner {

  private type OptionMap = Map[Symbol, Any]

  /** Usage -help information, formatted to 80 characters width. */
  private val usage = "KeYmaera X Prover (ACAS X Proofs)" + " " + core.VERSION +
    """
      |Supersedes alpha version of ACAS X proofs at
      |http://www.ls.cs.cmu.edu/pub/AcasX-long_alpha.zip
      |
      |Usage: java -Xss256M -jar KeYmaeraX-ACASX.jar
      |  -prove [all | theorem{1,3,4,5} | lemma{1,3,4} | corollary{1,3,4} ]
      |
      |Additional options:
      |  -mathkernel MathKernel(.exe) path to the Mathematica kernel executable
      |  -jlink path/to/jlinkNativeLib path to the J/Link native library directory
      |  -help     Display this usage information
      |  -license  Show license agreement for using this software
      |
      |Copyright (c) Carnegie Mellon University.
      |Use option -license to show the license conditions.
      |""".stripMargin

  def main (args: Array[String]): Unit = {
    println("KeYmaera X Prover (ACAS X Proofs)" + core.VERSION + "\n\n" +
      "Models at https://github.com/LS-Lab/KeYmaeraX/tree/master/keymaerax-webui/src/main/resources/examples/casestudies/acasx/sttt\n" +
      "Proof sources at https://github.com/LS-Lab/KeYmaeraX/tree/master/keymaerax-webui/src/test/scala/edu/cmu/cs/ls/keymaerax/btactics/acasxhstp/safeable\n\n" +
      "Supersedes alpha version of ACAS X proofs at\n http://www.ls.cs.cmu.edu/pub/AcasX-long_alpha.zip\n\n" +
      "Use option -help for usage and license information")

    if (args.length > 0 && (args(0)=="-help" || args(0)=="--help" || args(0)=="-h")) {println(usage); sys.exit(1)}
    else {
      def nextOption(map: OptionMap, list: List[String]): OptionMap = {
        list match {
          case Nil => map
          case "-help" :: _ => println(usage); sys.exit(1)
          case "-license" :: _ => println(license); sys.exit(1)
          case "-mathkernel" :: value :: tail =>
            if(value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('mathkernel -> value), tail)
            else optionErrorReporter("-mathkernel")
          case "-jlink" :: value :: tail =>
            if(value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('jlink -> value), tail)
            else optionErrorReporter("-jlink")
          case "-prove" :: value :: tail =>
            if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('mode -> "prove", 'what -> value), tail)
            else if (value.isEmpty) nextOption(map ++ Map('mode -> "prove", 'what -> "all"), tail)
            else optionErrorReporter("-prove")
          case option :: _ => optionErrorReporter(option)
        }
      }

      val options = nextOption(Map('commandLine -> args.mkString(" "), 'tool -> "z3"), args.toList)
      require(options.contains('mode), usage + "\narguments: " + args.mkString("  "))

      initializeProver(options)
      options.get('mode) match {
        case Some("prove") => prove(options)
      }
    }
  }

  private def scalatestReporter(succeeded: mutable.ListBuffer[(String, String)],
                                failed: mutable.ListBuffer[(String, String)],
                                ignored: mutable.ListBuffer[(String, String)]): Reporter = new Reporter() {
    override def apply(event: Event): Unit = event match {
      case TestSucceeded(_, _, _, _, testName, _, _, _, _, _, _, _, _, _) => succeeded += ((testName, "")); println(event)
      case TestFailed(_, _, _, _, _, testName, _, _, Some(cause), _, _, _, _, _, _, _) => failed += ((testName, cause.toString)); println(event)
      case TestFailed(_, _, _, _, _, testName, _, _, None, _, _, _, _, _, _, _) => failed += ((testName, "Unknown cause")); println(event)
      case TestIgnored(_, _, _, _, testName, _, _, _, _, _, _) => ignored += ((testName, "")); println(event)
      case _ => println(event)
    }
  }

  private def optionErrorReporter(option: String) = {
    val noValueMessage = "[Error] No value specified for " + option + " option. "
    option match {
      case "-prove" => println(noValueMessage + "Please use: -prove [all | lemma 3]\n\n" + usage); sys.exit(1)
      case "-mathkernel" => println(noValueMessage + "Please use: -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE\n\n" + usage); sys.exit(1)
      case "-jlink" => println(noValueMessage + "Please use: -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n\n" + usage); sys.exit(1)
      case _ =>  println("[Error] Unknown option " + option + "\n\n" + usage); sys.exit(1)
    }
  }

  private def initializeProver(options: OptionMap) = {
    initMathematica(options)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)

    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator

    //@note just in case the user shuts down the prover from the command line
    Runtime.getRuntime.addShutdownHook(new Thread() { override def run(): Unit = { shutdownProver() } })
  }

  /** Initializes Mathematica from command line options, if present; else from default config */
  private def initMathematica(options: OptionMap) = {
    assert((options.contains('mathkernel) && options.contains('jlink)) || (!options.contains('mathkernel) && !options.contains('jlink)),
      "\n[Error] Please always use command line option -mathkernel and -jlink together," +
        "and specify the Mathematica link paths with:\n" +
        " -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE" +
        " -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE \n\n" + usage)

    val mathematicaConfig =
      if (options.contains('mathkernel) && options.contains('jlink)) Map("linkName" -> options('mathkernel).toString,
        "libDir" -> options('jlink).toString)
      else DefaultConfiguration.defaultMathematicaConfig

    val linkNamePath = mathematicaConfig.get("linkName") match {
      case Some(path) => path
      case _ => ""
    }
    val libDirPath = mathematicaConfig.get("libDir") match {
      case Some(path) => path
      case _ => ""
    }
    assert(linkNamePath!="" && libDirPath!="",
      "\n[Error] The paths to MathKernel file named " + DefaultConfiguration.defaultMathLinkName._1 + " and jlinkLibDir file named " + DefaultConfiguration.defaultMathLinkName._2 + " are not specified! " +
        "(On your system, they could look like: " + {if(DefaultConfiguration.defaultMathLinkPath._1!="") DefaultConfiguration.defaultMathLinkPath._1 else DefaultConfiguration.exemplaryMathLinkPath._1} +
        " and " + {if(DefaultConfiguration.defaultMathLinkPath._2!="") DefaultConfiguration.defaultMathLinkPath._2 else DefaultConfiguration.exemplaryMathLinkPath._2} + ")\n" +
        "Please specify the paths to " + DefaultConfiguration.defaultMathLinkName._1 + " and " + DefaultConfiguration.defaultMathLinkName._2 + " with command line option:" +
        " -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE" +
        " -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n" +
        "[Note] Please always use command line option -mathkernel and -jlink together. \n\n" + usage)
    assert(linkNamePath.endsWith(DefaultConfiguration.defaultMathLinkName._1) && new java.io.File(linkNamePath).exists(),
      "\n[Error] Cannot find MathKernel file named " + DefaultConfiguration.defaultMathLinkName._1 + " in path: " + linkNamePath+ "! " +
        "(On your system, it could look like: " + {if(DefaultConfiguration.defaultMathLinkPath._1!="") DefaultConfiguration.defaultMathLinkPath._1 else DefaultConfiguration.exemplaryMathLinkPath._1} + ")\n" +
        "Please specify the correct path that points to " + DefaultConfiguration.defaultMathLinkName._1 + " file with command line option:" +
        " -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE\n" +
        "[Note] Please always use command line option -mathkernel and -jlink together. \n\n" + usage)
    assert(new java.io.File(libDirPath + File.separator + DefaultConfiguration.defaultMathLinkName._2).exists(),
      "\n[Error] Cannot find jlinkLibDir file named " + DefaultConfiguration.defaultMathLinkName._2 + " in path " + libDirPath+ "! " +
        "(On your system, it could look like: " + {if(DefaultConfiguration.defaultMathLinkPath._2!="") DefaultConfiguration.defaultMathLinkPath._2 else DefaultConfiguration.exemplaryMathLinkPath._2} + ")\n" +
        "Please specify the correct path that points to the directory contains " + DefaultConfiguration.defaultMathLinkName._2 + " file with command line option:" +
        " -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n" +
        "[Note] Please always use command line option -mathkernel and -jlink together. \n\n" + usage)

    DefaultConfiguration.currentMathematicaConfig = mathematicaConfig
    //@note test setup will initialize Mathematica tool provider
  }

  private def shutdownProver() = {
    ToolProvider.shutdown()
    TactixLibrary.invGenerator = FixedGenerator(Nil)
  }

  private def prove(options: OptionMap) = {
    require(options.contains('what), usage)

    val succeeded: mutable.ListBuffer[(String, String)] = mutable.ListBuffer()
    val failed: mutable.ListBuffer[(String, String)] = mutable.ListBuffer()
    val ignored: mutable.ListBuffer[(String, String)] = mutable.ListBuffer()

    (new DerivedAxiomsTests).run(Some("The DerivedAxioms prepopulation procedure should not crash"),
      Args(scalatestReporter(succeeded, failed, ignored)))

    val (tester: Suite, testName: Option[String]) = options('what).toString match {
      case "all" => (new AcasX, None)
      case x => val (t, tn) = testOf(x); (t, Some(tn))
    }

    val allTests: Set[String] = testName match {
      case None => tester.testNames ++ tester.nestedSuites.flatMap(_.testNames)
      case Some(tn) => Set(tn)
    }
    tester.run(testName, Args(scalatestReporter(succeeded, failed, ignored)))

    println("============= Proof summary ================")
    println(s"Succeeded proofs (${succeeded.size}/${allTests.size+1}}):\n  " + succeeded.toList.map(_._1).mkString("\n  "))
    println(s"Failed proofs (${failed.size}/${allTests.size+1}}):\n  " + failed.toList.map(f => f._1 + ": " + f._2).mkString("\n  "))
    println(s"Ignored proofs (${ignored.size}/${allTests.size+1}}):\n  " + ignored.toList.map(_._1).mkString("\n  "))
  }

  private def testOf(abbrv: String): (Suite, String) = abbrv.toLowerCase match {
    case "theorem1" => (new AcasXSafe, "ACAS X safe should prove Theorem 1: correctness of implicit safe regions")
    case "lemma1" => (new AcasXSafe, "ACAS X safe should prove Lemma 1: equivalence between implicit and explicit region formulation")
    case "corollary1" => (new AcasXSafe, "ACAS X safe should prove Corollary 1: explicit region safety from implicit region safety and conditional equivalence")
    case "theorem3" => (new AcasXSafeTwoSided, "ACAS X 2-sided safe should prove Theorem 3: correctness of implicit two-sided safe regions")
    case "lemma3" => (new AcasXSafeTwoSided, "ACAS X 2-sided safe should prove Lemma 3 fitting the form required by Corollary 3")
    case "corollary3" => (new AcasXSafeTwoSided, "ACAS X 2-sided safe should prove Corollary 3 (safety of explicit 2-sided regions) from Theorem 3 (implicit 2-sided safety) and Lemma 3 (implicit-explicit equivalence)")
    case "theorem4" => (new AcasXSafeBoundedTime, "ACAS X bounded time should prove Theorem 4: correctness of implicit bounded-time safe regions")
    case "lemma4" => (new AcasXSafeBoundedTime, "ACAS X bounded time should prove Lemma 4: alternative proof fitting the form required by Corollary 4")
    case "corollary4" => (new AcasXSafeBoundedTime, "ACAS X bounded time should prove Corollary 4 (safety of bounded-time explicit regions) from Theorem 4 (bounded-time implicit safety) and Lemma 4 (implicit-explicit equivalence)")
    case "theorem5" => (new AcasXSafeable, "ACAS X safeable should prove Theorem 5: correctness of implicit safeable region")
    case _ => throw new IllegalArgumentException(usage)
  }

  private val license: String = """
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
