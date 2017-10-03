package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.File
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXTestLib._
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.{CoasterXParser, CoasterXProver, CoasterXSpec, CoasterXTestLib}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

@SlowTest
object CoasterXTests {

}
class CoasterXTests extends TacticTestBase {
  "Joint Parser" should "parse first joint" in {
    val joint = CoasterXParser.parsePoint("(40,100)")
    joint shouldBe 'defined
  }

  "Joints Parser" should "parse example joints" in {
    val coaster = CoasterXParser.parseJoints(joints + "]")
    coaster shouldBe 'defined
  }

  it should "parse singleton list" in {
    val joints = CoasterXParser.parseJoints("(40,100)]")
    joints shouldBe 'defined
  }

  "Segment Parser" should "parse null segment" in {
    val seg = CoasterXParser.parseSection(seg1)
    seg shouldBe 'defined
  }

  it should "parse straight" in {
    val seg = CoasterXParser.parseSection(seg2)
    seg shouldBe 'defined
  }

  it should "parse arc" in {
    val seg = CoasterXParser.parseSection(seg3)
    seg shouldBe 'defined
  }

  it should "parse more 4" in {
    val seg = CoasterXParser.parseSection(seg4)
    seg shouldBe 'defined
  }

  it should "parse more 5" in {
    val seg = CoasterXParser.parseSection(seg5)
    seg shouldBe 'defined
  }

  it should "parse more 6" in {
    val seg = CoasterXParser.parseSection(seg6)
    seg shouldBe 'defined
  }

  it should "parse more 7 " in {
    val seg = CoasterXParser.parseSection(seg7)
    seg shouldBe 'defined
  }

  it should "parse more 8" in {
    val seg = CoasterXParser.parseSection(seg8)
    seg shouldBe 'defined
  }

  it should "parse segment list" in {
    val seggs = CoasterXParser.parseSections(segments + "]")
    seggs shouldBe 'defined
  }

  it should "singleton list" in {
    val segg = CoasterXParser.parseSections(seg1 + "]")
    segg shouldBe 'defined
  }

  it should "two element list" in {
    val seggs = CoasterXParser.parseSections(seg1+","+seg2+"]")
    seggs shouldBe 'defined
  }
  it should "reconstructed list" in {
    val seggs = CoasterXParser.parseSections(seg1+","+seg2+","+seg3+","+seg4+","+seg5+","+seg6+","+seg7+","+seg8+"]")
    seggs shouldBe 'defined
  }

  "Coaster Parser" should "parse example coaster" in {
    val coaster = CoasterXParser.parseFile(exampleFile1)
    coaster shouldBe 'defined
  }

  "newline" should "be whitespace" in {
    ' '.isWhitespace shouldBe true
  }

  def printFileSpec(s:String):Unit = println(new CoasterXSpec(1.0)(CoasterXParser.parseFile(s).get))

  "Spec Generator" should "generate a spec for example coaster" in {
    printFileSpec(exampleFile1)
  }


  it should "generate spec for straight line" in {
    printFileSpec(straightLine)
  }

  // quarterArc, halfArc, fullArc, simpleHill, simpleValley
  it should "generate spec for quarter arc" in {
    printFileSpec(quarterArc)
  }

  it should "generate spec for halfArc" in {
    printFileSpec(halfArc)
  }

  it should "generate spec for fullArc" in {
    printFileSpec(fullArc)
  }

  it should "generate spec for simpleHill" in {
    printFileSpec(simpleHill)
  }

  it should "generate spec for simpleValley" in {
    printFileSpec(simpleValley)
  }

  "All components " should "prove and produce statistics" in { withMathematica(qeTool => {
    val spec = new CoasterXSpec(1.0)
    // file shouldnt matter
    val file = straightLine
    val parsed = CoasterXParser.parseFile(file).get
    val (align,alignFml) = spec.prepareFile(parsed)
    val env = spec.envelope(align)
    val specc = spec.fromAligned((align,alignFml),env)
    val specStr = KeYmaeraXPrettyPrinter.stringify(specc)
    val specLenKB = specStr.length / 1000.0
    val nVars = countVars(specc)

    val prFast = new CoasterXProver(spec,env, reuseComponents = false)

    val q1ccw = doStats("Q1CCW", () => prFast.arcProofQ1CCW, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q2ccw = doStats("Q2CCW", () => prFast.arcProofQ2CCW, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q3cw  = doStats("Q3CW", () => prFast.arcProofQ3CW, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q4cw  = doStats("Q4CW", () => prFast.arcProofQ4CW, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q1 = doStats("Q1", () => prFast.arcProofQ1, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q2 = doStats("Q2", () => prFast.arcProofQ2, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q3 = doStats("Q3", () => prFast.arcProofQ3, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val q4 = doStats("Q4", () => prFast.arcProofQ4, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
    val s = doStats("Line", () => prFast.straightProof, doFormula = true, doTactic = true, willDoStats = true, numRuns = 1)
  })}


  def prover(fileContents:String, modelName:String):ProvableSig = {
    CoasterXTestLib.prover(fileContents, modelName, doFast = false, NUM_RUNS = 1, feetPerUnit = 1.0, velocity = None, doFormula = true, doStats = true)
  }

  "Proof Generator" should "generate proof for straight line" in { withMathematica(qeTool => {
    val pr = prover(straightLine, "Straight Line")
    pr shouldBe 'proved
    })
  }

  it should "generate proof for quarter arc" in { withMathematica(qeTool => {
    val pr = prover(quarterArc, "Quarter Arc")
    pr shouldBe 'proved
  })}

  it should "generate proof for half arc" in {  withMathematica(qeTool => {
    val pr = prover(halfArc, "Half Arc 1")
    pr shouldBe 'proved
  })}

  it should "generate proof for second half arc" in {  withMathematica(qeTool => {
    val pr = prover(secondHalfArc, "Half Arc 2")
    pr shouldBe 'proved
  })}

  it should "generate proof for full arc" in {  withMathematica(qeTool => {
    val pr = prover(fullArc, "Full Arc")
    pr shouldBe 'proved
  })}

  it should "generate proof for Q1 CCW" in { withMathematica(qeTool => {
    val pr = prover(q1arcCCW, "Q1 CCW")
    pr shouldBe 'proved
  })}

  it should "generate proof for Q2 CCW" in { withMathematica(qeTool => {
    val pr = prover(q2arcCCW, "Q2 CCW")
    pr shouldBe 'proved
  })}

  it should "generate proof for Q3 CW" in { withMathematica(qeTool => {
    val pr = prover(q3arcCW, "Q3 CW")
    pr shouldBe 'proved
  })}

  it should "generate proof for Q4 CW" in { withMathematica(qeTool => {
    val pr = prover(q4arcCW, "Q4 CW")
    pr shouldBe 'proved
  })}

  it should "generate proof for hill" in {  withMathematica(qeTool => {
    val pr = prover(simpleHill, "Simple Hill")
    pr shouldBe 'proved
  })}

  it should "generate proof for valley" in {  withMathematica(qeTool => {
    val pr = prover(simpleValley, "Simple Valley")
    pr shouldBe 'proved
  })}

  it should "generate proof for simple inversion" in {  withMathematica(qeTool => {
    val pr = prover(simpleInversion, "Simple Inversion")
    pr shouldBe 'proved
  })}

  it should "generate proof for example coaster" in { withMathematica(qeTool => {
    val pr = prover(exampleFile1, "Example (Top Thrill?)")
    pr shouldBe 'proved
  })
  }

  it should "generate proof for extreme envelope" in { withMathematica(qeTool => {
    val pr = prover(extremeEnv, "Extreme Envelope")
    pr shouldBe 'proved
  })}

  it should "generate proof for many arc sizes" in { withMathematica(qeTool => {
    val pr = prover(multiSizeArcs, "ManyArcSizes")
    pr shouldBe 'proved
  })}

  it should "generate proof for shrinking Q3" in { withMathematica(qeTool => {
    val pr = prover(q3Shrinks, "Shrinking Q3")
    pr shouldBe 'proved
  })}

  it should "generate proof for growing Q3" in { withMathematica(qeTool => {
    val pr = prover(q3Grows, "Growing Q3")
    pr shouldBe 'proved
  })}

  it should "generate proof for Paul Gregg's backyard coaster" in { withMathematica(qeTool => {
    val pr = prover(byrc, "BYRC")
    pr shouldBe 'proved
  })
  }

  it should "generate proof for Lil' Phantom" in { withMathematica(qeTool => {
    val pr = prover(lilPhantom, "Lil' Phantom")
    pr shouldBe 'proved
  })}

  it should "generate proof for  The Phantom's Revenge" in { withMathematica(qeTool => {
    val pr = prover(phantomsRevenge, "Phantom's Revenge")
    pr shouldBe 'proved
  })
  }

  /*  it should "generate proof for part of El Toro" in { withMathematica(qeTool => {
    val pr = prover(smallToro, "El Toro Mini")
    pr shouldBe 'proved
  })}
*/
  it should "generate proof for El Toro" in { withMathematica(qeTool => {
    val pr = prover(elToro, "El Toro Full")
    pr shouldBe 'proved
  })}


  "Core Parser" should "not do funny scientific notation" in {
    val x = "0.00000001".asTerm
    val str = x.prettyString
    str.asTerm shouldBe x
  }
}
