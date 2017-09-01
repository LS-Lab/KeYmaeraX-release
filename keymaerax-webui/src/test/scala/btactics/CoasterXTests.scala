package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.{CoasterXParser, CoasterXProver, CoasterXSpec}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, KeYmaeraXPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

class CoasterXTests extends TacticTestBase {
  val exampleFile1:String = "([(40, 100), \n  (800, 100), \n  (1003, 292), \n  (1014.0703641303933, 490.6092116668379), \n  (1037.047741675357, 512.3415096403996),\n  (1060, 491), \n  (1074.5057163758297, 291.8183498791612), \n  (1198, 111)], \n [('straight', (None,), None), \n  ('straight', ((40, 500, 800, 500),), 0.0),\n  ('arc', ((596.6848958333333, 93.36979166666652, 1003.3151041666667, 500.0), -90.0, 86.80966720837762), 17.940621403912424), \n  ('straight', ((1003, 308, 1014.0703641303933, 109.3907883331621),), 17.940621403912424), \n  ('arc', ((1014.0346977885041, 87.6584903596004, 1060.0607855622097, 133.68457813330605), 176.80966720837756, -86.80966720837756), 0), \n  ('arc', ((1014.0346977885041, 87.6584903596004, 1060.0607855622097, 133.68457813330605), 90, -85.8346983689234), -13.7312522153492), \n  ('straight', ((1060, 109, 1074.5057163758297, 308.1816501208388),), -13.7312522153492), \n  ('arc', ((1073.9302486950965, 74.48837803692527, 1509.6673714837575, 510.2255008255863), -175.83469836892337, 60.33353966713379), -0.4770003569825235)], \n165, \n(1143.3888820234438, 306.5466392767369, 1335.184957771975, 498.342715025268))"
  val joints:String = "(40,100),(800,100),(1003,292),(1014.0703641303933,490.6092116668379),(1037.047741675357,512.3415096403996),(1060,491),(1074.5057163758297,291.8183498791612),(1198,111)"
  val segments:String = "('straight',(None,),None),('straight',((40,500,800,500),),0.0),('arc',((596.6848958333333,93.36979166666652,1003.3151041666667,500.0),-90.0,86.80966720837762),17.940621403912424),('straight',((1003,308,1014.0703641303933,109.3907883331621),),17.940621403912424),('arc',((1014.0346977885041,87.6584903596004,1060.0607855622097,133.68457813330605),176.80966720837756,-86.80966720837756),0),('arc',((1014.0346977885041,87.6584903596004,1060.0607855622097,133.68457813330605),90,-85.8346983689234),-13.7312522153492),('straight',((1060,109,1074.5057163758297,308.1816501208388),),-13.7312522153492),('arc',((1073.9302486950965,74.48837803692527,1509.6673714837575,510.2255008255863),-175.83469836892337,60.33353966713379),-0.4770003569825235)"
  val full:String = "([" + joints + "], [" + segments + "], 165, \n(1143.3888820234438, 306.5466392767369, 1335.184957771975, 498.342715025268))"
  val seg1:String = "('straight',(None,),None)"
  val seg2:String = "('straight',((40,500,800,500),),0.0)"
  val seg3:String = "('arc',((596.6848958333333,93.36979166666652,1003.3151041666667,500.0),-90.0,86.80966720837762),17.940621403912424)"
  val seg4:String = "('straight',((1003,308,1014.0703641303933,109.3907883331621),),17.940621403912424)"
  val seg5:String = "('arc',((1014.0346977885041,87.6584903596004,1060.0607855622097,133.68457813330605),176.80966720837756,-86.80966720837756),0)"
  val seg6:String = "('arc',((1014.0346977885041,87.6584903596004,1060.0607855622097,133.68457813330605),90,-85.8346983689234),-13.7312522153492)"
  val seg7:String = "('straight',((1060,109,1074.5057163758297,308.1816501208388),),-13.7312522153492)"
  val seg8:String = "('arc',((1073.9302486950965,74.48837803692527,1509.6673714837575,510.2255008255863),-175.83469836892337,60.33353966713379),-0.4770003569825235)"

  // More example files
  val straightLine = "([(0, 100), (1000, 100)], [('straight', (None,), None), ('straight', ((0, 500, 1000, 500),), 0.0)], 1.0, (0, 0, 0, 0))"
  val quarterArc = "([(100, 100), (171, 129)], [('straight', (None,), None),   ('arc', ((0, 300, 200, 500), -90, 45.0), 1.0)], 500.0, (171, 129, 171, 129))"
  val halfArc = "([(0, 200), (100, 300)], [('straight', (None,), None),   ('arc', ((0, 300, 200, 500), -180, -90.0), 0.0)], 500.0, (100, 300, 100, 300))"
  val fullArc = "([(0, 200), (100, 300), (200, 200)],  [('straight', (None,), None), ('arc', ((0, 300, 200, 500), -180, -90.0), 0.0),   ('arc', ((0, 300.0, 200, 500), 90.0, -90), -48.494845360825195)], 500.0, (-800, -94.31605562579006, 198.106405394016, 906.9587020648964))"
  val simpleHill = "([(0, 100),  (100, 200),  (342, 300),   (579, 202),  (683, 102)],[('straight', (None,), None), ('straight', ((0, 500, 100, 400),), 1.0), ('arc', ((0, 300, 683, 983), 135.0, -45.0), 0), ('arc', ((0, 300, 683, 983), 90, -45.0), -1), ('straight', ((579, 398, 683, 497),), -1)], 500.0, (-2406.346757107975, -29.408888352737677, 1211.9531693319414, 3588.8910380871785))"
  val simpleValley = "([(0, 500),  (100, 400),   (199, 359),   (299, 398),   (415, 505)], [('straight', (None,), None),  ('straight', ((0, 100, 100, 200),), -1.0),  ('arc', ((59, -39, 339, 241), -135, 45), 0),  ('arc', ((51, -55, 347, 241), -90,  43), 0.92), ('straight', ((299, 202, 415, 95),), 0.92)], 500.0, (415.37482499434077, 94.97095456951104, 253.3717788455165, 243.96392952765427))"


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

  def printFileSpec(s:String):Unit = println(CoasterXSpec(CoasterXParser.parseFile(s).get))

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

  "Proof Generator" should "generate proof for straight line" in { withMathematica(qeTool => {
    val pr = CoasterXProver(straightLine)
    pr shouldBe 'proved
    })
  }

  it should "generate proof for quarter arc" in { withMathematica(qeTool => {
    val pr = CoasterXProver(quarterArc)
    pr shouldBe 'proved
    })
  }


  /* bigDecimal = {BigDecimal@2869} "0E+1"
 intVal = {BigInteger@2872} "0"
 scale = -1
 precision = 1
 stringCache = "0E+1"
 intCompact = 0
mc = {MathContext@2870} "precision=34 roundingMode=HALF_EVEN"
computedHashCode = 1565550863*/
  "Core Parser" should "not do funny scientific notation" in {
    val x = "0.00000001".asTerm
    //val x = Number(BigDecimal(1)/BigDecimal(10000000L))
    val str = x.prettyString
    str.asTerm shouldBe x
  }
}
