package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.coasterx.{CoasterXParser, CoasterXSpec}
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

  "Spec Generator" should "generate a spec for example coaster" in {
    val coaster = CoasterXParser.parseFile(exampleFile1)
    val spec = CoasterXSpec(coaster.get)
    //TODO: Should normally use plain prettyString, but sometimes I've been creating massive formulas where the fast printer helps
    //val bigString = new KeYmaeraXPrinter().stringify(spec)
    val bigString = spec.prettyString
    println(bigString)
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
