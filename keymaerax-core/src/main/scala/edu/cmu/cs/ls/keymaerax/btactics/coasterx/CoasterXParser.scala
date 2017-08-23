package edu.cmu.cs.ls.keymaerax.btactics.coasterx

import edu.cmu.cs.ls.keymaerax.btactics.coasterx.CoasterXParser.parseDoublePoint
import edu.cmu.cs.ls.keymaerax.core._


object CoasterXParser {
/*
* CoasterX Format:
* FILE = ([JOINTS], [SECTIONS], v0, tentativeLineParams)
* JOINTS = <POINT,>*POINT
* POINT = (float, float)
* SECTIONS = <SECTION,>*SECTION
* SECTION = ('straight', paramOpt, pointOpt)
*  | ('arc', paramOpt, gradient)
*
* paramOpt = (None,)
*   | ((x1,y1,x2,y2),theta1,theta2)  (for arc)
*   | ((x1,y1,x2,y2),)  (for straight line)
*
* pointOpt = None
*   | float
* */

  // Parameters to sections are stored as (x, HEIGHT-y) so we will convert them to (x,y) (Quadrant I) to match the joints section
  val WORLD_WIDTH = 1200
  val WORLD_HEIGHT = 600

  val example:String = "([(40, 100), \n  (800, 100), \n  (1003, 292), \n  (1014.0703641303933, 490.6092116668379), \n  (1037.047741675357, 512.3415096403996),\n  (1060, 491), \n  (1074.5057163758297, 291.8183498791612), \n  (1198, 111)], \n [('straight', (None,), None), \n  ('straight', ((40, 500, 800, 500),), 0.0),\n  ('arc', ((596.6848958333333, 93.36979166666652, 1003.3151041666667, 500.0), -90.0, 86.80966720837762), 17.940621403912424), \n  ('straight', ((1003, 308, 1014.0703641303933, 109.3907883331621),), 17.940621403912424), \n  ('arc', ((1014.0346977885041, 87.6584903596004, 1060.0607855622097, 133.68457813330605), 176.80966720837756, -86.80966720837756), 0), \n  ('arc', ((1014.0346977885041, 87.6584903596004, 1060.0607855622097, 133.68457813330605), 90, -85.8346983689234), -13.7312522153492), \n  ('straight', ((1060, 109, 1074.5057163758297, 308.1816501208388),), -13.7312522153492), \n  ('arc', ((1073.9302486950965, 74.48837803692527, 1509.6673714837575, 510.2255008255863), -175.83469836892337, 60.33353966713379), -0.4770003569825235)], \n165, \n(1143.3888820234438, 306.5466392767369, 1335.184957771975, 498.342715025268))"

  sealed trait SectionParam {}
  final case class ArcParam(bl:TPoint, tr:TPoint, theta1:Number, deltaTheta:Number) extends SectionParam {
    def theta2:Number = {Number(theta1.value + deltaTheta.value)}
  }
  final case class LineParam(bl:TPoint, tr:TPoint) extends SectionParam {}

  sealed trait Section {}
  final case class ArcSection(param:Option[ArcParam], gradient:Option[Term]) extends Section {}
  final case class LineSection(param:Option[LineParam], gradient:Option[Term]) extends Section {}

  type Point = (Number, Number)
  type TPoint = (Term, Term)

  type File = (List[TPoint], List[Section], Number, SectionParam)

  def parseArcParam(str:String):Option[(Option[ArcParam],String)] = {
    peelPrefix(str, "(None,)") match {
      case Some(post) => Some(None, post)
      case None =>
        peelPrefix(str, "(").flatMap({case post1 =>
        parseDoublePoint(post1).flatMap({case ((x1,x2,x3,x4),post2) =>
        peelPrefix(post2, ",").flatMap({case post3 =>
        parseNumber(post3).flatMap({case (theta1, post4) =>
        peelPrefix(post4, ",").flatMap({case post5 =>
        parseNumber(post5).flatMap({case (theta2, post6) =>
        peelPrefix(post6,")").map({case post7 =>
        (Some(ArcParam((x1,Number(WORLD_HEIGHT-x2.value)),(x3,Number(WORLD_HEIGHT-x4.value)),theta1,theta2)),post7)})})})})})})})}
  }

  def parseLineParam(str:String):Option[(Option[LineParam],String)] = {
    peelPrefix(str, "(None,)") match {
      case Some(post) => Some(None, post)
      case None =>
        peelPrefix(str, "(").flatMap({case post1 =>
        parseDoublePoint(post1).flatMap({case ((x1,x2,x3,x4),post2) =>
        peelPrefix(post2,",)").map({case post3 =>
        (Some(LineParam((x1,Number(WORLD_HEIGHT-x2.value)),(x3,Number(WORLD_HEIGHT-x4.value)))),post3)})})})}
  }

  def parseSection(file:String):Option[(Section, String)] = {
    peelPrefix(file, "(").flatMap({case post1 =>
      (peelPrefix(post1,"\'arc\'"), peelPrefix(post1,"\'straight\'")) match {
        case(Some(arcPost), _) =>
          peelPrefix(arcPost, ",").flatMap({case post2 =>
          parseArcParam(post2).flatMap({case (arcParam, post3) =>
          peelPrefix(post3,",").flatMap({case post4 =>
          parseNumberOption(post4).flatMap({case (grad, post5) =>
          peelPrefix(post5, ")").map({case post6 =>
          (ArcSection(arcParam,grad),post6)})})})})})

        case(_, Some(straightPost)) =>
          peelPrefix(straightPost, ",").flatMap({case post2 =>
          parseLineParam(post2).flatMap({case (lineParam, post3) =>
          peelPrefix(post3,",").flatMap({case post4 =>
          parseNumberOption(post4).flatMap({case (grad, post5) =>
          peelPrefix(post5, ")").map({case post6 =>
          (LineSection(lineParam,grad),post6)})})})})})
      }
    })
  }

  def parseSections(file:String):Option[(List[Section], String)] = {
    parseList(parseSection,file)
  }


  def parseTentParam(str:String):Option[(SectionParam, String)] = {
    parseDoublePoint(str).flatMap({case ((x1,x2,x3,x4),post2) =>
    Some(LineParam((x1,x3),(x2,x4)),post2)})
  }

  def parseList[T](parseOne:String => Option[(T,String)], str:String):Option[(List[T],String)] = {
    parseOne(str) match {
      case Some((one, tail)) =>
        val innerTail =
          if(tail.startsWith(",")) {
            tail.drop(1)
          } else {
            tail
          }
        parseList(parseOne, innerTail).map({case (tailParsed, post) => (one ::tailParsed, post)})
      case None =>
        peelPrefix(str, "]").map({case post => (Nil, post)})
    }
  }


  def parsePoint(str:String):Option[(Point, String)] = {
    peelPrefix(str,"(").flatMap({case post1 =>
    parseNumber(post1).flatMap({case (x1, post2) =>
    peelPrefix(post2, ",").flatMap({case post3 =>
    parseNumber(post3).flatMap({case (x2, post4) =>
    peelPrefix(post4, ")").map({case post5 =>
    ((x1,x2),post5)})})})})})
  }

  def parseDoublePoint(str:String):Option[((Number,Number,Number,Number), String)] = {
    peelPrefix(str,"(").flatMap({case post1 =>
    parseNumber(post1).flatMap({case (x1, post2) =>
    peelPrefix(post2, ",").flatMap({case post3 =>
    parseNumber(post3).flatMap({case (x2, post4) =>
    peelPrefix(post4, ",").flatMap({case post5 =>
    parseNumber(post5).flatMap({case (x3, post6) =>
    peelPrefix(post6, ",").flatMap({case post7 =>
    parseNumber(post7).flatMap({case (x4, post8) =>
    peelPrefix(post8, ")").map({case post9 =>
    ((x1,x2,x3,x4),post9)})})})})})})})})})
  }

  def parseJoints(file:String):Option[(List[Point], String)] = {
    parseList(parsePoint, file)
  }


  def checkPrefix(str:String, pre:String):Option[Unit] = {
    if(str.startsWith(pre)) {
      Some()
    } else {
      None
    }
  }

  def peelPrefix(str:String, pre:String):Option[String] = {
    if(str.startsWith(pre)) {
      Some(str.drop(pre.length))
    } else {
      None
    }
  }

  def parseNumber(str:String):Option[(Number,String)] = {
    val (pre,post) = str.span(c => c.isDigit || c == '.' || c == '-')
    try {
      Some((Number(BigDecimal(pre)),post))
    } catch {
      case _:NumberFormatException => None
    }
  }

  def parseNumberOption(str:String):Option[(Option[Number],String)] = {
    peelPrefix(str,"None") match {
      case Some(post) => Some(None, post)
      case None => parseNumber(str).map{case (num,post) => (Some(num),post)}
    }
  }

  def parseFile(fileRaw:String):Option[File] = {
    val file = fileRaw.filter({case c => c != '\n' && c != ' '})
    peelPrefix(file, "([").flatMap({case pre1 =>
    parseJoints(pre1).flatMap({case (joints, post1) => {
    peelPrefix(post1, ",[").flatMap({case pre2 =>
    parseSections(pre2).flatMap({case (sections, post2) => {
    peelPrefix(post2, ",").flatMap({case pre3 =>
    parseNumber(pre3).flatMap({case (v0, post3) =>
    peelPrefix(post3, ",").flatMap({case pre4 =>
    parseTentParam(pre4).flatMap({case (param, post4) =>
    peelPrefix(post4, ")").flatMap({case "" =>
    Some((joints, sections, v0, param))
    })})})})})}})})}})})
  }
}
