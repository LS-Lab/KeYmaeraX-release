package edu.cmu.cs.ls.keymaerax

/**
  * Created by nfulton on 1/17/16.
  */
object CourseMain {
  def main(args : Array[String]) = {
    val file = args(0)
    try {
      edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser(scala.io.Source.fromFile(file).mkString)
      System.exit(0)
    }
    catch {
      case e : Exception => {
        e.printStackTrace()
        System.exit(-1)
      }
    }
  }
}
