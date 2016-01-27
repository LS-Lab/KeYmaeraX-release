package edu.cmu.cs.ls.keymaerax.fcpsutils

/**
  * Created by nfulton on 1/25/16.
  */
object AutoLabScores {
  def apply(problemInfo: Map[String, Int]) = """{"scores":""" + problemInfo.map(problem => {
    "\n" + s"""  "${problem._1}":${problem._2},"""
  }) + "}"
}
