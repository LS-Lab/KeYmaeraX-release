package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import java.io._
import edu.cmu.cs.ls.keymaera.core.ProofStep

object TermTests {

  def test = {
      //val p = new FormulaName("p")
      val p = new PredicateConstant("p")
      val q = new PredicateConstant("q")
      //val q = new FormulaName("q")
      val i = Imply(p, q)
      val i2 = Imply(q, i)
      println(i)
      val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
      val pos = new Position(false, 0)
      val pos2 = new Position(true, 0)
      val c = r(ImplyRight, pos)
      for(n <- c) {
        val c2 = n(ImplyRight, pos)
        for(n2 <- c2) {
          val end = n2(AxiomClose(pos2), pos)
          println(end)
        }
      }
  }

  def test2 = {
    val p = new PredicateConstant("p")
    val q = new PredicateConstant("q")
    val i = Imply(p, q)
    val i2 = Imply(q, i)
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    println(r.isClosed)
    println(print(r))
    val tactic: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & AxiomCloseT
    tactic(r, new Limit(None, None))
    println(print(r))
    r.isClosed
  }

  def test3(fileName: String) = {
    val p = new PredicateConstant("p")
    val q = new PredicateConstant("q")
    val i = Imply(p, q)
    val i2 = Imply(q, i)
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    println(r.isClosed)
    println(print(r))
    val tactic: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & AxiomCloseT
    tactic(r, new Limit(None, None))
    val tree =  print(r)
    println(tree)
    writeToFile(new File(fileName), tree)
    r.isClosed
  }

  def test4(input: String, output: String) = {
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.parse(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    println(r.isClosed)
    println(print(r))
    val tactic: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & AxiomCloseT
    tactic(r, new Limit(None, None))
    val tree =  print(r)
    println(tree)
    writeToFile(new File(output), tree)
    r.isClosed
  }

  def readFile(input: String): String = try {
    val fr = new BufferedReader(new FileReader(input))
    var result = ""
    while(fr.ready) {
      result += fr.readLine
    }
    result
  } catch {
    case e => throw new IllegalArgumentException(e)
  }

  def writeToFile(f: File, s: String) = try {
    val fw = new BufferedWriter(new FileWriter(f));
    fw.write(s)
    fw.flush
    fw.close
  } catch {
    case _ =>
  }

  def print(l: Seq[Formula]): String = (for(f <- l) yield KeYmaeraPrettyPrinter.stringify(f)).mkString(",")
  def print(s: Sequent): String = "\"" + print(s.ante) + " ==> " + print(s.succ) + "\""
  def print(p: ProofNode): String = "{ \"name\":" + print(p.sequent) + ", \"children\": [ " + p.children.map(print).mkString(",") + "]}"
  def print(ps: ProofStep): String = "{\"name\":\"" + ps.rule.toString + "\", \"children\": [" + ps.subgoals.map(print).mkString(",") + "]" + "}"

}

// vim: set ts=4 sw=4 et:
