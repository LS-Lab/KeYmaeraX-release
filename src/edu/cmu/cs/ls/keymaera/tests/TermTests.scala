package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import java.io._
import scala.language.postfixOps
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.core.ProofStep

object TermTests {

  def getTautology: Formula = {
    val p = new PredicateConstant("p")
    val q = new PredicateConstant("q")
    //val q = new FormulaName("q")
    val i = Imply(p, q)
    Imply(q, i)
  }

  def getTautology2: Formula = {
    val x = Variable("x", None, Real)
    val a = Assign(x, Number(0))
    val b = Assign(x, Number(1))
    val p = GreaterThan(Real, x, Number(0))
    Equiv(BoxModality(Choice(a, b), p),And(BoxModality(a, p), BoxModality(b, p)))
  }

  def getSubst = {
    val x = Variable("x", None, Real)
    val a = Assign(x, Number(0))
    val b = Assign(x, Number(1))
    val p = GreaterThan(Real, x, Number(0))
    val substPairs = Seq(new SubstitutionPair(PredicateConstant("$p"), p), new SubstitutionPair(ProgramConstant("$a"), a), new SubstitutionPair(ProgramConstant("$b"), b))
    val subst = new Substitution(substPairs)
    Axiom.axioms.get("Choice") match {
      case Some(f) => (subst, Map((getTautology2, f)))
      case _ => throw new IllegalArgumentException("blub")
    }
  }


  def test = {
      val i2 = getTautology
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
    val i2 = getTautology
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
    val i2 = getTautology
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
    val (subst, delta) = getSubst
    val tactic: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & cutT(getTautology2) & (hideT(new Position(true, 1)), (hideT(new Position(true, 0))*) & uniformSubstT(subst, delta) & axiomT("Choice") & AxiomCloseT)
    val tactic2: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & AxiomCloseT
    tactic(r, new Limit(None, None))
    tactic2(r, new Limit(None, None))
    val tree =  print(r)
    println(tree)
    writeToFile(new File(output), tree)
    r.isClosed
  }

  def test5(input: String, output: String) {
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.parse(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val form = printForm(i2)
    writeToFile(new File(output), form)
  }

  def readFile(input: String): String = try {
    val fr = new BufferedReader(new FileReader(input))
    var result = ""
    while(fr.ready) {
      result += fr.readLine
    }
    result
  } catch {
    case e: IOException => throw new IllegalArgumentException(e)
  }

  def writeToFile(f: File, s: String) = try {
    val fw = new BufferedWriter(new FileWriter(f));
    fw.write(s)
    fw.flush
    fw.close
  } catch {
    case _: IOException =>
  }

  def printPos(expr: PosInExpr): Any = ???

  def printNamedSymbol(n: NamedSymbol): String = n.name + "_" + (n.index match { case Some(j) => "_" + j case _ => "" }) + "\""

  def printForm(formula: Formula): String = {
    var jsonResult: String = ""
    val fn = new ExpressionTraversalFunction {

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += e match {
          case True() => "{ id=\"" + printPos(p) + "\" name=\"true\"}"
          case False() => "{ id=\"" + printPos(p) + "\" name=\"false\"}"
          case x@PredicateConstant(a, b) => "{ id=\"" + printPos(p) + "\" name=" + printNamedSymbol(x.asInstanceOf[PredicateConstant]) + "}"
          case ApplyPredicate(a, b) => "{ id=\"" + printPos(p) + "\" name=\"apply\" children=[ " + printNamedSymbol(a) + ", "
          case Equals(d, a, b) => "{ id=\"" + printPos(p) + "\" name=\"equals\"" + " children=[ "
          case NotEquals(d, a, b) => "{ id=\"" + printPos(p) + "\" name=\"notEquals\"" + " children=[ "
          case ProgramEquals(a, b) => "{ id=\"" + printPos(p) + "\" name=\"programEquals\"" + " children=[ "
          case ProgramNotEquals(a, b) => "{ id=\"" + printPos(p) + "\" name=\"programNotEquals\"" + " children=[ "
          case LessThan(d, a, b) => "{ id=\"" + printPos(p) + "\" name=\"lt\"" + " children=[ "
          case LessEquals(d, a, b) => "{ id=\"" + printPos(p) + "\" name=\"leq\"" + " children=[ "
          case GreaterEquals(d, a, b) => "{ id=\"" + printPos(p) + "\" name=\"geq\"" + " children=[ "
          case GreaterThan(d, a, b) => "{ id=\"" + printPos(p) + "\" name=\"gt\"" + " children=[ "
          case Not(a) => "{ id=\"" + printPos(p) + "\" name=\"not\"" + " children=[ "
          case And(a, b) => "{ id=\"" + printPos(p) + "\" name=\"and\"" + " children=[ "
          case Or(a, b) => "{ id=\"" + printPos(p) + "\" name=\"or\"" + " children=[ "
          case Imply(a, b) => "{ id=\"" + printPos(p) + "\" name=\"imply\"" + " children=[ "
          case Equiv(a, b) => "{ id=\"" + printPos(p) + "\" name=\"equiv\"" + " children=[ "
          case Modality(a, b) => "{ id=\"" + printPos(p) + "\" name=\"modality\"" + " children=[ "
          case Forall(v, a) => "{ id=\"" + printPos(p) + "\" name=\"forall\" variables=[" + v.map(printNamedSymbol).mkString(",") + "] children=[ "
          case Exists(v, a) => "{ id=\"" + printPos(p) + "\" name=\"exists\" variables=[" + v.map(printNamedSymbol).mkString(",") + "] children=[ "
          case _ => throw new UnsupportedOperationException("not implemented yet")
        }

        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += e match {
          case Number(s, i) => "{ id=\"" + printPos(p) + "\" name=\"" + i + "\"}"
          case x@Variable(_, _, _) => "{ id=\"" + printPos(p) + "\" name=" + printNamedSymbol(x.asInstanceOf[Variable]) + "}"
          case Apply(a, b) => "{ id=\"" + printPos(p) + "\" name=\"apply\" children=[ " + printNamedSymbol(a) + ", "
          case Neg(_, a) => "{ id=\"" + printPos(p) + "\" name=\"neg\"" + " children=[ "
          case Derivative(_, a) => "{ id=\"" + printPos(p) + "\" name=\"derivative\"" + " children=[ "
          case Add(_, a, b) => "{ id=\"" + printPos(p) + "\" name=\"add\"" + " children=[ "
          case Subtract(_, a, b) => "{ id=\"" + printPos(p) + "\" name=\"subtract\"" + " children=[ "
          case Multiply(_, a, b) => "{ id=\"" + printPos(p) + "\" name=\"multiply\"" + " children=[ "
          case Divide(_, a, b) => "{ id=\"" + printPos(p) + "\" name=\"divide\"" + " children=[ "
          case Exp(_, a, b) => "{ id=\"" + printPos(p) + "\" name=\"Exp\"" + " children=[ "
          case _ => throw new UnsupportedOperationException("not implemented yet")
        }
        Left(None)
      }

      override def inF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += ", "
        Left(None)
      }

      override def inT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += ", "
        Left(None)
      }

      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += e match {
          case ApplyPredicate(a, b) => "]}"
          case Equals(d, a, b) => "]}"
          case NotEquals(d, a, b) => "]}"
          case ProgramEquals(a, b) => "]}"
          case ProgramNotEquals(a, b) => "]}"
          case LessThan(d, a, b) => "]}"
          case LessEquals(d, a, b) => "]}"
          case GreaterEquals(d, a, b) => "]}"
          case GreaterThan(d, a, b) => "]}"
          case Not(a) => "]}"
          case And(a, b) => "]}"
          case Or(a, b) => "]}"
          case Imply(a, b) => "]}"
          case Equiv(a, b) => "]}"
          case Modality(a, b) => "]}"
          case Forall(v, a) => "]}"
          case Exists(v, a) => "]}"
          case _ => ""
        }
        Left(None)
      }

      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += e match {
          case Apply(a, b) => "]}"
          case Neg(_, a) => "]}"
          case Derivative(_, a) => "]}"
          case Add(_, a, b) => "]}"
          case Subtract(_, a, b) => "]}"
          case Multiply(_, a, b) => "]}"
          case Divide(_, a, b) => "]}"
          case Exp(_, a, b) => "]}"
          case _ => ???
        }

        Left(None)
      }
    }
    ""
  }

  def print(l: Seq[Formula]): String = (for(f <- l) yield KeYmaeraPrettyPrinter.stringify(f).replaceAll("\\\\", "\\\\\\\\")).mkString(",")
  def print(s: Sequent): String = "\"" + print(s.ante) + " ==> " + print(s.succ) + "\""
  def print(p: ProofNode): String = "{ \"sequent\":" + print(p.sequent) + ", \"children\": [ " + p.children.map(print).mkString(",") + "]}"
  def print(ps: ProofStep): String = "{\"rule\":\"" + ps.rule.toString + "\", \"children\": [" + ps.subgoals.map(print).mkString(",") + "]" + "}"

}

// vim: set ts=4 sw=4 et:
