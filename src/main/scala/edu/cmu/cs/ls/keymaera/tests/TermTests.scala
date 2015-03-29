package edu.cmu.cs.ls.keymaera.tests

// favoring immutable Seqs

import edu.cmu.cs.ls.keymaera.core.ProofNode.ProofStep

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import java.io._
import scala.language.postfixOps
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.tactics.{Generate, TacticWrapper, TacticLibrary, Tactics}

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
    val substPairs = Seq(new SubstitutionPair(PredicateConstant("p"), p), new SubstitutionPair(ProgramConstant("a"), a), new SubstitutionPair(ProgramConstant("b"), b))
    val subst = USubst(substPairs)
    Axiom.axioms.get("[++] choice") match {
      case Some(f) => (subst, Map((getTautology2, f)))
      case _ => throw new IllegalArgumentException("blub")
    }
  }


  def test = {
      val i2 = getTautology
      val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
      val pos = SuccPosition(0)
      val pos2 = AntePosition(0)
      val c = r(ImplyRight(pos)).subgoals
      for(n <- c) {
        val c2 = n(ImplyRight(pos)).subgoals
        for(n2 <- c2) {
          val end = n2(AxiomClose(pos2, pos))
          println(end)
        }
      }
  }

/*  def test2 = {
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

*/
  def test4(input: String, output: String) = {
    import TacticLibrary._
    val i2: Formula = new KeYmaeraParser().runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    //println(r.isClosed)
    println(print(r))
    val (subst, delta) = getSubst
    val tactic: Tactic = Tactics.weakSeqT(
      Tactics.weakSeqT(
        Tactics.weakSeqT(
          Tactics.repeatT(locateSucc(ImplyRightT)),
          locateAnte(ImplyLeftT)),
        cutT(Some(getTautology2)))
     , hideT(AntePosition(1)))//, (hideT(new Position(true, 0))*) & uniformSubstT(subst, delta) & axiomT("Choice") & AxiomCloseT)
    //val tactic2: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & AxiomCloseT
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    //tactic2(r)
    Thread.sleep(3000)
    val tree =  print(r)
    println(tree)
    writeToFile(new File(output), tree)
    //r.isClosed
  }

  def test5(input: String, output: String) {
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val form = printForm(i2)
    writeToFile(new File(output), form)
  }

  def test6(input: String, output: String) {
    import TacticLibrary._
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    val tactic = ((AxiomCloseT | locateSucc(indecisive(false, true, true))
      | locateAnte(indecisive(false, true, true))
      | locateSucc(indecisive(true, true, true))
      | locateAnte(indecisive(true, true, true))
      | locateAnte(eqLeft(false)) )*) ~ quantifierEliminationT("Mathematica")
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    Thread.sleep(3000)
    /*while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(100)
      println("Blocked " + Tactics.KeYmaeraScheduler.blocked + " of " + Tactics.KeYmaeraScheduler.maxThreads)
      println("Tasks open: " + Tactics.KeYmaeraScheduler.prioList.length)
    }*/
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }

  def test7(output: String) {
    import TacticLibrary._
    // x>0,y=x+1,x>0&y=x+1->x+1>0 ==> x+1>0
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val xp1 = Add(Real, x, Number(1))
    val zero = Number(0)
    val r = new RootNode(new Sequent(Nil, Vector(GreaterThan(Real, x, zero), Equals(Real, y, xp1), Imply(And(GreaterThan(Real, x, zero), Equals(Real, y, xp1)), GreaterThan(Real, xp1, zero))), Vector(GreaterThan(Real, xp1, zero))))
    val tactic = ((AxiomCloseT | locateSucc(indecisive(true, false, true)) | locateAnte(indecisive(true, false, true, true)))*)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
//    while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
//      Thread.sleep(10)
//    }
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }

  def test8(output: String) {
    import TacticLibrary._
    // x>0,y=x+1,x>0&y=x+1->x+1>0 ==> x+1>0
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val xp1 = Add(Real, x, Number(1))
    val zero = Number(0)
    val r = new RootNode(new Sequent(Nil, Vector(GreaterThan(Real, x, zero), Equals(Real, y, xp1), Imply(And(GreaterThan(Real, x, zero), Equals(Real, y, xp1)), GreaterThan(Real, xp1, zero))), Vector(GreaterThan(Real, xp1, zero))))
    val tactic = ((AxiomCloseT ~ locateSucc(indecisive(true, false, true)) ~ locateAnte(indecisive(true, false, true, true)))*)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
//    while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
//      Thread.sleep(100)
//    }
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }

  def test9(input: String, output: String) {
    import TacticLibrary._
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    val master = ((AxiomCloseT | locateSucc(indecisive(false, true, true)) | locateAnte(indecisive(false, true, true))
      | locateSucc(indecisive(true, true, true)) | locateAnte(indecisive(true, true, true))
      | locateAnte(eqLeft(false)) )*) ~ quantifierEliminationT("Mathematica")
    val tactic = locateAnte(ImplyRightT) & locateSucc(inductionT(Some(PredicateConstant("inv")))) & master
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    Thread.sleep(3000)
    /*while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(100)
      println("Blocked " + Tactics.KeYmaeraScheduler.blocked + " of " + Tactics.KeYmaeraScheduler.maxThreads)
      println("Tasks open: " + Tactics.KeYmaeraScheduler.prioList.length)
    }*/
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }
  def test10(output: String) {
    import TacticLibrary._
    val parse = new KeYmaeraParser()
    val input = "examples/dev/t/tactics/ETCS-essentials.key"
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    val invString = "v^2<=2*b*(m-z)"
    val invInput = "Functions. R b. End.\n ProgramVariables. R v. R m. R z. End.\n Problem.\n " + invString + "End.\n"
    val inv: Formula = parse.runParser(invInput).asInstanceOf[Formula]
    val tactic = master(new Generate(inv), true)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    Thread.sleep(3000)
    /*while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(100)
      println("Blocked " + Tactics.KeYmaeraScheduler.blocked + " of " + Tactics.KeYmaeraScheduler.maxThreads)
      println("Tasks open: " + Tactics.KeYmaeraScheduler.prioList.length)
    }*/
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }
//
//  def test10database {
//    val input = "jsgui/keymaera/resources/input.key"
//    val in = readFile(input)
//    val node = ProverBusinessLogic.addModel(in)
//    println("running tactic on " + node)
//    val tree = ProverBusinessLogic.getSubtree(node)
//    var nTree = tree
//    ProverBusinessLogic.runTactic(ProverBusinessLogic.getTactic(0), node, "0", None)
//    while(tree == nTree) {
//      nTree = ProverBusinessLogic.getSubtree(node)
//      Thread.sleep(100)
//    }
//    println("Result is: " + nTree)
//  }

  def test10a(output: String) {
    import TacticLibrary._
    val parse = new KeYmaeraParser()
    val input = "examples/dev/t/tactics/ETCS-safety.key"
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    val invString = "v^2 - d^2 <= 2*b*(m-z) & d >= 0"
    val invInput = "Functions. R b. End.\n ProgramVariables. R v. R m. R z. R d. End.\n Problem.\n " + invString + "End.\n"
    val inv: Formula = parse.runParser(invInput).asInstanceOf[Formula]
    val tactic = master(new Generate(inv), true)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    Thread.sleep(3000)
    /*while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(100)
      println("Blocked " + Tactics.KeYmaeraScheduler.blocked + " of " + Tactics.KeYmaeraScheduler.maxThreads)
      println("Tasks open: " + Tactics.KeYmaeraScheduler.prioList.length)
    }*/
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }

  def test11(input: String, output: String) {
    import TacticLibrary._
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    val inv = GreaterThan(Real, Variable("x", None, Real), Number(0))
    val tactic = master(new Generate(inv), true)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    Thread.sleep(3000)
    /*while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(100)
      println("Blocked " + Tactics.KeYmaeraScheduler.blocked + " of " + Tactics.KeYmaeraScheduler.maxThreads)
      println("Tasks open: " + Tactics.KeYmaeraScheduler.prioList.length)
    }*/
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
  }

  def testMaster(input: String, output: String) {
    import TacticLibrary._
    val parse = new KeYmaeraParser()
    val i2: Formula = parse.runParser(readFile(input)).asInstanceOf[Formula]
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    val tactic = master(new Generate(True), true)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    Thread.sleep(3000)
    /*while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(100)
      println("Blocked " + Tactics.KeYmaeraScheduler.blocked + " of " + Tactics.KeYmaeraScheduler.maxThreads)
      println("Tasks open: " + Tactics.KeYmaeraScheduler.prioList.length)
    }*/
    val tree = print(r)
    println(tree)
    writeToFile(new File(output), tree)
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

  def printPos(p: PosInExpr): Any =
   p.pos.mkString(",")

  def printNamedSymbol(n: NamedSymbol): String = "\"" + n.name + (n.index match { case Some(j) => "_" + j case _ => "" }) + "\""

  def printForm(formula: Formula): String = {
    var jsonResult: String = ""
    val fn = new ExpressionTraversalFunction {

      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        jsonResult += (e match {
          case True() => "{ \"id\": \"" + printPos(p) + "\", \"name\": \"true\"}"
          case False() => "{ \"id\": \"" + printPos(p) + "\", \"name\": \"false\"}"
          case x@PredicateConstant(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\": " + printNamedSymbol(x.asInstanceOf[PredicateConstant]) + "}"
          case ApplyPredicate(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"apply\", \"children\": [ " + printNamedSymbol(a) + ", "
          case Equals(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"equals\"" + ", \"children\": [ "
          case NotEquals(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"notEquals\"" + ", \"children\": [ "
          case ProgramEquals(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"programEquals\"" + ", \"children\": [ "
          case ProgramNotEquals(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"programNotEquals\"" + ", \"children\": [ "
          case LessThan(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"lt\"" + ", \"children\": [ "
          case LessEqual(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"leq\"" + ", \"children\": [ "
          case GreaterEqual(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"geq\"" + ", \"children\": [ "
          case GreaterThan(d, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"gt\"" + ", \"children\": [ "
          case Not(a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"not\"" + ", \"children\": [ "
          case And(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"and\"" + ", \"children\": [ "
          case Or(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"or\"" + ", \"children\": [ "
          case Imply(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"imply\"" + ", \"children\": [ "
          case Equiv(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"equiv\"" + ", \"children\": [ "
          case Modality(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"modality\"" + ", \"children\": [ "
          case Forall(v, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"forall\", \"variables\": [" + v.map(printNamedSymbol).mkString(",") + "], \"children\": [ "
          case Exists(v, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"exists\", \"variables\": [" + v.map(printNamedSymbol).mkString(",") + "], \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + KeYmaeraPrettyPrinter.stringify(e) + " type " + e.getClass)
        })
        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += (e match {
          case Number(s, i) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"" + i + "\"}"
          case x@Variable(_, _, _) => "{ \"id\": \"" + printPos(p) + "\", \"name\":" + printNamedSymbol(x.asInstanceOf[Variable]) + "}"
          case Apply(a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"apply\", \"children\": [ " + printNamedSymbol(a) + ", "
          case Neg(_, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"neg\"" + ", \"children\": [ "
          case Derivative(_, a) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"derivative\"" + ", \"children\": [ "
          case Add(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"add\"" + ", \"children\": [ "
          case Subtract(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"subtract\"" + ", \"children\": [ "
          case Multiply(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"multiply\"" + ", \"children\": [ "
          case Divide(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"divide\"" + ", \"children\": [ "
          case Exp(_, a, b) => "{ \"id\": \"" + printPos(p) + "\", \"name\":\"Exp\"" + ", \"children\": [ "
          case _ => throw new UnsupportedOperationException("not implemented yet for " + KeYmaeraPrettyPrinter.stringify(e) + " type " + e.getClass)
        })
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
        jsonResult += (e match {
          case ApplyPredicate(a, b) => "]}"
          case Equals(d, a, b) => "]}"
          case NotEquals(d, a, b) => "]}"
          case ProgramEquals(a, b) => "]}"
          case ProgramNotEquals(a, b) => "]}"
          case LessThan(d, a, b) => "]}"
          case LessEqual(d, a, b) => "]}"
          case GreaterEqual(d, a, b) => "]}"
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
        })
        Left(None)
      }

      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        jsonResult += (e match {
          case Apply(a, b) => "]}"
          case Neg(_, a) => "]}"
          case Derivative(_, a) => "]}"
          case Add(_, a, b) => "]}"
          case Subtract(_, a, b) => "]}"
          case Multiply(_, a, b) => "]}"
          case Divide(_, a, b) => "]}"
          case Exp(_, a, b) => "]}"
          case _ =>""
        })
        Left(None)
      }
    }
    ExpressionTraversal.traverse(fn, formula)
    jsonResult
  }

  def print(l: Seq[Formula]): String = (for(f <- l) yield KeYmaeraPrettyPrinter.stringify(f).replaceAll("\\\\", "\\\\\\\\")).mkString(",")
  def print(s: Sequent): String = print(s.ante) + " ==> " + print(s.succ)
  def print(p: ProofNode): String = "{ \"sequent\":\"" + (if(p.children.isEmpty) "??? " else "") + (p.tacticInfo.infos.get("branchLabel") match { case Some(l) => l + ": " case None => "" }) + print(p.sequent) + "\", \"children\": [ " + p.children.map(print).mkString(",") + "]}"
  def print(ps: ProofStep): String = "{\"rule\":\"" + ps.rule.toString + "\", \"children\": [" + ps.subgoals.map(print).mkString(",") + "]" + "}"

}

// vim: set ts=4 sw=4 et:
