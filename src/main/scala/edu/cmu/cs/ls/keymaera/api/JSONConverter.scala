package edu.cmu.cs.ls.keymaera.api

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaera.parser.{KeYmaeraPrettyPrinter, ParseSymbols}
import spray.json._
import scala.collection.immutable.Seq
import edu.cmu.cs.ls.keymaera.core.Sequent
import edu.cmu.cs.ls.keymaera.core.PosInExpr
import edu.cmu.cs.ls.keymaera.core.ProofNode.ProofStep

import scala.collection.mutable

// TODO fetch sequents only on demand
object JSONConverter {
  val prettyPrinter = new KeYmaeraPrettyPrinter(ParseSymbols) //todo use appropriate symbol table.

  def convertPos(p: PosInExpr) = JsString(p.pos.mkString(","))

  def convertNamedSymbol(n: NamedSymbol) = JsString(n.name + (n.index match { case Some(j) => "_" + j case _ => "" }))

  def convertFormula(formula: Formula, formulaId: String, nodeId: String): JsObject = {
    val jsonStack = new mutable.Stack[List[JsValue]]

    val fn = new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        e match {
          case True() => /* nothing to do */
          case False() => /* nothing to do */
          case PredicateConstant(_, _) => /* nothing to do */
          case _ => jsonStack.push(List())
        }
        Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case Number(_, _) => /* Nothing to do here */
          case Variable(_, _, _) => /* Nothing to do here */
          case Nothing => /* Nothing to do here */
          case Anything => /* Nothing to do here */
          case _ => jsonStack.push(List())
        }
        Left(None)
      }

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        e match {
          case ProgramConstant(_, _) => /* Nothing to do */
          case DifferentialProgramConstant(_, _) => /* Nothing to do */
          case _ => jsonStack.push(List())
        }
        Left(None)
      }

      override def postF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = {
        val cf = ("nodeId" -> JsString(nodeId)) :: ("id" -> convertPos(p)) :: Nil
        val o = e match {
          case True() => JsObject(("name" -> JsString("true")) +: cf)
          case False() => JsObject(("name" -> JsString("false")) +: cf)
          case x@PredicateConstant(a, b) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[PredicateConstant])) +: cf)
          case ApplyPredicate(a, b) => JsObject(("name" -> JsString("apply")) :: ("function" -> convertNamedSymbol(a)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Equals(d, a, b) => JsObject(("name" -> JsString("equals")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case NotEquals(d, a, b) => JsObject(("name" -> JsString("notEquals")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case ProgramEquals(a, b) => JsObject(("name" -> JsString("programEquals")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case ProgramNotEquals(a, b) => JsObject(("name" -> JsString("programNotEquals")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case LessThan(d, a, b) => JsObject(("name" -> JsString("lt")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case LessEqual(d, a, b) => JsObject(("name" -> JsString("leq")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case GreaterEqual(d, a, b) => JsObject(("name" -> JsString("geq")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case GreaterThan(d, a, b) => JsObject(("name" -> JsString("gt")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Not(a) => JsObject(("name" -> JsString("not")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case And(a, b) => JsObject(("name" -> JsString("and")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Or(a, b) => JsObject(("name" -> JsString("or")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Imply(a, b) => JsObject(("name" -> JsString("imply")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Equiv(a, b) => JsObject(("name" -> JsString("equiv")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case BoxModality(a, b) => JsObject(("name" -> JsString("boxmodality")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case DiamondModality(a, b) => JsObject(("name" -> JsString("diamondmodality")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Forall(v, a) => JsObject(("name" -> JsString("forall")) :: ("variables" -> JsArray(v.map(convertNamedSymbol).toList)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Exists(v, a) => JsObject(("name" -> JsString("exists")) :: ("variables" -> JsArray(v.map(convertNamedSymbol).toList)) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case FormulaDerivative(a) => JsObject(("name" -> JsString("formuladerivative")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
        }
        jsonStack.push(jsonStack.pop() :+ o)
        Left(None)
      }

      override def postT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        val cf = ("nodeId" -> JsString(nodeId)) :: ("id" -> convertPos(p)) :: Nil
        val o = e match {
          case Number(s, i) => JsObject(("name" -> JsString(i.toString())) +: cf)
          case x@Variable(_, _, _) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[Variable])) +: cf)
          case Nothing => JsObject(("name" -> JsString("Nothing")) +: cf)
          case Anything => JsObject(("name" -> JsString("Anything")) +: cf)
          case Apply(a, b) => JsObject(("name" -> JsString("apply")) :: ("children" -> JsArray(convertNamedSymbol(a) :: Nil ++: jsonStack.pop())) :: Nil ++: cf)
          case Neg(_, a) => JsObject(("name" -> JsString("neg")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Derivative(_, a) => JsObject(("name" -> JsString("derivative")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Add(_, a, b) => JsObject(("name" -> JsString("add")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Subtract(_, a, b) => JsObject(("name" -> JsString("subtract")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Multiply(_, a, b) => JsObject(("name" -> JsString("multiply")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Divide(_, a, b) => JsObject(("name" -> JsString("divide")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Exp(_, a, b) => JsObject(("name" -> JsString("exp")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
        }
        jsonStack.push(jsonStack.pop() :+ o)
        Left(None)
      }

      override def postP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = {
        val cf = ("nodeId" -> JsString(nodeId)) :: ("id" -> convertPos(p)) :: Nil
        val o = e match {
          case x@ProgramConstant(_, _) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[ProgramConstant])) +: cf)
          case x@DifferentialProgramConstant(_, _) => JsObject(("name" -> convertNamedSymbol(x.asInstanceOf[DifferentialProgramConstant])) +: cf)
          case Assign(_, _) => JsObject(("name" -> JsString("Assign")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case NDetAssign(_) => JsObject(("name" -> JsString("NDetAssign")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Sequence(_, _) => JsObject(("name" -> JsString("Sequence")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Choice(_, _) => JsObject(("name" -> JsString("Choice")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Test(_) => JsObject(("name" -> JsString("Test")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case Loop(_) => JsObject(("name" -> JsString("Loop")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case _: EmptyODE => JsObject("name" -> JsString("EmptyODE") :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case CheckedContEvolveFragment(_) => JsObject("name" -> JsString("checked=") :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case ContEvolve(_) => JsObject(("name" -> JsString("ContEvolve")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case AtomicODE(_, _) => JsObject(("name" -> JsString("AtomicODE")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case ODEProduct(_, _) => JsObject(("name" -> JsString("ODEProduct")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
          case ODESystem(_, _, _) => JsObject(("name" -> JsString("NFODEProduct")) :: ("children" -> JsArray(jsonStack.pop())) :: Nil ++: cf)
        }
        jsonStack.push(jsonStack.pop() :+ o)
        Left(None)
      }
    }
    jsonStack.push(List())
    ExpressionTraversal.traverse(fn, formula)
    jsonStack.pop().head.asJsObject()
  }

  def convertPosition(pos : Position) = JsObject(
    "kind" -> JsString(if (pos.isAnte) "ante" else "succ"),
    "index" -> JsNumber(pos.getIndex),
    "inExpr" -> convertPos(pos.inExpr)
  )

  def convertRule(rule : Rule) = {
    val cf = ("name" -> JsString(rule.name)) :: Nil
    rule match {
      case r : AssumptionRule => JsObject(("kind" -> JsString("AssumptionRule")) :: ("pos" -> convertPosition(r.pos))
        :: ("assumption" -> convertPosition(r.aPos)) :: Nil ++: cf)
      case r : PositionRule => JsObject(("kind" -> JsString("PositionRule"))
        :: ("pos" -> convertPosition(r.pos)) :: Nil ++: cf)
      case r : TwoPositionRule => JsObject(("kind" -> JsString("TwoPositionRule"))
        :: ("pos1" -> convertPosition(r.pos1)) :: ("pos2" -> convertPosition(r.pos2)) :: Nil ++: cf)
      case _ => JsObject(("kind" -> JsString("UnspecificRule")) +: cf)
    }
  }

  def convert(l: Seq[Formula], ante: String, nodeId: String): JsArray =
    JsArray(l.zipWithIndex.map(f => JsObject(
        "nodeId"  -> JsString(nodeId),
        "id"      -> JsString(ante + ":" + f._2),
        "formula" -> convertFormula(f._1, ante + ":" + f._2, nodeId)
      )).toList)
  def convert(s: Sequent, nodeId: String): JsObject =
    JsObject(
      "nodeId"  -> JsString(nodeId),
      "ante"    -> convert(s.ante, "ante", nodeId),
      "succ"    -> convert(s.succ, "succ", nodeId)
    )
  def convert(id: String, limit: Option[Int], store: ((ProofNode, String) => Unit), printSequent: Boolean)(p: ProofNode): JsObject = {
    store(p, id)
    var fields =
      "id"        -> JsString(id) ::
      "infos"     -> infos(p) ::
      "children"  -> (limit match {
        case Some(l) if l > 0 => JsArray(p.children.zipWithIndex.map(ps => convert(id, limit.map(i => i - 1), ps._1, ps._2, store, printSequent)))
        case _ => JsArray()
      }) :: Nil
    if (printSequent) fields = "sequent"   -> sequent(p, id) :: fields
    JsObject(fields)
  }
  def convert(id: String, limit: Option[Int], ps: ProofStep, i: Int, store: ((ProofNode, String) => Unit), printSequent: Boolean): JsObject =
    JsObject(
      "rule"      -> convertRule(ps.rule),
      "id"        -> JsNumber(i),
      "children"  -> subgoals(id, limit, store, printSequent)(ps)
    )

  def convert(id: String, filter: (ProofStepInfo => Boolean), store: (ProofNode, String) => Unit, printSequent: Boolean)(p: ProofNode): JsObject = {
    store(p, id)
    var fields =
      "id"       -> JsString(id) ::
      "infos"    -> infos(p) ::
      "children" -> JsArray(p.children.zipWithIndex.filter(ps => filter(ps._1.tacticInfo)).map(ps => convert(id, filter, ps._1, ps._2, store, printSequent))) :: Nil
    if (printSequent) fields = "sequent"  -> sequent(p, id) :: fields
    JsObject(fields)
  }

  def convert(id: String, filter: (ProofStepInfo => Boolean), ps: ProofStep, i: Int, store: (ProofNode, String) => Unit, printSequent: Boolean): JsObject =
    JsObject(
      "rule"      -> convertRule(ps.rule),
      "id"        -> JsNumber(i),
      "children"  -> subgoals(id, filter, store, printSequent)(ps)
    )

  private def infos(p: ProofNode): JsArray = JsArray(p.tacticInfo.infos.map(s =>
    JsObject(
      "key"   -> JsString(s._1),
      "value" -> JsString(s._2)
    )).toList
  )
  private def sequent(p: ProofNode, nodeId: String) = convert(p.sequent, nodeId)
  private def updateIndex(id: String, limit: Option[Int], store: (ProofNode, String) => Unit, printSequent: Boolean)(in: (ProofNode, Int)): JsObject = convert(id + "_" + in._2, limit, store, printSequent)(in._1)
  private def updateIndex(id: String, filter: (ProofStepInfo => Boolean), store: (ProofNode, String) => Unit, printSequent: Boolean)(in: (ProofNode, Int)): JsObject = convert(id + "_" + in._2, filter, store, printSequent)(in._1)
  private def subgoals(id: String, limit: Option[Int], store: (ProofNode, String) => Unit, printSequent: Boolean)(ps: ProofStep): JsArray = JsArray(ps.subgoals.zipWithIndex.map(updateIndex(id, limit, store, printSequent)))
  private def subgoals(id: String, filter: (ProofStepInfo => Boolean), store: (ProofNode, String) => Unit, printSequent: Boolean)(ps: ProofStep): JsArray = JsArray(ps.subgoals.zipWithIndex.map(updateIndex(id, filter, store, printSequent)))

  //def apply(p: ProofNode): String = print("", None, (_, _) => ())(p)
  def apply(p: ProofNode, id: String, limit: Int, store: (ProofNode, String) => Unit, printSequent: Boolean): JsObject = convert(id, Some(limit), store, printSequent)(p)
  def apply(p: ProofNode, id: String, filter: (ProofStepInfo => Boolean), store: ((ProofNode, String) => Unit), printSequent: Boolean): JsObject = convert(id, filter, store, printSequent)(p)

}
