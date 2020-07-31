package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context.Context
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._


object ForwardProofChecker {
  private def subst(x: Variable, f: Term, p: Formula): Formula = p.replaceAll(x, f)
  private def invSubst(x: Variable, f: Term, p: Formula): Formula = p.replaceAll(f, x)
  val nullaryBuiltin: Map[String, Formula] = Map("trueI" -> True)
  val unaryBuiltin: Map[String, (String, ForwardArg => Formula)] = Map(
    "andEL"   -> ("andEL (proof: P & Q)", {case ProvedArg(And(l, r)) => l}),
    "andER"   -> ("andER (proof: P & Q)", {case ProvedArg(And(l, r)) => r}),
    "equivEL" -> ("equivEL (proof: P <-> Q)", {case ProvedArg(Equiv(l, r)) => Imply(l, r)}),
    "equivER" -> ("equivER (proof: P <-> Q)", {case ProvedArg(Equiv(l, r)) => Imply(r, l)}),
    "notI"    -> ("notI (proof: P -> False)", {case (ProvedArg(Imply(p, False))) => Not(p)})
  )
  val binaryBuiltin: Map[String, (String, (ForwardArg, ForwardArg) => Formula)] = Map(
    "andI" -> ("andI (proofL: P) (proofR: Q)", {case (ProvedArg(l), ProvedArg(r)) => And(l, r)}),
    "orIL" -> ("orIL (proof: P) (Q : Formula)", {case (ProvedArg(l), ExpressionArg(r: Formula)) => Or(l, r)}),
    "orIR" -> ("orIR (P: Formula) (proof: Q)", {case (ExpressionArg(l: Formula), ProvedArg(r)) => Or(l, r)}),
    "notE" -> ("notE (proofL: !P) (proofR: P)", {case (ProvedArg(Not(p)), ProvedArg(pp)) if p == pp => False}),
    "falseE" -> ("falseE (proof: False) (P: Formula)", {case (ProvedArg(False), ExpressionArg(p: Formula)) => p}),
    "ignoreI" -> ("ignoreI (P: Formula) (proof: Q)", {case (ExpressionArg(p: Formula), ProvedArg(q)) => Imply(p, q)}),
    "allI" -> ("allI (x: Variable) (proof: P)", {case (ExpressionArg(v: Variable), ProvedArg(p)) if !StaticSemantics(p).fv.contains(v) => Forall(List(v), p)}),
    "allE" -> ("allE (proof: forall x, P) (f: Term)", {case (ProvedArg(Forall(xs, p)), ExpressionArg(f: Term)) => subst(xs.head, f, p)}),
    "existsE" -> ("existsE (proofL: exists x, P) (proofR: forall y, P -> Q)", {case (ProvedArg(Exists(List(x), p)), ProvedArg(Forall(List(y), Imply(pp, q)))) if p == pp && x == y && !StaticSemantics(q).fv.contains(x) => q})
  )
  val ternaryBuiltin: Map[String, (String, (ForwardArg, ForwardArg, ForwardArg) => Formula)] = Map(
    "orE"     -> ("orE (proof: A | B) (proofL: A -> C) (proofR: B -> C)", {case (ProvedArg(Or(a,b)), ProvedArg(Imply(aa, c)), ProvedArg(Imply(bb, cc))) if a == aa && b == bb && c == cc => c}),
    "existsI" -> ("existsI (x: Variable) (f: Term) (proof: P(f))", {case (ExpressionArg(x: Variable), ExpressionArg(f: Term), ProvedArg(p)) => Exists(List(x), invSubst(x, f, p))})
  )

  sealed trait ForwardArg
  case class ProvedArg (fml: Formula) extends ForwardArg
  case class ExpressionArg (expr: Expression) extends ForwardArg


  def ptToForwardArg(con: Context, pt: ProofTerm): ForwardArg = {
    pt match {
      case ProofInstance(e) => ExpressionArg(e)
      case _ => ProvedArg(apply(con, pt))
    }
  }

  private def unary(name: String, arg1: ForwardArg): Formula = {
    val (spec, f) = unaryBuiltin(name)
    try {
      f(arg1)
    } catch {
      case t: Throwable =>
        throw ProofCheckException(s"Expected argument: $spec\nBut got ($arg1)", cause = t)
    }
  }

  private def binary(name: String, arg1: ForwardArg, arg2: ForwardArg): Formula = {
    val (spec, f) = binaryBuiltin(name)
    try {
      f(arg1, arg2)
    } catch {
      case t: Throwable =>
        throw ProofCheckException(s"Expected arguments: $spec\nBut got ($arg1) ($arg2)", cause = t)
    }
  }

  private def ternary(name: String, arg1: ForwardArg, arg2: ForwardArg, arg3: ForwardArg): Formula = {
    val (spec, f) = ternaryBuiltin(name)
    try {
      f(arg1, arg2, arg3)
    } catch {
      case t: Throwable =>
        throw ProofCheckException(s"Expected arguments: $spec\nBut got ($arg1) ($arg2) ($arg3)", cause = t)
    }
  }

  // @TODO: Check scope and ghosting
  def apply(con: Context, pt: ProofTerm): Formula = {
    pt match {
      case ProgramVar(x) =>
        val asgns = Context.getAssignments(con, x)
        asgns.reduce(And)
      case ProofVar(s) if nullaryBuiltin.contains(s.name) => nullaryBuiltin(s.name)
      case ProofApp(ProofVar(s), pt1) if unaryBuiltin.contains(s.name) => unary(s.name, ptToForwardArg(con, pt1))
      case ProofApp(ProofApp(ProofVar(s), pt1), pt2) if binaryBuiltin.contains(s.name) =>
        binary(s.name, ptToForwardArg(con, pt1), ptToForwardArg(con, pt2))
      case ProofApp(ProofApp(ProofApp(ProofVar(s), pt1), pt2), pt3) if ternaryBuiltin.contains(s.name) =>
        ternary(s.name, ptToForwardArg(con, pt1), ptToForwardArg(con, pt2), ptToForwardArg(con, pt3))
      case ProofVar(s) =>
        Context.get(con, s) match {
          case Some(fml) =>
            fml
          case None => throw ProofCheckException(s"Undefined proof variable $s")
        }
      case ProofApp(pt, ProofInstance(e)) =>
        apply(con, pt) match {
          case Forall(List(x), p) => USubst(SubstitutionPair(x, e) :: Nil)(p)
          case _ => throw ProofCheckException("Tried to instantiate non-quantifier")
        }
      case ProofApp(pt1, pt2) =>
        (apply(con, pt1), apply(con, pt2)) match {
          case (Imply(p, q), r)  if p == r => throw ProofCheckException(s"Argument $r in proof term does not match expected $p")
          case (Imply(p, q), r)  => q
          case _ => throw ProofCheckException("Tried modus ponens on non-implication")
        }
      case _ => throw ProofCheckException(s"Ill-typed forward proof term $pt")
    }
  }

}
