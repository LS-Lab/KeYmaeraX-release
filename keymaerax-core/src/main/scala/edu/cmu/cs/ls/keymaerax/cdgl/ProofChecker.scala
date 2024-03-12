/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Main CdGL proof-checking algorithm.
 * @note
 *   Soundness-critical
 * @author
 *   Brandon Bohrer
 */
package edu.cmu.cs.ls.keymaerax.cdgl

import edu.cmu.cs.ls.keymaerax.btactics.{Integrator, ToolProvider}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal._
import edu.cmu.cs.ls.keymaerax.tools.ext.QETacticTool
import edu.cmu.cs.ls.keymaerax.btactics.helpers._

/**
 * Raised when a proof term does not proof check
 * @param msg
 *   Description of error
 */
case class ProofException(msg: String, context: Context = Context.empty) extends Exception {
  override def toString: String =
    if (context.asList.isEmpty) { msg }
    else {
      val ctxt = context.toString()
      s"Message: $msg\nContext: $ctxt"
    }
}

/**
 * Checks proof terms.
 * @see
 *   [[ProofChecker.apply]]
 */
object ProofChecker {
  // Note: we will likely want some normalization for formula and term derivatives here, so leaving the code as is until then.
  private def standardizeFormula(fml: Formula): Formula = fml
  private def standardizeTerm(f: Term): Term = f

  /**
   * @see
   *   [[kaisar.ProofChecker]]
   * @return
   *   compute differential of formula [[p]]
   */
  def deriveFormula(p: Formula, map: Map[Variable, Term]): Formula = { formulaDerivative(standardizeFormula(p), map) }

  /** @return compute differential of term [[f]] */
  def deriveTerm(f: Term, map: Map[Variable, Term]): Term = { termDerivative(standardizeTerm(f), map) }

  def formulaDerivative(p: Formula, map: Map[Variable, Term]): Formula = {
    p match {
      case And(p, q) => And(formulaDerivative(p, map), formulaDerivative(q, map))
      case Or(p, q) => And(formulaDerivative(p, map), formulaDerivative(q, map))
      case Exists(List(x), p) => Forall(List(x), formulaDerivative(p, map))
      case Forall(List(x), p) => Forall(List(x), formulaDerivative(p, map))
      case Equal(f, g) => Equal(deriveTerm(f, map), deriveTerm(g, map))
      case NotEqual(f, g) => Equal(deriveTerm(f, map), deriveTerm(g, map))
      case Less(f, g) => LessEqual(deriveTerm(f, map), deriveTerm(g, map))
      case LessEqual(f, g) => LessEqual(deriveTerm(f, map), deriveTerm(g, map))
      case Greater(f, g) => GreaterEqual(deriveTerm(f, map), deriveTerm(g, map))
      case GreaterEqual(f, g) => GreaterEqual(deriveTerm(f, map), deriveTerm(g, map))
      case p => throw ProofException(s"Derivative of $p not supported")
    }
  }

  /** @return compute differential of formula [[p]] */
  def deriveFormula(p: Formula, ode: DifferentialProgram): Formula = {
    val map = DifferentialHelper.atomicOdes(ode).map({ case AtomicODE(DifferentialSymbol(x), f) => (x, f) }).toMap
    deriveFormula(p, map)
  }

  private def termDerivative(e: Term, map: Map[Variable, Term]): Term = {
    e match {
      case _: Number => Number(0)
      case x: BaseVariable => map.get(x) match {
          case Some(f) => f
          case None => Number(0)
        }
      case dx: DifferentialSymbol => throw ProofException(s"Double differential ($dx)' not supported")
      case Plus(f, g) => Plus(termDerivative(f, map), termDerivative(g, map))
      case Times(f, g) => Plus(Times(termDerivative(f, map), g), Times(f, termDerivative(g, map)))
      case Divide(f, g) =>
        Divide(Minus(Times(termDerivative(f, map), g), Times(f, termDerivative(g, map))), Power(g, Number(2)))
      case Power(f, n: Number) =>
        if (n.value == 0) throw ProofException(s"Cannot derive $f^0")
        else Times(Times(n, Power(f, Number(n.value - 1))), termDerivative(f, map))
      case Power(f, Divide(n: Number, d: Number)) =>
        if (n.value == 0) throw ProofException(s"Cannot derive $f^0")
        else if (d.value == 0) throw ProofException(s"Division by zero when deriving $e")
        else Times(Times(Divide(n, d), Power(f, Divide(Number(n.value - d.value), d))), termDerivative(f, map))
      case _: Power => throw ProofException("Must simplify power to f^n or f^(n/d) before deriving")
      case Neg(f) => Neg(termDerivative(f, map))
      case Minus(f, g) => Minus(termDerivative(f, map), termDerivative(g, map))
      case Pair(f, g) => Pair(termDerivative(f, map), termDerivative(g, map))
      case p => throw ProofException(s"Derivative of $p not supported")
    }
  }

  /** @return compute differential of term [[f]] */
  def deriveTerm(e: Term, ode: DifferentialProgram): Term = {
    val map = DifferentialHelper.atomicOdes(ode).map({ case AtomicODE(DifferentialSymbol(x), f) => (x, f) }).toMap
    deriveTerm(e, map)
  }

  /** @return whether [[p]] contains only conjunctions and universals over comparisons */
  private def isConjunctive(p: Formula): Boolean = {
    p match {
      case True | _: Less | _: LessEqual | _: Equal | _: NotEqual | _: Greater | _: GreaterEqual => true
      case And(p, q) => isConjunctive(p) && isConjunctive(q)
      case Forall(xs, f) => isConjunctive(f)
      case _ => false
    }
  }

  /** @return whether [[p]] is admissible as an assumption in constructive QE */
  private def isAssumptive(p: Formula): Boolean = {
    p match {
      case True | _: Less | _: LessEqual | _: Equal | _: NotEqual | _: Greater | _: GreaterEqual => true
      case And(p, q) => isAssumptive(p) && isAssumptive(q)
      case Forall(xs, f) => isAssumptive(f)
      // It's okay to assume p | q because constructive p | q implies classical p | q, but can only assume p | q in
      // positive polarity, e.g. not okay to have assumption (\forall x (a(x) | b(x)) -> c(x))
      case Or(l, r) => isAssumptive(l) && isAssumptive(r)
      case Imply(l, r) => isConjunctive(l) && isAssumptive(r)
    }
  }

  /**
   * @param p
   *   formula of first-order constructive arithmetic
   * @return
   *   whether formula is constructively valid
   */
  // @TODO: More detailed error handling
  def qeValid(p: Formula): Boolean = {
    val t: QETacticTool = ToolProvider.provider.qeTool().get
    val (pre, post) = p match {
      case Imply(p, q) => (p, q)
      case p => (True, p)
    }
    // Is formula classically valid?
    val freevars = StaticSemantics(Imply(pre, post)).fv.toSet
    val closure = freevars.foldLeft[Formula](Imply(pre, post))({ case (acc, x) =>
      Forall(collection.immutable.Seq(x), acc)
    })
    val fact = t.qe(closure).fact
    val conclusion = fact.conclusion
    val isFormula = conclusion.ante.isEmpty && conclusion.succ.length == 1
    val assumpPre = isAssumptive(pre)
    val conjPost = isConjunctive(post)
    val isProved = fact.isProved
    fact.conclusion.succ.headOption match {
      // If formula is conjunctive, then classical and constructive truth agree
      case Some(Equiv(_, True)) => isFormula && assumpPre && conjPost && isProved
      case proved => false
    }
  }

  // Map recording the maximum index, if any, with which each base or differential variable has appeared so far
  type Indices = Map[Either[String, String], Option[Int]]

  /**
   * Traverse expression and record indices with which each variable appears
   * @param init
   *   Indices of variables seen so far
   * @param e
   *   Expression in which to collect variable references
   * @return
   *   Index map including occurrences in e
   */
  private def collectVars(init: Indices, e: Expression): Indices = {
    var acc: Indices = init
    val etf = new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = {
        e match {
          case BaseVariable(x, ind, kind) => (acc.get(Left(x)), ind) match {
              case (None, _) => acc = acc.+((Left(x), ind))
              case (Some(Some(i)), Some(j)) => acc = acc.+((Left(x), Some(Math.max(i, j))))
              case (Some(_), _) => acc = acc.+((Left(x), ind))
            }
          case DifferentialSymbol(BaseVariable(x, ind, kind)) => (acc.get(Right(x)), ind) match {
              case (None, _) => acc = acc.+((Right(x), ind))
              case (Some(Some(i)), Some(j)) => acc = acc.+((Right(x), Some(Math.max(i, j))))
              case (Some(_), _) => acc = acc.+((Right(x), ind))
            }
          case _ => ()
        }
        Left(None)
      }
    }
    e match {
      case e: Program => ExpressionTraversal.traverse(etf, e)
      case e: Term => ExpressionTraversal.traverse(etf, e)
      case e: Formula => ExpressionTraversal.traverse(etf, e)
      case e => throw ProofException(s"Unexpected expression $e in ghostVars")
    }
    acc
  }

  /** Collect variable occurrences in list of expressions */
  private def collectVars(es: List[Expression]): Indices = { es.foldLeft[Indices](Map())(collectVars) }

  /** @return whether x is a fresh variable given the occurrences of map */
  private def freshIn(x: Variable, map: Indices): Boolean = {
    x match {
      case BaseVariable(name, ind, sort) => (map.get(Left(name)), ind) match {
          case (None, _) => true
          case (Some(None), Some(_)) => true
          case (Some(Some(i)), Some(j)) => i < j
          case _ => false
        }
      case DifferentialSymbol(BaseVariable(name, ind, sort)) => (map.get(Right(name)), ind) match {
          case (None, _) => true
          case (Some(None), Some(_)) => true
          case (Some(Some(i)), Some(j)) => i < j
          case _ => false
        }

    }
  }

  /** @return whether x is fresh in all es */
  private def freshIn(x: Variable, taboos: List[Expression]): Boolean = {
    val map: Indices = collectVars(taboos)
    freshIn(x, map)
  }

  /** @return whether all xs fresh in all es */
  private def freshIn(xs: List[Variable], taboos: List[Expression]): Boolean = { xs.forall(freshIn(_, taboos)) }

  /** @return x_i for some i which makes x_i fresh in map */
  private def freshOf(x: Variable, map: Indices): Variable = {
    x match {
      case BaseVariable(name, ind, sort) => map.get(Left(name)) match {
          case None => x
          case Some(None) => BaseVariable(name, Some(0), sort)
          case Some(Some(i)) => BaseVariable(name, Some(i + 1), sort)
        }
      case DifferentialSymbol(BaseVariable(name, ind, sort)) => map.get(Right(name)) match {
          case None => x
          case Some(None) => DifferentialSymbol(BaseVariable(name, Some(0), sort))
          case Some(Some(i)) => DifferentialSymbol(BaseVariable(name, Some(i + 1), sort))
        }
    }
  }

  /**
   * @param explicit
   *   Optional, explicit variable annotation
   * @param base
   *   Base variable which can be reindexed to find ghost
   * @param taboos
   *   Expressions in which ghost must be fresh
   * @return
   *   ghost variable fresh in taboos, either [[explicit]] or renaming of [[base]].
   * @throws [[ProofException]]
   *   if [[explicit]] ghost is not fresh
   */
  def ghostVar(explicit: Option[Variable], base: Variable, taboos: List[Expression]): Variable = {
    val map: Indices = collectVars(taboos)
    explicit match {
      case Some(x) =>
        if (freshIn(x, map)) { x }
        else { throw ProofException(s"Proof term specified ghost variable $x which was not fresh in $taboos") }
      case None => freshOf(base, map)
    }
  }

  /**
   * @param explicit
   *   Optional, explicit variable annotations
   * @param base
   *   Base variables which can be reindexed to find ghost
   * @param taboos
   *   Expressions in which ghosts must be fresh
   * @return
   *   ghost variables fresh in taboos, either [[explicit]] or renamings of [[base]].
   * @throws [[ProofException]]
   *   if [[explicit]] ghosts are not fresh
   */
  def ghostVars(explicit: Option[List[Variable]], base: List[Variable], taboos: List[Expression]): List[Variable] = {
    val xys: List[(Option[Variable], Variable)] = explicit match {
      case None => base.map((None, _))
      case Some(xs) => xs.zip(base).map({ case (x, y) => (Some(x), y) })
    }
    xys.map({ case (x, y) => ghostVar(x, y, taboos) })
  }

  /**
   * Solves an ODE
   * @param tvar
   *   Variable for time
   * @param xys
   *   Renamings for bound variables of ODE
   * @param ode
   *   ODE to solve
   * @return
   *   solution terms for each bound variable of ODE
   * @throws [[ProofException]]
   *   if ode is not integrable
   */
  def solve(tvar: Variable, xys: List[(Variable, Variable)], ode: ODESystem): List[(Variable, Term)] = {
    try {
      val initialConditions = xys.toMap
      val solutions = Integrator(initialConditions, tvar, ode)
      solutions.map({
        case Equal(x: Variable, f) => (x, f)
        case p => throw ProofException(s"Solve expected $p to have shape x=f")
      })
    } catch { case e: Exception => throw ProofException(s"ODE $ode not integrable") }
  }

  /**
   * Checks whether G |- M : P for some P
   * @param G
   *   Context in which to check term
   * @param M
   *   Term to check
   * @return
   *   Unique P such that G |- M : P, if any
   * @throws [[ProofException]]
   *   if M does not check in context G
   */
  def apply(G: Context, M: Proof): Formula = {
    val Context(con) = G
    M match {
      case Triv() => True
      case DTestI(left, right) =>
        val P = apply(G, left)
        val Q = apply(G, right)
        Diamond(Test(P), Q)
      case DTestEL(child) => apply(G, child) match {
          case Diamond(Test(p), _) => p
          case p => throw ProofException(s"[?]EL not applicable to formula ${p}", G)
        }
      case DTestER(child) => apply(G, child) match {
          case Diamond(Test(_), q) => q
          case p => throw ProofException(s"[?]ER not applicable to formula ${p}", G)
        }
      case DAssignI(asgn @ Assign(x, f), child, yOpt) =>
        val y = ghostVar(yOpt, x, f :: G.asList)
        val ren = URename(x, y)
        val f1 = ren(f)
        val G1 = G.rename(x, y).extend(Equal(x, f1))
        val P = apply(G1, child)
        val vars = (G.freevars ++ StaticSemantics(asgn).fv ++ StaticSemantics(P).fv).toSet
        if (x != y && vars.contains(y)) { throw ProofException(s"Ghost variable ${y} not fresh in <:=>I", G1) }
        Diamond(Assign(x, f), P)
      case DAssignE(child) => apply(G, child) match {
          case Diamond(Assign(x, f), pp) => SubstitutionHelper.replaceFree(pp)(x, f)
          case p => throw ProofException(s"[: =]E not applicable to formula $p", G)
        }
      case DRandomI(Assign(x, f), child, yOpt) =>
        val y = ghostVar(yOpt, x, f :: G.asList)
        val f1 = URename(x, y)(f)
        val G1 = G.rename(x, y).extend(Equal(x, f1))
        val P = apply(G1, child)
        if (x != y && StaticSemantics(P).fv.contains(y)) {
          throw ProofException(s"Postcondition $P must not mention ghost $y in <:*>I", G1)
        }
        Diamond(AssignAny(x), P)
      case DRandomE(left, right, yOpt) => apply(G, left) match {
          case Diamond(AssignAny(x), q) =>
            val y = ghostVar(yOpt, x, q :: G.asList)
            val G1 = G.rename(x, y).extend(q)
            val p = apply(G1, right)
            if (!StaticSemantics(p).fv.intersect(Set(x, y)).isEmpty) {
              throw ProofException(s"Postcondition $p cannot mention $x or $y in rule <: *>E", G1)
            } else p
          case p => throw ProofException(s"Rule <:*>E not applicable to formula $p", G)
        }
      case ExistsI(Assign(x, f), child: Proof, yOpt: Option[Variable]) =>
        val y = ghostVar(yOpt, x, f :: G.asList)
        val f1 = URename(x, y)(f)
        val G1 = G.rename(x, y).extend(Equal(x, f1))
        val P = apply(G1, child)
        if (x != y && StaticSemantics(P).fv.contains(y)) {
          throw ProofException(s"Postcondition $P must not mention ghost $y in existsI", G1)
        }
        Exists(List(x), P)
      case ExistsE(left: Proof, right: Proof, yOpt: Option[Variable]) => apply(G, left) match {
          case Exists(List(x), q) =>
            val y = ghostVar(yOpt, x, q :: G.asList)
            val G1 = G.rename(x, y).extend(q)
            val p = apply(G1, right)
            if (!StaticSemantics(p).fv.intersect(Set(x, y)).isEmpty) {
              throw ProofException(s"Postcondition $p cannot mention $x or $y in rule <: *>E", G1)
            } else p
          case p => throw ProofException(s"Rule <: *>E not applicable to subgoal $p", G)
        }
      case DComposeI(child) => apply(G, child) match {
          case Diamond(a, Diamond(b, p)) => Diamond(Compose(a, b), p)
          case p => throw ProofException(s"Rule <;>I not applicable to subgoal $p", G)
        }
      case DComposeE(child) => apply(G, child) match {
          case Diamond(Compose(a, b), p) => Diamond(a, Diamond(b, p))
          case p => throw ProofException(s"Rule <;>E not applicable to subgoal $p", G)
        }
      case DChoiceIL(b, child) => apply(G, child) match {
          case Diamond(a, p) => Diamond(Choice(a, b), p)
          case p => throw ProofException(s"Rule <++>IL not applicable to subgoal $p", G)
        }

      case DChoiceIR(a, child) => apply(G, child) match {
          case Diamond(b, p) => Diamond(Choice(a, b), p)
          case p => throw ProofException(s"Rule <++>IR not applicable to subgoal $p", G)
        }
      case DChoiceE(child, left, right) => apply(G, child) match {
          case Diamond(Choice(a, b), p) =>
            val pp = apply(G.extend(Diamond(a, p)), left)
            val qq = apply(G.extend(Diamond(b, p)), right)
            if (pp != qq) { throw ProofException(s"Postconditions $pp and $qq do not match in <++>E", G) }
            pp
          case p => throw ProofException(s"Rule <++>E not applicable to subgoal $p", G)
        }
      case DStop(child, a) =>
        val p = apply(G, child)
        Diamond(Loop(a), p)
      case DGo(child) => apply(G, child) match {
          case Diamond(a, Diamond(Loop(b), p)) =>
            if (a != b) throw ProofException(s"Programs $a and $b do not match in <*>G", G)
            Diamond(Loop(a), p)
          case p => throw ProofException(s"Rule <*>G not applicable to subgoal $p", G)
        }
      case DRepeatI(metric, init, step, post) =>
        val variant = apply(G, init)
        val fact = apply(G, metric.witness)
        metric.setFact(fact)
        apply(Context(List(And(metric.ghost, metric.nonZero), variant)), step) match {
          case Diamond(a, p2) =>
            val p3 = apply(Context(List(metric.isZero, variant)), post)
            val expectedPost = And(variant, Or(metric.isZero, metric.decreased))
            val taboos = (variant :: p3 :: G.asList).foldLeft[SetLattice[Variable]](SetLattice.bottom)({
              case (acc, f) => acc.++(StaticSemantics(f).fv)
            })
            if (p2 != expectedPost) {
              throw ProofException(s"Rule <*>I expected inductive step postcondition $expectedPost, got $p2", G)
            } else if (!metric.isAdmissible(StaticSemantics(a).bv.toSet, taboos.toSet)) {
              throw ProofException(s"Metric $metric must be admissible in <*>I", G)
            }
            Diamond(Loop(a), p3)
          case p => throw ProofException(s"Rule <*>I not applicable to subgoal $p", G)
        }
      case DRepeatE(child, post, step) => apply(G, child) match {
          case Diamond(Loop(a), p) =>
            val p1 = apply(Context(List(p)), post)
            val p2 = apply(Context(List(Diamond(a, p1))), step)
            if (p1 != p2) throw ProofException(s"Rule <*>E postconditions $p1 and $p2 did not match", G)
            p1
          case p => throw ProofException(s"Rule <*>E not applicable to subgoal $p", G)
        }
      case DDualI(child) => apply(G, child) match {
          case Box(a, p) => Diamond(Dual(a), p)
          case p => throw ProofException(s"Rule <d>I not applicable to subgoal $p", G)
        }
      case DDualE(child) => apply(G, child) match {
          case Diamond(Dual(a), p) => Box(a, p)
          case p => throw ProofException(s"Rule <d>E not applicable to subgoal $p", G)
        }
      case DSolve(ode, post, durPos, dc, child, s, t, ysOpt) =>
        val tOld = ghostVar(None, t, ode :: G.asList)
        val sOld = ghostVar(None, s, t :: tOld :: ode :: G.asList)
        val t0 = if (t == tOld) Number(0) else tOld
        val xs = StaticSemantics(ode)
          .bv
          .toSet
          .toList
          .filter({
            case _: BaseVariable => true
            case _ => false
          }: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, List(ode))
        val xys = (if (t == tOld) Nil else List((t, tOld))) ++ (if (s == sOld) Nil else List((s, sOld))) ++ xs.zip(ys)
        val sols = solve(t, xys, ode)
        val G1 = xys.foldLeft(G)({ case (acc, (x, y)) => acc.rename(x, y) })
        apply(G, durPos) match {
          case GreaterEqual(dur, n: Number) =>
            if (n.value != 0) { throw ProofException(s"<'> duration must be proven >= 0, had ${n.value} instead", G) }
            if (
              StaticSemantics(dur).intersect(StaticSemantics(ode).bv.+(t).+(s).+(tOld).+(sOld).++(ys)).toSet.nonEmpty
            ) { throw ProofException(s"<'> requires admissible duration $dur", G) }
            val G2 = G1.extend(And(LessEqual(Number(0), s), LessEqual(s, dur)))
            val dcFml = apply(G2, dc)
            val expectedDC = ((t, s) :: sols).foldRight[Formula](ode.constraint)({ case ((x, f), acc) =>
              SubstitutionHelper.replaceFree(acc)(x, f)
            })
            if (dcFml != expectedDC) {
              throw ProofException(
                s"<'> DC step with constraint ${ode.constraint} expected constraint $expectedDC, got $dcFml",
                G2,
              )
            }
            val postSub = apply(G1, child)
            val expectedSub = ((t, dur) :: sols).foldRight[Formula](post)({ case ((x, f), acc) =>
              SubstitutionHelper.replaceFree(acc)(x, f)
            })
            if (postSub != expectedSub) {
              throw ProofException(
                s"<'> Post step with postcondition $post expected subgoal postcondition $expectedSub, got $postSub",
                G1,
              )
            }
            if (!StaticSemantics(post).fv.intersect((s :: tOld :: sOld :: ys).toSet).isEmpty) {
              throw ProofException(s"<'> ghost variables must be fresh in postcondition $post", G1)
            }
            Diamond(ode, post)
          case p => throw ProofException(s"<'> duration must be proven >= 0, had $p instead", G)
        }
      case DV(const, dur, rate, post, t, ysOpt) =>
        val tOld = ghostVar(None, t, G.asList)
        val t0 = if (t == tOld) Number(0) else tOld
        val G1 = G.rename(t, tOld).extend(Equal(t, t0))
        apply(G1, const) match {
          case And(GreaterEqual(d1, n1: Number), GreaterEqual(f, Neg(Times(d2, v1)))) =>
            if (d1 != d2) throw ProofException(s"Durations $d1 and $d2 must be equal in DV", G1)
            else if (n1.value != 0) throw ProofException(s"Expected duration >=0 in DV, got $n1", G1)
            apply(G1, dur) match {
              case Diamond(
                    ODESystem(tode @ DifferentialProduct(AtomicODE(DifferentialSymbol(t1), one: Number), ode1), q1),
                    td @ GreaterEqual(Minus(t2, tInit), d3),
                  ) =>
                if (t1 != t || one.value != 1) {
                  throw ProofException(s"DV expected ODE shape $t'=1, x'=f, got $tode", G1)
                } else if (t2 != t || d3 != d1) {
                  throw ProofException(s"DV expected second postcondition t>=d, got $td", G1)
                } else if (tInit != t0) { throw ProofException(s"DV expected initial time $t0, got $tInit", G1) }
                else if (!StaticSemantics(d1).intersect(StaticSemantics(tode).bv.+(tOld)).isEmpty) {
                  throw ProofException(
                    s"DV duration $d1 must not mention time variables $t, $tOld or bound variables of $tode",
                    G1,
                  )
                } else if (!StaticSemantics(v1).intersect(StaticSemantics(tode).bv.+(tOld)).isEmpty) {
                  throw ProofException(
                    s"DV rate $v1 must be constant with respect to time $t, $tOld and bound variables of $tode",
                    G1,
                  )
                }
                apply(G, rate) match {
                  case Box(ODESystem(ode2, q2), GreaterEqual(fdiff, v2)) =>
                    val map = DifferentialHelper
                      .atomicOdes(ode1)
                      .map({ case AtomicODE(DifferentialSymbol(x), f) => (x, f) })
                      .toMap
                    val xs = StaticSemantics(ode1)
                      .bv
                      .toSet
                      .toList
                      .filter({
                        case _: BaseVariable => true
                        case _ => false
                      }: (Variable => Boolean))
                    val ys = ghostVars(ysOpt, xs, v1 :: d1 :: q1 :: f :: ode1 :: G.asList)
                    val fdiffExpected = deriveTerm(f, map)
                    if (ode1 != ode2) { throw ProofException(s"ODEs $ode1 and $ode2 must match in DV", G) }
                    else if (q1 != q2) { throw ProofException(s"Constraints $q1 and $q2 must match in DV", G) }
                    else if (v1 != v2) { throw ProofException(s"Rates $v1 and $v2 must match in DV", G) }
                    else if (fdiff != fdiffExpected) {
                      throw ProofException(s"DV expected derivative of $f, i.e., $fdiffExpected, got $fdiff", G)
                    }
                    val G1 = G.renames(xs, ys).extend(GreaterEqual(f, Number(0)))
                    val p = apply(G1, post)
                    if (!StaticSemantics(p).fv.intersect(ys.toSet.+(tOld)).isEmpty) {
                      throw ProofException(s"Ghost variables not fresh in postcondition in DV", G1)
                    }
                    Diamond(ODESystem(ode1, q1), p)
                  case p => throw ProofException(s"Third DV subgoal must be shape <x'=f&Q>f'>=0, was $p", G1)
                }
              case p => throw ProofException(s"Second DV subgoal must be shape <t'=1, x'=f&Q>t>=d, was $p", G)
            }
          case p => throw ProofException(s"First DV subgoal must be shape d>=0 & v>=0 & f>=-dv, was $p", G)
        }
      case BTestI(fml, child) =>
        val p1 = apply(G.extend(fml), child)
        Box(Test(fml), p1)
      case BTestE(left, right) => apply(G, left) match {
          case Box(Test(p1), q) =>
            val p2 = apply(G, right)
            if (p1 != p2) throw ProofException(s"Assumption $p2 does not match expected $p1 in [?]E", G)
            q
          case p => throw ProofException(s"Rule [?]E not applicable to subogal $p", G)
        }
      case BAssignI(asgn @ Assign(x, f), child, yOpt) =>
        val y = ghostVar(yOpt, x, f :: G.asList)
        val ren = URename(x, y)
        val f1 = ren(f)
        val G1 = G.rename(x, y).extend(Equal(x, f1))
        val P = apply(G1, child)
        val vars = (G.freevars ++ StaticSemantics(asgn).fv ++ StaticSemantics(P).fv).toSet
        if (x != y && vars.contains(y)) { throw ProofException(s"Ghost variable ${y} not fresh in [:=]I", G) }
        Box(Assign(x, f), P)
      case BAssignE(child) => apply(G, child) match {
          case Box(Assign(x, f), pp) => SubstitutionHelper.replaceFree(pp)(x, f)
          case p => throw ProofException(s"Rule [: =]E does not apply to formula $p", G)
        }
      case BRandomI(x, child, yOpt) =>
        val y = ghostVar(yOpt, x, G.asList)
        val pp = apply(G.rename(x, y), child)
        if (y != x && StaticSemantics(pp).fv.contains(y)) {
          throw ProofException(s"Ghost variable ${y} not fresh in $pp in rule [:*]I", G)
        }
        Box(AssignAny(x), pp)
      case BRandomE(child, f) => apply(G, child) match {
          case Box(AssignAny(x), pp) => SubstitutionHelper.replaceFree(pp)(x, f)
          case p => throw ProofException(s"Rule [: *]E does not apply to formula $p", G)
        }
      case ForallI(x, child, yOpt) =>
        val y = ghostVar(yOpt, x, G.asList)
        val pp = apply(G.rename(x, y), child)
        if (StaticSemantics(pp).fv.contains(y)) {
          throw ProofException(s"Ghost variable ${y} not fresh in $pp in rule forallI", G)
        }
        Forall(List(x), pp)
      case ForallE(child: Proof, f: Term) => apply(G, child) match {
          case Forall(List(x), pp) => SubstitutionHelper.replaceFree(pp)(x, f)
          case p => throw ProofException(s"Rule forallE does not apply to formula $p", G)
        }
      case BComposeI(child) => apply(G, child) match {
          case Box(a, Box(b, p)) => Box(Compose(a, b), p)
          case p => throw ProofException(s"Rule [;]I does not apply to formula $p", G)
        }
      case BComposeE(child) => apply(G, child) match {
          case Box(Compose(a, b), p) => Box(a, Box(b, p))
          case p => throw ProofException(s"Rule [;]E does not apply to formula $p", G)
        }
      case BChoiceI(left, right) => apply(G, left) match {
          case Box(a, p) => apply(G, right) match {
              case Box(b, q) =>
                if (p != q) throw ProofException(s"Conjunct postconditions $p and $q differ in [++]I", G)
                else Box(Choice(a, b), p)
              case r => throw ProofException(s"Rule [++]I not applicable with right conjunct $r", G)
            }
          case l => throw ProofException(s"Rule [++]I not applicable with left conjunct $l", G)
        }
      case BChoiceEL(child) => apply(G, child) match {
          case Box(Choice(a, _), p) => Box(a, p)
          case p => throw ProofException(s"Rule [++]EL not applicable to formula $p", G)
        }
      case BChoiceER(child) => apply(G, child) match {
          case Box(Choice(_, b), p) => Box(b, p)
          case p => throw ProofException(s"Rule [++]ER not applicable to formula $p", G)
        }
      case BRepeatI(pre, step, post, a1, ysOpt) =>
        val j1 = apply(G, pre)
        val xs = StaticSemantics(a1).bv.toSet.toList.filter(_.isInstanceOf[BaseVariable])
        val ys = ghostVars(ysOpt, xs, j1 :: a1 :: G.asList)
        val G1 = G.renames(xs, ys).extend(j1)
        apply(G1, step) match {
          case Box(a2, j2) =>
            if (a1 != a2) { throw ProofException(s"Expected program $a1 and actual $a2 in [*]I must be the same", G1) }
            else if (j1 != j2) {
              throw ProofException(
                s"Base case invariant $j1 and inductive step invariant $j2 in [*]I must be the same",
                G1,
              )
            }
            val pp = apply(G1, post)
            if (!StaticSemantics(pp).fv.intersect(ys.toSet).isEmpty) {
              throw ProofException(s"Ghost variable not fresh ", G1)
            }
            Box(Loop(a1), pp)
          case p => throw ProofException(s"Rule [*]I not applicable to formula $p", G1)
        }
      case BRepeatEL(child) => apply(G, child) match {
          case Box(Loop(_), p) => p
          case p => throw ProofException(s"Rule [*]EL not applicable to formula $p", G)
        }
      case BRepeatER(child) => apply(G, child) match {
          case Box(Loop(a), p) => Box(a, Box(Loop(a), p))
          case p => throw ProofException(s"Rule [*]ER not applicable to formula $p", G)
        }
      case BDualI(child) => apply(G, child) match {
          case Diamond(a, p) => Box(Dual(a), p)
          case p => throw ProofException(s"Rule [d]I not applicable to formula $p", G)
        }
      case BDualE(child) => apply(G, child) match {
          case Box(Dual(a), p) => Diamond(a, p)
          case p => throw ProofException(s"Rule [d]E not applicable to formula $p", G)
        }
      case BSolve(ode, post, child, s, t, ysOpt) =>
        val tOld = ghostVar(None, t, G.asList)
        val sOld = ghostVar(None, s, t :: tOld :: G.asList)
        val t0 = if (t == tOld) Number(0) else tOld
        val xs = StaticSemantics(ode)
          .bv
          .toSet
          .toList
          .filter({
            case _: BaseVariable => true
            case _ => false
          }: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, ode :: G.asList)
        val xys = (if (t == tOld) Nil else List((t, tOld))) ++ (if (s == sOld) Nil else List((s, sOld))) ++ xs.zip(ys)
        val sols = solve(t, xys, ode)
        val g = xys.foldLeft(G)({ case (acc, (x, y)) => acc.rename(x, y) })
        val con = ((t, s) :: sols).foldLeft[Formula](ode.constraint)({ case (acc, (x, f)) =>
          SubstitutionHelper.replaceFree(acc)(x, f)
        })
        val dcFml = Forall(List(s), Imply(And(LessEqual(t0, s), LessEqual(s, t)), con))
        val G1 = g.extend(GreaterEqual(t, t0)).extend(dcFml)
        val p = apply(G1, child)
        val sub = sols.foldLeft[Formula](post)({ case (acc, (x, f)) => SubstitutionHelper.replaceFree(acc)(x, f) })
        if (sub != p) {
          throw ProofException(s"['] with postcondition $post expected subgoal postcondition $sub, got $p", G1)
        }
        val free = StaticSemantics(post).fv
        val taboos = ys.toSet.+(tOld).+(sOld).+(s)
        if (!free.intersect(taboos).isEmpty) {
          throw ProofException(s"['] ghost variables must be fresh in postcondition $post", G1)
        }
        Box(ode, post)
      case DW(ode, child, ysOpt) =>
        val xs = StaticSemantics(ode)
          .bv
          .toSet
          .toList
          .filter({
            case _: BaseVariable => true
            case _ => false
          }: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, ode :: G.asList)
        val G1 = G.renames(xs, ys).extend(ode.constraint)
        val p1 = apply(G1, child)
        if (!StaticSemantics(p1).fv.intersect(ys.toSet).isEmpty) {
          throw ProofException(s"Ghost variable not fresh in postcondition $p1 in DW", G1)
        }
        Box(ode, p1)
      case DC(left, right) => apply(G, left) match {
          case Box(ODESystem(ode, con), p) => apply(G, right) match {
              case Box(ODESystem(ode1, And(con1, p1)), q) =>
                if (ode != ode1) { throw ProofException(s"DC expects ODEs $ode and $ode1 to match", G) }
                else if (con1 != con) { throw ProofException(s"DC expects constraint $con to match conjunct $con1", G) }
                else if (p1 != p) { throw ProofException(s"DC expects postconditions $p and $p1 to match", G) }
                Box(ODESystem(ode, con), q)
              case p => throw ProofException(s"DC does not apply to right premiss $p", G)
            }
          case p => throw ProofException(s"DC does not apply to left premiss $p", G)
        }

      case DI(ode1, pre, step, ysOpt) =>
        val p = apply(G, pre)
        val xs = StaticSemantics(ode1)
          .bv
          .toSet
          .toList
          .filter({
            case _: BaseVariable => true
            case _ => false
          }: (Variable => Boolean))
        val ys = ghostVars(ysOpt, xs, p :: ode1 :: G.asList)
        val G1 = G.renames(xs, ys).extend(ode1.constraint)
        apply(G1, step) match {
          case dp =>
            val map = DifferentialHelper
              .atomicOdes(ode1.ode)
              .map({ case AtomicODE(DifferentialSymbol(x), f) => (x, f) })
              .toMap
            val df = deriveFormula(p, map)
            if (dp != df) { throw ProofException(s"Subgoal in DI should be derivative $df, was $dp", G1) }
            if (!StaticSemantics(dp).fv.intersect(ys.toSet).isEmpty) {
              throw ProofException(s"Ghost variable not fresh in postcondition $dp in DI", G1)
            }
            Box(ode1, p)
        }
      // G, y=y0 |- M: [x'=f, y'=a(y)+b&Q]P
      case DG(Assign(y, y0), rhs @ Plus(Times(a, yy), b), child) =>
        if (y != yy) { throw ProofException(s"Variables $y and $yy should be equal in DG", G) }
        apply(G.extend(Equal(y, y0)), child) match {
          case Box(ODESystem(DifferentialProduct(AtomicODE(yp, ye), c), con), pp) =>
            if (yp != DifferentialSymbol(y)) {
              throw ProofException(s"Expected $yp and ${DifferentialSymbol(y)} equal in DG subgoal", G)
            } else if (ye != rhs) { throw ProofException(s"Expected $ye and $rhs equal in DG subgoal", G) }
            else if (ye != Plus(Times(a, yy), b)) {
              throw ProofException(s"Expected $ye and ${Plus(Times(a, yy), b)} equal in DG subgoal", G)
            } else if (
              StaticSemantics(pp)
                .fv
                .++(StaticSemantics(a).++(
                  StaticSemantics(b).++(StaticSemantics(con).fv.++(StaticSemantics(y0).++(G.freevars)))
                ))
                .toSet
                .intersect(Set(y, DifferentialSymbol(y)))
                .nonEmpty
            ) { throw ProofException(s"Variable $y needs to be fresh in DG", G) }
            else Box(ODESystem(c, con), pp)
        }
      case DG(e, _, _) => throw ProofException(s"Expected ghost term $e to have shape (f*y)+g in DG")
      case AndI(left, right) =>
        val p = apply(G, left)
        val q = apply(G, right)
        And(p, q)
      case AndEL(child) => apply(G, child) match {
          case And(p, _) => p
          case p => throw ProofException(s"Rule ^EL not applicable to subgoal $p", G)
        }
      case AndER(child) => apply(G, child) match {
          case And(_, q) => q
          case p => throw ProofException(s"Rule ^ER not applicable to subgoal $p", G)
        }
      case OrIL(other, child) =>
        val p = apply(G, child)
        Or(p, other)
      case OrIR(other, child) =>
        val q = apply(G, child)
        Or(other, q)
      case OrE(child, left, right) => apply(G, child) match {
          case Or(p, q) =>
            val r1 = apply(G.extend(p), left)
            val r2 = apply(G.extend(q), right)
            if (r1 != r2) throw ProofException(s"Postconditions $r1 and $r2 do not match in rule |E", G) else r1
          case p => throw ProofException(s"Rule |E not applicable to subgoal $p", G)
        }
      case ImplyI(fml, child) =>
        val q = apply(G.extend(fml), child)
        Imply(fml, q)
      case ImplyE(left, right) => apply(G, left) match {
          case Imply(p1, q) =>
            val p2 = apply(G, right)
            if (p1 != p2) throw ProofException(s"Assumption $p1 and $p2 mismatch in ->E", G) else q
          case p => throw ProofException(s"Rule ->E not applicable to formula $p", G)
        }
      case EquivI(Equiv(p, q), left, right) =>
        val q1 = apply(G.extend(p), left)
        val p1 = apply(G.extend(q), right)
        if (p1 != p) { throw ProofException(s"Left formula $p1 does not match $p in <->I", G) }
        else if (q1 != q) { throw ProofException(s"Right formula $q1 does not match $q in <->I", G) }
        else Equiv(p, q)
      case EquivEL(child, assump) => apply(G, child) match {
          case Equiv(p, q) =>
            val pp = apply(G, assump)
            if (p != pp) { throw ProofException(s"Assumption $pp does not match expected $p in <->EL", G) }
            else { q }
          case p => throw ProofException(s"Rule <->EL not applicable to subgoal $p", G)
        }
      case EquivER(child, assump) => apply(G, child) match {
          case Equiv(p, q) =>
            val qq = apply(G, assump)
            if (q != qq) { throw ProofException(s"Assumption $qq does not match expected $q in <->EL", G) }
            else { p }
          case p => throw ProofException(s"Rule <->ER not applicable to subgoal $p", G)
        }
      case NotI(p, child) => apply(G.extend(p), child) match {
          case False => Not(p)
          case p => throw ProofException(s"Rule !I not applicable to subgoal $p", G)
        }
      case NotE(left, right) => apply(G, left) match {
          case Not(p) =>
            val pp = apply(G, right)
            if (p != pp) { throw ProofException(s"Rule !E needed $p to contradict ${Not(p)}, got $pp", G) }
            False
          case p => throw ProofException(s"Rule !E not applicable to subgoal $p", G)
        }
      case FalseE(child, fml) => apply(G, child) match {
          case False => fml
          case p => throw ProofException(s"Rule falseE not applicable to subgoal $p", G)
        }
      case Hyp(p) => if (G.contains(p)) G(p) else throw ProofException(s"Proof variable $p undefined in rule hyp", G)
      case Mon(left, right, ysOpt) =>
        val p = apply(G, left)
        p match {
          case Box(a, p) =>
            val xs = StaticSemantics(a).bv.toSet.toList
            val ys = ghostVars(ysOpt, xs, p :: a :: G.asList)
            val G1 = G.renames(xs, ys).extend(p)
            val q = apply(G1, right)
            if (!StaticSemantics(q).fv.intersect(ys.toSet).isEmpty) {
              throw ProofException(s"Ghost variable not fresh in postcondition $q in monotonicity", G1)
            }
            Box(a, q)
          case Diamond(a, p) =>
            val xs = StaticSemantics(a).bv.toSet.toList
            val ys = ghostVars(ysOpt, xs, p :: a :: G.asList)
            val G1 = G.renames(xs, ys).extend(p)
            val q = apply(G1, right)
            if (!StaticSemantics(q).fv.intersect(ys.toSet).isEmpty) {
              throw ProofException(s"Ghost variable not fresh in postcondition $q in monotonicity", G1)
            }
            Diamond(a, q)
          case _ => throw ProofException(s"Montonicity not applicable to non-modal formula ${p}", G)
        }
      case QE(q, child) =>
        val p = apply(G, child)
        if (!Imply(p, q).isFOL) { throw ProofException(s"QE formula ${p}->${q} was not FOL", G) }
        if (qeValid(Imply(p, q))) { q }
        else { throw ProofException(s"QE formula ${Imply(p, q)} not valid", G) }
      case Compare(f: Term, g: Term, child: Proof) => apply(G, child) match {
          case Greater(k, n: Number) =>
            if (n.value != 0) { throw ProofException(s"Compare expects subgoal k > 0, got k > $n", G) }
            Or(Greater(f, g), Less(f, Plus(g, k)))
          case p => throw ProofException(s"Compare expects subgoal k > 0, got $p", G)
        }
    }
  }
}
