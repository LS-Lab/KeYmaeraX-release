package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.bellerophon.{StringInputTactic, _}
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.btactics.helpers._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.tools.{BigDecimalQETool, RingsLibrary, ToolEvidence}
import org.apache.logging.log4j.message.Message
import org.apache.logging.log4j.scala.Logging
import java.util.UUID

import cc.redberry.rings
import rings.poly.PolynomialMethods._
import rings.scaladsl._
import syntax._

import scala.collection.immutable._

object TaylorModelTactics extends Logging {

  // Timing
  object Timing {
    var time = System.nanoTime()
    def tic() = {
      time = System.nanoTime()
    }
    def toc(msg: String) = {
      val t = System.nanoTime()
      logger.info("TIMING " + msg + ": " + (t - time)/1000000000.0 + "s")
      tic()
    }
    def tocTac(message: => String): StringInputTactic =
      new StringInputTactic("tocTac", message::Nil) {
        override def result(provable: ProvableSig): ProvableSig = {
          toc(message)
          provable
        }
      }
  }
  import Timing._

  // Debugging
  private val pp = new KeYmaeraXPrettierPrinter(100)
  private def ppSubgoals(prv: ProvableSig) = {
    prv.subgoals.zipWithIndex.map{case (s, i) => "== Subgoal " + i + "==\n" + pp.stringify(s)}.mkString("\n")
  }
  def debug(msg: Unit => String) : Unit = {
    val message = new Message {
      override def getFormattedMessage(): String = msg()
      override def getParameters: Array[AnyRef] = ???
      override def getFormat(): String = ???
      override def getThrowable(): Throwable = ???
    }
    logger.debug(message)
  }
  def debug(name: String, e: Expression) : Unit = debug(_ => "=== " + name + "===\n" + pp.stringify(e))
  def debugTac(message: => String): StringInputTactic =
    new StringInputTactic("debugTac", message::Nil) {
      override def result(provable: ProvableSig): ProvableSig = {
        debug(_ => "===== " + message + " ====\n" + ppSubgoals(provable) + "\n===== " + message + " (end)\n")
        provable
      }
    }

  // Terms

  def constR(name: String) = FuncOf(Function(name, None, Unit, Real), Nothing)
  def minF(a: Term, b: Term) = FuncOf(BigDecimalQETool.minF, Pair(a, b))
  def maxF(a: Term, b: Term) = FuncOf(BigDecimalQETool.maxF, Pair(a, b))

  // Formulas

  def stripForall(fml: Formula) = fml match {
    case Forall(_, t) => this
    case _ => throw new IllegalArgumentException("stripForall not on Forall")
  }
  def stripForalls(fml: Formula) : Formula = fml match {
    case Forall(_, t) => stripForalls(t)
    case _ => fml
  }
  def rconjuncts(formula: Formula): List[Formula] = formula match {
    case And(p,q) => p :: rconjuncts(q)
    case f => List(f)
  }

  // Substitution

  def replaceFreeList(t: Term)(whats: List[Term], repls: List[Term]) =
    (whats, repls).zipped.foldLeft(t)((t, wr) => SubstitutionHelper.replaceFree(t)(wr._1, wr._2))

  def replaceFreeList(t: Formula)(whats: List[Term], repls: List[Term]) =
    (whats, repls).zipped.foldLeft(t)((t, wr) => SubstitutionHelper.replaceFree(t)(wr._1, wr._2))

  def replaceFreeList(t: Program)(whats: List[Term], repls: List[Term]) =
    (whats, repls).zipped.foldLeft(t)((t, wr) => SubstitutionHelper.replaceFree(t)(wr._1, wr._2))

  def replaceList(what: List[Term], witH: List[Term])(ts: List[Term]) = ts map (replaceFreeList(_)(what, witH))


  // Polynomials
  // TODO:
  //  - use own representation of multivariate polynomials or a
  //  - dedicated library
  //    libraryDependencies += "cc.redberry" %% "rings.scaladsl" % "2.5.2"
  //  - RingsAlgebraTool?

  /* A more efficient data structure for polynomial arithmetic */

  def normalise(p: Term) = {
    PolynomialArith.normalise(p, true)._1
  }

  def factors(t: Term): List[Term] = t match {
    case t: Times => factors(t.right) ++ factors(t.left)
    case x: Term => List(x)
  }

  def degree_gen(t: Term, isVar: Term=>Boolean) : BigDecimal = t match {
    case Power(l, Number(n)) if isVar(l) => n
    case t if PolynomialArith.isVar(t) => 1
    case _ => 0
  }
  def degree(t: Term) : BigDecimal = degree_gen(t,  PolynomialArith.isVar(_))

  def degree_wrt(w: Variable)(t: Term): BigDecimal = t match {
    case t: Power => t.left match {
      case v if v == w => t.right match {
        case n: Number => n.value
      }
      case _ => 0
    }
    case v if v == w => 1
    case _ => 0
  }

  /* of a monomial */
  def order_wrt(v: Variable)(t: Term): BigDecimal = t match {
    case t: Times => (factors(t) map degree_wrt(v)) sum
    case _ => 0
  }

  /* of a monomial */
  def order_gen(t: Term, isVar: Term=>Boolean): BigDecimal = t match {
    case t: Times =>
      val r = ((factors(t) map (v => degree_gen(v, isVar))) sum)
      r
    case _ => 0
  }

  // For normalized polynomials
  def integrate_monom(t: Variable)(p: Term): Term = {
    val n = order_wrt(t)(p)
    normalise(Divide(Times(p, t), Number(n + 1)))
  }

  def normaliseStripZero(p: Term) = {
    DifferentialHelper.stripPowZero(PolynomialArith.normalise(p, true)._1)
  }

  def sum_terms(ts: List[Term]) = if (ts isEmpty) Number(0) else ts.reduce(Plus(_, _))

  def summands(t: Term): List[Term] = t match {
    case t: Plus => summands(t.right) ++ summands(t.left)
    case x: Term => List(x)
  }

  def integrate(t: Variable)(p: Term): Term = sum_terms(summands(p) map (integrate_monom(t)))

  def split_poly(tm: Term, keepP: Term=>Boolean, ivl_terms: List[Term]): (Term, Term) = {
    val (throw_away, keep) = summands(tm).partition(t =>
      // contains ivl_terms
      ivl_terms.exists(ivlterm => PolynomialArith.divPoly(normalise(t),normalise(ivlterm)).isDefined)
        ||
        (!keepP(t))
    )
    (normalise(keep.reduceLeft(Plus)), if (throw_away.isEmpty) Number(0) else normalise(throw_away.reduceLeft(Plus)))
  }

  def divPoly(a: Term, b: Term): Option[(Term, Term)] =
  // TODO: this is too much normalisation
  {
    (PolynomialArith.divPoly(normalise(a), normalise(Neg(b))) /* TODO: for some reason, PolynomialArith.divPoly switches signs?? */) match {
      case Some(qr) =>
        divPoly(qr._2, b) match {
          case Some(qsrs) =>
            val (qs, rs) = qsrs
            Some (PolynomialArith.addPoly(normalise(qr._1),qs,true)._1,
              normalise(rs))
          case None => Some (normalise(qr._1), normalise(qr._2))
        }
      case None => None
    }
  }

  // rewrite t to Horner Form (w.r.t. "Variables" xs)
  def horner(t: Term, xs: List[Term]) : Term = xs match {
    case Nil => SimplifierV3.termSimp(t, SimplifierV3.emptyCtx, SimplifierV3.defaultTaxs)._1
    case x::xs => {
      divPoly(t, x) match {
        case None => horner(t, xs)
        case Some((q, r)) => {
          val hq = horner(q, x :: xs)
          val hr = horner(r, xs)
          val prod = if (hq == Number(0)) Number(0)
          else if (hq == Number(1)) x
          else if (hq == Number(-1)) Neg(x)
          else Times(x, hq)
          if (hr == Number(0)) prod
          else if (prod == Number(0)) hr
          else Plus(hr, prod)
        }
      }
    }
  }


  // Equality

  def rewriteAnte(hide: Boolean) = "rewriteAnte" by { (pos: Position, seq: Sequent) =>
    seq.ante.zipWithIndex.filter{ case (Equal(_, _), i) => true case _ => false }.foldLeft(skip){ case (t, (f, i)) =>
      eqL2R(- i - 1)(pos) & (if(hide) hideL(-i - 1) else skip) & t
    }
  }


  // DifferentialPrograms

  def getTime(ode: DifferentialProgram): Variable = {
    val aodes = DifferentialHelper.atomicOdes(ode)
    aodes find (_.e == Number(1)) match {
      case Some(aode) => aode.xp.x
      case None => throw new IllegalArgumentException("getTime: no time variable in ode")
    }
  }

  def applyODE(ode: DifferentialProgram, state: List[Term], time: Term)(ps: List[Term]) =
    DifferentialHelper.atomicOdes(ode).filter(_.xp.x != time).map(dx => replaceFreeList(dx.e)(state, ps))

  private def normalizingLieDerivative(p: DifferentialProgram, t: Term): Term = {
    val ld = normalise(DifferentialHelper.simplifiedLieDerivative(p, normaliseStripZero(t), None))
    ld
  }


  // Generic TaylormModel functions

  // names
  case class TMNames(precond_prefix: String,
                     right_prefix: String,
                     interval_prefix: String,
                     remainder_suffix: String,
                     timestepN: String) {
    def remainder(i: Int) : Variable = Variable("Rem" + i)
    def precond(i: Int, j: Int) : FuncOf = constR(precond_prefix + i + j)
    def precondC(i: Int) : FuncOf = constR(precond_prefix + "C" + i)
    def right(i: Int) : FuncOf = constR(right_prefix + i)
    def rightL(i: Int) : FuncOf = constR(right_prefix + "L" + i)
    def rightU(i: Int) : FuncOf = constR(right_prefix + "U" + i)
    def lower(i: Int) : FuncOf = constR(interval_prefix + "L" + i)
    def upper(i: Int) : FuncOf = constR(interval_prefix + "U" + i)
    def interval(i: Int) : FuncOf = constR(interval_prefix + i)
    val timestep = constR(timestepN)
    def right_vars(n: Int) : List[FuncOf] = ((0 until n) map right).toList

    def all_vars(n: Int) : List[Term] = {
      def make(f: Int => Term) = (0 until n) map f
      val preconds : List[Int => Term] = (0 until n).map(i => (j: Int) => precond(i, j)).toList
      // Scala does not like this?
      // (precondC::right::lower::upper::interval::preconds).flatMap(make)
      (make(precondC)::make(right)::make(lower)::make(upper)::make(interval)::make(remainder)::preconds.map(make)).flatten
    }
  }

  def templateTmCompose(names: TMNames, dim: Int): Seq[Term] = {
    (0 until dim).map(i => Plus((0 until dim).map(j => Times(names.precond(i, j), names.right(j))).reduceLeft(Plus), names.precondC(i)))
  }

  // Specialized Tactics
  private val namespace = "taylormodel"
  def remember(fml: Formula, tac: BelleExpr) = AnonymousLemmas.remember(fml, tac, namespace)
  private lazy val unfoldExistsLemma = remember("\\exists x (x = r() & P(x)) <-> P(r())".asFormula, prop & Idioms.<(
    existsL(-1) & andL(-1) & eqL2R(-1)(-2) & closeId,
    existsR("r()".asTerm)(1) & prop & QE & done))
  val unfoldExists = "unfoldExists" by { (pos: Position, seq: Sequent) =>
    Idioms.mapSubpositions(pos, seq, {
      case (Exists(vs, And(Equal(v, _), _)), pos) if vs.length == 1 && vs.head == v =>
        Some(useAt(unfoldExistsLemma, PosInExpr(0 :: Nil))(pos): BelleExpr)
      case _ => None
    }).reduceLeft(_ & _)
  }

  private lazy val foldAndLessEqExistsLemma = remember(("(a() <= x - b() & x - b() <= c()) <->" +
    "(\\exists xr_ (x = xr_ + b() & (a() <= xr_ & xr_ <= c())))").asFormula, QE & done)
  val foldAndLessEqExists = "foldAndLessEqExists" by { (pos: Position, seq: Sequent) =>
    Idioms.mapSubpositions(pos, seq, {
      case (And(LessEqual(_, Minus(v1: Variable, _)), LessEqual(Minus(v2: Variable, _), _)), pos) if v1 == v2 =>
        Some(useAt(foldAndLessEqExistsLemma, PosInExpr(0::Nil))(pos): BelleExpr)
      case _ =>
        None
    }).reduceLeft(_ & _)
  }

  lazy val leTimesMonoLemma =
    remember("0 <= t_() & t_() <= h_() -> R_() <= t_() * U_() -> R_() <= max((0,h_() * U_()))".asFormula, QE & done)
  lazy val timesLeMonoLemma =
    remember("0 <= t_() & t_() <= h_() -> t_() * L_() <= U_() -> min((0,h_() * L_())) <= U_()".asFormula, QE & done)
  private[btactics] def coarsenTimesBounds(t: Term) = "coarsenTimesBounds" by { (seq: Sequent) =>
    val leTimesMono = "leTimesMono" by { (pos: Position, seq: Sequent) =>
      pos.checkAnte
      seq.sub(pos) match {
        case Some(LessEqual(l, Times(t, g))) =>
          toc("cTB")
          seq.ante.find{ case (LessEqual(Number(n), s)) if n==0 && s==t => true case _ => false } match {
            case None => throw new IllegalArgumentException("could not find matching nonnegativity assumption")
            case Some(nonneg) => {
              toc(" found nonnegative ")
              seq.ante.find { case (LessEqual(s, _)) if s == t => true case _ => false } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml@(LessEqual(_, ub))) =>
                  {
                    toc(" found upper bound")
                    cutL(LessEqual(l, FuncOf(BigDecimalQETool.maxF, Pair(Number(0), Times(ub, g)))))(pos) &
                      Idioms.<(skip,
                        cohideOnlyR('Rlast) &
                          cutR(And(nonneg, ub_fml))(1) & Idioms.<(
                          andR(1) & Idioms.<(closeId, closeId),
                          cohideR(1) &
                            useAt(leTimesMonoLemma, PosInExpr(Nil))(1) & // TODO: in high-order (>=4), nonlinear ODE, a QE at this point is very slow (8s), but QE on the subgoal in a separate test is fast(<1s)
                            done
                        )
                      )
                  }
              }
            }
          }
        case _ => throw new IllegalArgumentException("leTimesMono not on _ <= _ * _")
      }
    }

    val timesLeMono = "timesLeMono" by { (pos: Position, seq: Sequent) =>
      pos.checkAnte
      seq.sub(pos) match {
        case Some(LessEqual(Times(t, g), u)) =>
          seq.ante.find{ case (LessEqual(Number(n), s)) if n==0 && s==t => true case _ => false } match {
            case None => throw new IllegalArgumentException("could not find matching nonnegativity assumption")
            case Some(nonneg) =>
              seq.ante.find{ case (LessEqual(s, _)) if s==t => true case _ => false } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml @ (LessEqual(_, ub))) =>
                  cutL(LessEqual(FuncOf(BigDecimalQETool.minF, Pair(Number(0), Times(ub, g))), u))(pos) &
                    Idioms.<( skip,
                      cohideOnlyR('Rlast) &
                        cutR(And(nonneg, ub_fml))(1) & Idioms.<(
                        andR(1) & Idioms.<(closeId, closeId),
                        cohideR(1) & useAt(timesLeMonoLemma, PosInExpr(Nil))(1) & done
                      )
                    )
              }
          }
        case _ => throw new IllegalArgumentException("leTimesMono not on _ <= _ * _")
      }
    }

    seq.zipAnteWithPositions.map{
      case (LessEqual(Times(s, _), _), pos) if s == t =>
        timesLeMono(pos)
      case (LessEqual(_, Times(s, _)), pos) if s == t =>
        leTimesMono(pos)
      case _ => skip
    }.reduceOption(_ & _).getOrElse(skip)
  }

  // only the cases that I need here...
  private lazy val minGtNorm = remember("min((f_(),g_()))>h_()<->(f_()>h_()&g_()>h_())".asFormula, QE& done)
  private lazy val minLeNorm = remember("min((f_(),g_()))<=h_()<->(f_()<=h_()|g_()<=h_())".asFormula, QE& done)
  private lazy val minGeNorm = remember("min((f_(),g_()))>=h_()<->(f_()>=h_()&g_()>=h_())".asFormula, QE& done)
  private lazy val leMaxNorm = remember("h_()<=max((f_(),g_()))<->(h_()<=f_()|h_()<=g_())".asFormula, QE& done)
  private [btactics] def unfoldMinMax = chaseCustom({
    case Greater(FuncOf(BigDecimalQETool.minF, _), _) => (minGtNorm.fact, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case GreaterEqual(FuncOf(BigDecimalQETool.minF, _), _) => (minGeNorm.fact, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case LessEqual(FuncOf(BigDecimalQETool.minF, _), _) => (minLeNorm.fact, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case LessEqual(_, FuncOf(BigDecimalQETool.maxF, _)) => (leMaxNorm.fact, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case _ => Nil
  })

  lazy val trivialInequality = remember("(x_() = 0 & y_() = 0) -> x_() <= y_()".asFormula, QE & done)
  def solveTrivialInequalities : DependentPositionTactic = "solveTrivialInequalities" by { (pos: Position, seq: Sequent) =>
    pos.checkTop
    pos.checkSucc
    val ssp = seq.sub(pos)
    seq.sub(pos) match {
      case Some(LessEqual(a, b)) =>
        useAt(trivialInequality, PosInExpr(1::Nil))(pos) & andR(pos) &
          Idioms.<(QE & done, QE & done) // TODO: this is purely algebraic, optimize for that?
      case Some(And(f, g)) =>
        andR(pos) & Idioms.<(solveTrivialInequalities(1), solveTrivialInequalities(1))
      case _ =>
        throw new IllegalArgumentException("solveTrivialInequalities cannot be applied here: " + ssp)
    }
  }

  lazy val refineConjunction = remember("((f_() -> h_()) & (g_() -> i_())) -> ((f_() & g_()) -> (h_() & i_()))".asFormula, prop & done)
  lazy val trivialRefineLtGt = remember("(w_() - v_() + y_() - x_() = 0) -> (v_() < w_() -> x_() > y_())".asFormula, QE & done)
  lazy val trivialRefineGeLe = remember("(v_() - w_() - y_() + x_() = 0) -> (v_() >= w_() -> x_() <= y_())".asFormula, QE & done)

  private [btactics] def refineTrivialInequalities : DependentPositionTactic = "refineTrivialStrictInequalities" by { (pos: Position, seq: Sequent) =>
    pos.checkTop
    pos.checkSucc
    val ssp = seq.sub(pos)
    seq.sub(pos) match {
      case Some(Imply(And(_, _), And(_, _))) =>
        useAt(refineConjunction, PosInExpr(1::Nil))(pos) & andR(pos) &
          Idioms.<(refineTrivialInequalities(1), refineTrivialInequalities(1))
      case Some(Imply(Less(_, _), Greater(_, _))) =>
        useAt(trivialRefineLtGt, PosInExpr(1::Nil))(pos) & Idioms.<(
          QE & done) // TODO: this is purely algebraic, optimize for that?
      case Some(Imply(GreaterEqual(_, _), LessEqual(_, _))) =>
        useAt(trivialRefineGeLe, PosInExpr(1::Nil))(pos) & Idioms.<(
          QE & done) // TODO: this is purely algebraic, optimize for that?
      case _ =>
        throw new IllegalArgumentException("solveTrivialInequalities cannot be applied here: " + ssp)
    }
  }
  /**
    * A class capturing all lemmas and tactics for Taylor models for the given ode
    * */
  case class TaylorModel(ode: DifferentialProgram, order: Int, names: TMNames = TMNames("a", "r", "i", "Rem", "h")) {
    private val time = getTime(ode)

    // State Variables of Expansion and Actual Evolution
    private val vars = DifferentialHelper.getPrimedVariables(ode)
    private val state = vars.filterNot(_ == time)
    private val dim = state.length
    private val timestep = names.timestep
    private val remainder = names.remainder(_)
    private val picRem = names.interval(_)
    private val tdL = names.lower(_)
    private val tdU = names.upper(_)
    private val remainders = (0 until dim).map(remainder(_)).toList

    // Establish connection to the rings-library
    private val ringsLib = new RingsLibrary(vars++names.all_vars(dim))
    private val ringsODE = ringsLib.ODE(time, state, names.right_vars(dim),
      DifferentialHelper.atomicOdes(ode).flatMap(aode => if (state.contains (aode.xp.x)) aode.e::Nil else Nil))

    private val initial_condition =
      And(Equal(time, Number(0)),
        (state, templateTmCompose(names, dim)).zipped.map { case (v, tm) => Equal(v, tm) }.reduceRight(And))

    private def lower_rembounds(t: Term)(td: Int => Term) : Seq[Formula] = (0 until dim).map(i =>
      LessEqual(minF(Number(0), Times(t, td(i))), remainder(i))
    )
    private def upper_rembounds(t: Term)(td: Int => Term) : Seq[Formula] = (0 until dim).map(i =>
      LessEqual(remainder(i), maxF(Number(0), Times(t, td(i))))
    )

    private def in_domain(ltu:(Term, Term, Term)) : Formula = ltu match {
      case (l: Term, t: Term, u: Term) => And(LessEqual(l, t), LessEqual(t, u))
    }

    private val right_tm_domain = (0 until dim).map(i => (names.rightL(i), names.right(i), names.rightU(i))).map(in_domain).reduceRight(And)

    tic()
    private val odeTac = DifferentialTactics.ODESpecific(ode)
    toc("odeTac")

    private val tm0 = templateTmCompose(names, dim)
    private val tm0R = tm0.map(ringsLib.toRing)
    private val picard_iterationR = ringsODE.PicardIteration(tm0R, order)
    private val picard_iteration = picard_iterationR.map(ringsLib.fromRing(_))
    toc("Picard Iteration")

    private val picard_remainder_vars = (0 until dim) map (picRem(_))
    private val picard_remainder_varsR = picard_remainder_vars.map(ringsLib.toRing(_))
    private val picard_remainder_varsI = picard_remainder_vars.map(v => ringsLib.ring.index(ringsLib.mapper(v.func)))

    private val picard_poly_rem = (picard_iterationR, picard_remainder_varsR).zipped.map(_ + _)

    private val (_, picard_iterate_remainder) = ringsODE.PicardOperation(tm0R, picard_poly_rem, order, picard_remainder_varsI)
    toc("Picard Iterate")

    private val right_vars = names.right_vars(dim)
    private val bounded_vars = right_vars ++ (0 until dim).map(remainder(_)) // variables for which we assume interval bounds somewhen

    /* this tries to keep even powers to exploit r:[-1,1]->r^2:[0,1] */
    private val horner_order = (0 until dim).flatMap(i => List(tdL(i), tdU(i))).toList ++ (time :: bounded_vars.map(Power(_, Number(2))) ++ bounded_vars)
    private val horner_orderR = horner_order.map(ringsLib.toRing)

    toc("horner_order")
    // TODO: use ringsLib here, as well
    // f (p + r)
    private val fpr = ringsODE.applyODE(picard_iterationR.zipWithIndex.map{case (p, i) => p + ringsLib.toRing(remainder(i))})
    // p'
    private val pp = picard_iteration.map(ringsLib.lieDerivative{
      case v: Variable if v == time => Some(ringsLib.ring(1))
      case _ => None
    })
    // Horner(f (p + r) - p')
    private val hornerFprPp = (fpr, pp).zipped.map{case (a, b) => ringsLib.toHorner(a - b, horner_orderR)}
    private val numbericCondition =
      FormulaTools.quantify(time :: remainders,
        Imply(
          And(And(LessEqual(Number(0), time), LessEqual(time, timestep)),
            (lower_rembounds(timestep)(tdL), upper_rembounds(timestep)(tdU)).zipped.map(And).reduceRight(And)),
          hornerFprPp.zipWithIndex.map{case (diff, i) => And(Less(tdL(i), diff), Less(diff, tdU(i)))}.reduceRight(And)
        ))
    toc("numbericCondition")


    private def tm_enclosure(x: Variable, i: Int, p: Term, l: Term, u: Term) = {
      val r = remainder(i)
      Exists(List(r), And(Equal(r, Minus(x, p)), And(LessEqual(l, r), LessEqual(r, u))))
    }
    private val post = (state, picard_iteration).zipped.toList.zipWithIndex.map { case ((x, p), i) =>
      tm_enclosure(x, i, p, Times(time, tdL(i)), Times(time, tdU(i)))
    }
    toc("post")

    private val boxTMEnclosure = Box(ODESystem(ode, And(LessEqual(Number(0), time), LessEqual(time, timestep))), post.reduceRight(And))
    private val instLeq = "ANON" by { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        case Some(Exists(vs, And(Equal(v: Variable, _), _))) if vs.length == 1 =>
          ProofRuleTactics.boundRenaming(vs.head, remainder(state.indexOf(v)))(pos) & existsL(pos)
        case _ => throw new IllegalArgumentException("instLeq not on expected shape.")
      }
    }

    val lemma : ProvableSig = proveBy(
        Imply(
          And(And(initial_condition, right_tm_domain), numbericCondition),
          boxTMEnclosure),
        debugTac("start") &
          implyR(1) &
          unfoldExists(1) &
          tocTac("pre dIClosed") &
          odeTac.dIClosed(1) &
          Idioms.<(
            // Initial Condition
            tocTac("dIClosed") &
            debugTac("Initial Condition") &
              andL(-1) & cohideOnlyL(-1) &
              SaturateTactic(andL('L)) &
              rewriteAnte(true)(1) &
              cohideR(1) &
              debugTac("initial QEs") &
              solveTrivialInequalities(1) &
              tocTac("Initial Condition done") &
              done,
            // Differential Invariant
            tocTac("Differential Invariant") &
            foldAndLessEqExists(1) &
              tocTac("foldAndLessEqExists") &
              implyR(1) &
              SaturateTactic(andL('L) | instLeq('L)) &
              tocTac("Saturate instLeq") &
              rewriteAnte(true)(1) &
              tocTac("rewriteAnte") &
              unfoldMinMax(1) &
              tocTac("unfoldMinMax") &
              coarsenTimesBounds(time) &
              tocTac("coarsenTimesBounds") &
              FOQuantifierTactics.allLs(time :: remainders)('L) &
              implyL('L) &
              Idioms.<(
                cohideOnlyR(2) & prop & done,
                  cohideOnlyL(Find(0, Some("P_() & Q_()".asFormula), AntePosition(1), false)) &
                  implyRi()(AntePosition(1), SuccPosition(1)) &
                  debugTac("refine it!") &
                  tocTac("to refine") &
                  refineTrivialInequalities(1) &
                  tocTac("refined it")
              )
          )
      )

    private def getBoundees(fml: Formula): List[Term] = fml match {
      case And(And(Less(_, t1), Less(t2, _)), ivls) if t1 == t2 =>
        t1::getBoundees(ivls)
      case And(Less(_, t1), Less(t2, _)) if t1 == t2 =>
        t1::Nil
      case _ => throw new IllegalArgumentException("getBoundees called on non-And")
    }

    private def numericPicard(prec: Integer, boundees: IndexedSeq[Term], timebound: Term, right_bounds: List[Formula])
                     (ivls: IndexedSeq[(BigDecimal, BigDecimal)]) : IndexedSeq[(BigDecimal, BigDecimal)] =
    {
      val lowers = lower_rembounds(timebound){i => Number(ivls(i)._1)}
      val uppers = upper_rembounds(timebound){i => Number(ivls(i)._2)}
      // TODO: compute bounds except lowers/uppers earlier?!
      val bounds = IntervalArithmeticV2.collect_bounds(prec, LessEqual(Number(0), time) :: LessEqual(time, timebound) :: right_bounds ++ lowers ++ uppers)
      boundees.map(IntervalArithmeticV2.eval_ivl(prec)(bounds))
    }

    def numericPicardIteration(prec: Integer, boundees: IndexedSeq[Term], timebound: Term, right_bounds: List[Formula],
                               remainder_estimation: IndexedSeq[(BigDecimal, BigDecimal)])
    :
    Option[IndexedSeq[(BigDecimal, BigDecimal)]] =
    {
      var remainders = remainder_estimation
      var cremainders = None : Option[IndexedSeq[(BigDecimal, BigDecimal)]]
      var subset = false
      for (k <- 0 until 40) {
        val remainders0 = remainders
        val remainders1 = numericPicard(prec, boundees, timebound, right_bounds)(remainders0)
        subset = (remainders0, remainders1).zipped.forall{ case ((l0, u0), (l, u)) => l0 < l && u < u0 }
        val remainders2 = if (!subset) {
          // epsilon inflation -- values for eps and algorithm from Ingo Eble: "Ueber Taylor Modelle", PhD thesis 2007
          val eps1 = 1e-2
          val eps2 = 1e-6
          remainders1 map {case (l, u) => (l + eps1*(l - u) - eps2, u + eps1*(u - l) + eps2) }
        } else {
          cremainders = Some(remainders1)
          remainders1
        }
        remainders = remainders2
        debug(_=>"State of numerical remainders of Picard Iteration: ")
        debug(_=>"subset = " + subset.toString)
        debug(_=>"remainders0: " + remainders0.toString)
        debug(_=>"remainders1: " + remainders1.toString)
        debug(_=>"remainders2: " + remainders2.toString)
      }
      cremainders
    }

    def cutTM(prec: Integer, antepos: AntePosition,
              qeTool: QETool,
              remainder_estimation : IndexedSeq[(BigDecimal, BigDecimal)] = (0 until dim).map(_ => (BigDecimal(-0.001),BigDecimal(0.001))))
    : DependentPositionTactic = "cutTM" by { (pos: Position, seq: Sequent) =>
      pos.checkSucc
      pos.checkTop
      seq.sub(pos) match {
        case Some(Box(ODESystem(ode1, And(LessEqual(time0, time1), LessEqual(time2, timebound))), goal))
          // TODO: more flexible domain, lookup ode?
          if ode1 == ode && time0 == Number(0) && time1 == time && time2 == time =>
        {
          require(seq.sub(antepos).isDefined)
          val concrete_initial_condition = seq.sub(antepos).get
          val subst = USubst(SubstitutionPair(names.timestep, timebound)::Nil)++UnificationMatch(And(initial_condition, right_tm_domain), concrete_initial_condition).usubst
          val lemma1 = lemma(subst)
          require(lemma1.conclusion.succ.length == 1)
          val (boundees, concrete_right_bound) = lemma1.conclusion.succ(0) match {
            case Imply(And(And(_, crb), fml : Forall), _) => stripForalls(fml) match {
              case Imply(bound_fml, conclusion) => (getBoundees(conclusion), FormulaTools.conjuncts(crb))
              case _ => throw new RuntimeException("Taylor model lemma not of expected shape (inner)")
            }
            case _ => throw new RuntimeException("Taylor model lemma not of expected shape")
          }
          val subst_remainders = numericPicardIteration(prec, boundees.toIndexedSeq, timebound, concrete_right_bound, remainder_estimation) match {
            case None => throw new RuntimeException("Picard Iteration did not converge")
            case Some(remainders) =>
              USubst(remainders.zipWithIndex.map{case ((l, _), i) => SubstitutionPair(names.lower(i), IntervalArithmeticV2.mathematicaFriendly(l))} ++
                remainders.zipWithIndex.map{case ((_, u), i) => SubstitutionPair(names.upper(i), IntervalArithmeticV2.mathematicaFriendly(u))})
          }
          val lemma2 = lemma1(subst_remainders)
          require(lemma2.conclusion.succ.length == 1)
          val cut_fml = lemma2.conclusion.succ(0) match {
            case Imply(_, Box(_, cut_fml)) => cut_fml
            case _ => throw new RuntimeException("Instantiated Taylor model lemma not of expected shape")
          }
          debugTac("Starting to do something") &
            DC(cut_fml)(pos) &
              Idioms.<(skip,
                useAt(lemma2, PosInExpr(1::Nil))(1) &
                  andR(1) & Idioms.<(closeId,
                      SaturateTactic(allR(1)) &
                      SaturateTactic(implyR(1)) &
                      SaturateTactic(andL('L)) &
                      debugTac("Numberic condition") &
                      IntervalArithmeticV2.intervalArithmeticBool(prec, qeTool) &
                      done
                )
              )
        }
        case _ => throw new IllegalArgumentException("cutTM not on suitable Box(ODE)")
      }
    }
  }

}