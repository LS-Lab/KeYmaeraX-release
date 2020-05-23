package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.bellerophon.{StringInputTactic, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.btactics.helpers._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.apache.logging.log4j.message.Message
import org.apache.logging.log4j.scala.Logging
import java.util.UUID

import cc.redberry.rings
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.tools.ext.{QETacticTool, RingsLibrary}
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import rings.poly.PolynomialMethods._
import rings.scaladsl._
import syntax._

import scala.collection.immutable._
import DerivationInfoAugmentors._

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

  def stripForalls(fml: Formula) : Formula = fml match {
    case Forall(_, t) => stripForalls(t)
    case _ => fml
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

  // TODO: sort in somewhere
  private lazy val partialVacuousExistsAxiom2 = remember(
    "\\exists x_ (p_() & q_(x_)) <-> p_() & \\exists x_ q_(x_)".asFormula,
    equivR(1) <(
      existsL(-1) & andR(1) <(prop & done, existsR("x_".asVariable)(1) & prop & done),
      andL('L) & existsL(-2) & existsR("x_".asVariable)(1) & prop & done
    )
  )

  private def rewriteFormula(prv: ProvableSig) = "rewriteFormula" by { (pos: Position, seq: Sequent) =>
    val failFast = new BuiltInTactic("ANON") with NoOpTactic {
      override def result(provable: ProvableSig): ProvableSig = throw new TacticInapplicableFailure("Fail")
    }
    prv.conclusion.succ.toList match {
      case Equiv(lhs, rhs) :: Nil =>
        seq.sub(pos) match {
          case Some(fml: Formula) =>
            val poss = FormulaTools.posOf(fml, a => a match {
              case (subfml: Formula) => {
                val um = UnificationMatch.unifiable(lhs, subfml)
                um.isDefined
              }
              case _ => false
            })
            poss.foldRight(fail){ case (subpos, a) => useAt(prv, PosInExpr(0 :: Nil))(pos ++ subpos) | a }
          case _ => throw new IllegalArgumentException("rewriteFormula not on Formula.")
        }
      case _ => throw new IllegalArgumentException("rewriteFormula expects an Equiv as single conclusion of provable but got:\\n" + prv)
    }
  }

  // Generic Taylor Model functions

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

  private def templateTmCompose(names: TMNames, dim: Int): Seq[Term] = {
    (0 until dim).map(i => Plus((0 until dim).map(j => Times(names.precond(i, j), names.right(j))).reduceLeft(Plus), names.precondC(i)))
  }

  // Specialized Tactics
  private val namespace = "taylormodel"
  private def remember(fml: Formula, tac: BelleExpr) = AnonymousLemmas.remember(fml, tac, namespace)
  private lazy val unfoldExistsLemma = remember("\\exists x_ (r_() = s_() + x_ & P_(x_)) <-> P_(r_()-s_())".asFormula, prop & Idioms.<(
    existsL(-1) & andL(-1) & cutR("r_() - s_() = x_".asFormula)(1) & Idioms.<(QE & done, implyR(1) & eqL2R(-3)(1) & closeId),
    existsR("r_() - s_()".asTerm)(1) & prop & QE & done))

  private lazy val foldAndLessEqExistsLemma = remember(("(a() <= x_ - b() & x_ - b() <= c()) <->" +
    "(\\exists xr_ (x_ = xr_ + b() & (a() <= xr_ & xr_ <= c())))").asFormula, QE & done)
  private def foldAndLessEqExists(but: Seq[Variable] = Nil) = "foldAndLessEqExists" by { (pos: Position, seq: Sequent) =>
    Idioms.mapSubpositions(pos, seq, {
      case (And(LessEqual(_, Minus(v1: Variable, _)), LessEqual(Minus(v2: Variable, _), _)), pos)
        if v1 == v2 && !but.contains(v1)
      =>
        Some(useAt(foldAndLessEqExistsLemma, PosInExpr(0::Nil))(pos): BelleExpr)
      case _ =>
        None
    }).reduceLeft(_ & _)
  }

  private lazy val leTimesMonoLemma =
    remember("0 <= t_() & t_() <= h_() -> R_() <= t_() * U_() -> R_() <= max((0,h_() * U_()))".asFormula, QE & done)
  private lazy val timesLeMonoLemma =
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
              seq.ante.collectFirst{ case fml @ LessEqual(s, _) if s == t => fml } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml @ LessEqual(_, ub)) =>
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
              seq.ante.collectFirst{ case fml @ LessEqual(s, _) if s==t => fml } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml @ LessEqual(_, ub)) =>
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

  private lazy val trivialInequality = remember("(x_() = 0 & y_() = 0) -> x_() <= y_()".asFormula, QE & done)
  private def solveTrivialInequalities : DependentPositionTactic = "solveTrivialInequalities" by { (pos: Position, seq: Sequent) =>
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

  private lazy val refineConjunction = remember("((f_() -> h_()) & (g_() -> i_())) -> ((f_() & g_()) -> (h_() & i_()))".asFormula, prop & done)
  private lazy val trivialRefineLtGt = remember("(w_() - v_() + y_() - x_() = 0) -> (v_() < w_() -> x_() > y_())".asFormula, QE & done)
  private lazy val trivialRefineGeLe = remember("(v_() - w_() - y_() + x_() = 0) -> (v_() >= w_() -> x_() <= y_())".asFormula, QE & done)

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
    private val time0 = "t0()".asTerm // TODO: parameterize!
    private val localTime = "s".asVariable // TODO: parameterize!

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
    private val ringsLib = new RingsLibrary(time0::localTime::vars++names.all_vars(dim))// TODO: time0, localTime?!
    private val ringsODE = ringsLib.ODE(localTime, state, names.right_vars(dim),
      DifferentialHelper.atomicOdes(ode).flatMap(aode => if (state.contains (aode.xp.x)) aode.e::Nil else Nil))

    private val initial_condition =
      And(Equal(time, time0),
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
    private val horner_order = (0 until dim).flatMap(i => List(tdL(i), tdU(i))).toList ++ (localTime :: bounded_vars.map(Power(_, Number(2))) ++ bounded_vars)
    private val horner_orderR = horner_order.map(ringsLib.toRing)

    toc("horner_order")
    // TODO: use ringsLib here, as well
    // f (p + r)
    private val fpr = ringsODE.applyODE(picard_iterationR.zipWithIndex.map{case (p, i) => p + ringsLib.toRing(remainder(i))})
    // p'
    private val pp = picard_iteration.map(ringsLib.lieDerivative{
      case v: Variable if v == localTime => Some(ringsLib.ring(1))
      case _ => None
    })
    // Horner(f (p + r) - p')
    private val hornerFprPp = (fpr, pp).zipped.map{case (a, b) => ringsLib.toHorner(a - b, horner_orderR)}
    private val numbericCondition =
      FormulaTools.quantifyForall(localTime :: remainders,
        Imply(
          And(And(LessEqual(Number(0), localTime), LessEqual(localTime, timestep)),
            (lower_rembounds(timestep)(tdL), upper_rembounds(timestep)(tdU)).zipped.map(And).reduceRight(And)),
          hornerFprPp.zipWithIndex.map{case (diff, i) => And(Less(tdL(i), diff), Less(diff, tdU(i)))}.reduceRight(And)
        ))
    toc("numbericCondition")


    private def tmEnclosureEx(x: Variable, i: Int, p: Term, l: Term, u: Term) = {
      val r = remainder(i)
      Exists(List(r), And(Equal(r, Minus(x, p)), And(LessEqual(l, r), LessEqual(r, u))))
    }

    private def tmEnclosure(x: Variable, i: Int, p: Term, l: Term, u: Term) = {
      val r = remainder(i)
      And(Equal(x, Plus(p, r)), And(LessEqual(l, r), LessEqual(r, u)))
    }
    // Taylor Model postcondition without existentials and instantiated with t for time.
    private val post = {
      (state, picard_iteration).zipped.toList.zipWithIndex.map { case ((x, p), i) =>
        tmEnclosure(x, i, p, Times(localTime, tdL(i)), Times(localTime, tdU(i)))
      }
    }
    toc("post")

    private val boxTMEnclosure = Box(ODESystem(ode, And(LessEqual(time0, time), LessEqual(time, Plus(time0, timestep)))),
      FormulaTools.quantifyExists(localTime :: remainders,
        (Equal(time, Plus(time0, localTime)):: post).reduceRight(And))
    )
    private val instLeq = "ANON" by { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        case Some(Exists(vs, And(Equal(v: Variable, _), _))) if vs.length == 1 =>
          ProofRuleTactics.boundRenaming(vs.head, remainder(state.indexOf(v)))(pos) & existsL(pos)
        case _ => throw new IllegalArgumentException("instLeq not on expected shape.")
      }
    }

    private val domain_rewrite = proveBy(Equiv(And(LessEqual(time0, time), LessEqual(time, Plus(time0, timestep))),
      And(LessEqual(Number(0), Minus(time, time0)), LessEqual(Minus(time, time0), timestep))), QE & done)

    val lemma: ProvableSig = proveBy(
      Imply(
        And(And(initial_condition, right_tm_domain), numbericCondition),
        boxTMEnclosure),
      debugTac("start") &
        implyR(1) &
        // push in existencial quantifiers
        SaturateTactic(rewriteFormula(partialVacuousExistsAxiom2.fact)(1) |
          rewriteFormula(Ax.pexistsV.provable)(1) |
          rewriteFormula(TaylorModelTactics.unfoldExistsLemma.fact)(1)
        ) &
        tocTac("pre dIClosed") &
        useAt(domain_rewrite, PosInExpr(0::Nil))(1, 0::1::Nil) &
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
            foldAndLessEqExists(time::Nil)(1) &
            tocTac("foldAndLessEqExists") &
            implyR(1) &
            SaturateTactic(andL('L) | instLeq('L)) &
            tocTac("Saturate instLeq") &
            rewriteAnte(true)(1) &
            tocTac("rewriteAnte") &
            unfoldMinMax(1) &
            tocTac("unfoldMinMax") &
            debugTac("unfoldMinMax") &
            coarsenTimesBounds(Minus(time, time0)) &
            tocTac("coarsenTimesBounds") &
            FOQuantifierTactics.allLs(Minus(time, time0):: remainders)('L) &
            implyL('L) &
            Idioms.<(
              cohideOnlyR(2) & prop & done,
              cohideOnlyL(Find(0, Some("P_() & Q_()".asFormula), AntePosition(1), false)) &
                implyRi()(AntePosition(1), SuccPosition(1)) &
                debugTac("refine it!") &
                tocTac("to refine") &
                refineTrivialInequalities(1) &
                tocTac("refined it") &
                done
            )
        )
    )

    val timestepLemma = {
      proveBy(
        Imply(
          And(And(And(And(
            // t=0, x = A*r + A_c
            initial_condition,
            // r : [rL, rU]
            right_tm_domain),
            // condition for valid TM conclusion
            numbericCondition),
            // \forall t x Rem ( x = TM(x,t,Rem) -> P(t, x))
            FormulaTools.quantifyForall(localTime :: state ++ remainders,
              Imply(
                And(And(LessEqual(Number(0), localTime), LessEqual(localTime, timestep)),
                  SubstitutionHelper.replaceFree(post.reduceRight(And))(time, localTime))
                ,
                SubstitutionHelper.replaceFree(odeTac.P_pat)(time, Plus(time, localTime)))
            )),
            // \forall x Rem ( x = TM(x,h,Rem) -> [x'=f(x)]P(t+h,x) )
            FormulaTools.quantifyForall(state++remainders,
              Imply(
                SubstitutionHelper.replaceFree(post.reduceRight(And))(time, timestep),
                Box(ODESystem(ode, True), SubstitutionHelper.replaceFree(odeTac.P(vars))(time, timestep))
              )
            )
          ),
          Box(ODESystem(ode, True), odeTac.P_pat)
        ),
        skip
      )
    }

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
      val bounds = IntervalArithmeticV2.collect_bounds(prec, LessEqual(Number(0), localTime) :: LessEqual(localTime, timebound) :: right_bounds ++ lowers ++ uppers)
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
              qeTool: QETacticTool,
              remainder_estimation : IndexedSeq[(BigDecimal, BigDecimal)] = (0 until dim).map(_ => (BigDecimal(-0.001),BigDecimal(0.001))))
    : DependentPositionTactic = "cutTM" by { (pos: Position, seq: Sequent) =>
      pos.checkSucc
      pos.checkTop
      seq.sub(pos) match {
        case Some(Box(ODESystem(ode1, And(LessEqual(t0, time1), LessEqual(time2, Plus(t00, timebound)))), goal))
          // TODO: more flexible domain, lookup ode?
          if ode1 == ode && time1 == time && time2 == time && t0 == t00 =>
        {
          require(seq.sub(antepos).isDefined)
          val concrete_initial_condition = seq.sub(antepos).get
          val subst = USubst(SubstitutionPair(time0, t0)::SubstitutionPair(names.timestep, timebound)::Nil)++UnificationMatch(And(initial_condition, right_tm_domain), concrete_initial_condition).usubst
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