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
import edu.cmu.cs.ls.keymaerax.tools.{BigDecimalQETool, ToolEvidence}
import org.apache.logging.log4j.message.Message
import org.apache.logging.log4j.scala.Logging
import java.util.UUID

import scala.collection.immutable._

object TaylorModelTactics extends Logging {

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
    def remainder(x: Variable) : Variable = Variable(x.name + "Rem")
    def precond(i: Int, j: Int) : FuncOf = constR(precond_prefix + i + j)
    def precondC(i: Int) : FuncOf = constR(precond_prefix + "C" + i)
    def right(i: Int) : FuncOf = constR(right_prefix + i)
    def lower(i: Int) : FuncOf = constR(interval_prefix + "L" + i)
    def upper(i: Int) : FuncOf = constR(interval_prefix + "U" + i)
    def interval(i: Int) : FuncOf = constR(interval_prefix + i)
    val timestep = constR(timestepN)
    def right_vars(n: Int) : List[FuncOf] = ((0 until n) map right).toList
  }

  def templateTmCompose(names: TMNames, dim: Int): List[Term] = {
    (0 until dim).map(i => Plus((0 until dim).map(j => Times(names.precond(i, j), names.right(j))).reduceLeft(Plus), names.precondC(i))).toList
  }

  // Specialized Tactics

  private lazy val unfoldExistsLemma = proveBy("\\exists x (x = r() & P(x)) <-> P(r())".asFormula, prop & Idioms.<(
    existsL(-1) & andL(-1) & eqL2R(-1)(-2) & closeId,
    existsR("r()".asTerm)(1) & prop & QE & done))
  val unfoldExists = "unfoldExists" by { (pos: Position, seq: Sequent) =>
    Idioms.mapSubpositions(pos, seq, {
      case (Exists(vs, And(Equal(v, _), _)), pos) if vs.length == 1 && vs.head == v =>
        Some(useAt(unfoldExistsLemma, PosInExpr(0 :: Nil))(pos): BelleExpr)
      case _ => None
    }).reduceLeft(_ & _)
  }

  private lazy val foldAndLessEqExistsLemma = proveBy(("(a() <= x - b() & x - b() <= c()) <->" +
    "(\\exists xr_ (x = xr_ + b() & (a() <= xr_ & xr_ <= c())))").asFormula, QE & done)
  val foldAndLessEqExists = "foldAndLessEqExists" by { (pos: Position, seq: Sequent) =>
    Idioms.mapSubpositions(pos, seq, {
      case (And(LessEqual(_, Minus(v1: Variable, _)), LessEqual(Minus(v2: Variable, _), _)), pos) if v1 == v2 =>
        Some(useAt(foldAndLessEqExistsLemma, PosInExpr(0::Nil))(pos): BelleExpr)
      case _ =>
        None
    }).reduceLeft(_ & _)
  }

  private[btactics] def coarsenTimesBounds(t: Term) = "coarsenTimesBounds" by { (seq: Sequent) =>
    val leTimesMono = "leTimesMono" by { (pos: Position, seq: Sequent) =>
      pos.checkAnte
      seq.sub(pos) match {
        case Some(LessEqual(l, Times(t, g))) =>
          seq.ante.find{ case (LessEqual(Number(n), s)) if n==0 && s==t => true case _ => false } match {
            case None => throw new IllegalArgumentException("could not find matching nonnegativity assumption")
            case Some(nonneg) =>
              seq.ante.find{ case (LessEqual(s, _)) if s==t => true case _ => false } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml @ (LessEqual(_, ub))) =>
                  cutL(LessEqual(l, FuncOf(BigDecimalQETool.maxF, Pair(Number(0), Times(ub, g)))))(pos) &
                    Idioms.<( skip,
                      cohideOnlyR('Rlast) &
                        cutR(And(nonneg, ub_fml))(1) & Idioms.<(
                        andR(1) & Idioms.<(closeId, closeId),
                        cohideR(1) & QE & done
                      )
                    )
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
                        cohideR(1) & QE & done
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
  private lazy val minGtNorm:ProvableSig = proveBy("min((f_(),g_()))>h_()<->(f_()>h_()&g_()>h_())".asFormula, QE& done)
  private lazy val minLeNorm:ProvableSig = proveBy("min((f_(),g_()))<=h_()<->(f_()<=h_()|g_()<=h_())".asFormula, QE& done)
  private lazy val leMaxNorm:ProvableSig = proveBy("h_()<=max((f_(),g_()))<->(h_()<=f_()|h_()<=g_())".asFormula, QE& done)
  private def unfoldMinMax = chaseCustom({
    case Greater(FuncOf(BigDecimalQETool.minF, _), _) => (minGtNorm, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case LessEqual(FuncOf(BigDecimalQETool.minF, _), _) => (minLeNorm, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case LessEqual(_, FuncOf(BigDecimalQETool.maxF, _)) => (leMaxNorm, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case _ => Nil
  })


  /**
    * A class capturing all lemmas and tactics for Taylor models for the given ode
    * */
  case class TaylorModel(ode: DifferentialProgram, order: Int, names: TMNames = TMNames("a", "r", "i", "Rem", "h")) {
    val time = getTime(ode)

    // State Variables of Expansion and Actual Evolution
    val vars = DifferentialHelper.getPrimedVariables(ode)
    val state = vars.filterNot(_ == time)

    /** apply the picard operator for initial value x0 on ps(polynomials in const0) */
    def PicardOperation(x0: List[Term], const0: List[Term], ps: List[Term], order: Int, consts_to_remainder: List[Term] = Nil) = {
      val stateify = replaceList (const0, state) (_)
      val constify = replaceList (state, const0) (_)

      def is_tm_var(t: Term) = t == time || const0.contains(t)

      // f(p)
      val f = applyODE(ode, state, time)(ps).map(normalise)

      // integral(f(picard_poly + r))
      val int_f = f map integrate(time)

      // x0 + integral(f(picard_poly + r))
      val tool = ToolProvider.simplifierTool()
      val pairs = ((x0, int_f).zipped.map(Plus).map(normalise)).map(split_poly(_, order_gen(_, is_tm_var) <= order, consts_to_remainder))
      val res = ((pairs.map(p => DifferentialHelper.simpWithTool(None, p._1))), (pairs.map(p => DifferentialHelper.simpWithTool(None, p._2))))
      logger.debug("PicardOperation:\n" + res)
      res
    }

    /** perform picard iteration for initial value tm0 (a polynomial in const0) up to order */
    def PicardIteration(tm0: List[Term], const0: List[Term], order: Int) = {
      var ptm = tm0
      for (i <- 0 until order) {
        ptm = PicardOperation(tm0, const0, ptm, order)._1
      }
      ptm
    }

    private def normaliseAt: DependentPositionTactic = "normaliseAt" by { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        case Some(t: Term) =>
          useAt(PolynomialArith.normalise(t, false)._2, PosInExpr(0::Nil))(pos)
        case Some(LessEqual(FuncOf(BigDecimalQETool.minF, _), _)) =>
          unfoldMinMax(pos) & normaliseAt(pos)
        case Some(LessEqual(_, FuncOf(BigDecimalQETool.maxF, _))) =>
          unfoldMinMax(pos) & normaliseAt(pos)
        case Some(fml: ComparisonFormula) =>
          SimplifierV3.ineqNormalize(fml) match {
            case (nrml, Some(prv)) =>
              useAt(prv, PosInExpr(0::Nil))(pos) &
                normaliseAt(pos ++ PosInExpr(0::Nil))
            case _ => normaliseAt(pos ++ PosInExpr(0::Nil)) // TODO: is this correct here? assuming that this case only occurs if ineqNormalize did not make progress
          }
        case Some(b: BinaryCompositeFormula) => normaliseAt(pos ++ PosInExpr(0::Nil)) & normaliseAt(pos ++ PosInExpr(1::Nil))
        case _ => TactixLibrary.fail
      }
    }

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

    val dim = state.length

    val initial_condition = And(Equal(time, Number(0)),
      state.zipWithIndex.map { case (v, i) => Equal(v,
        Plus(
          (0 until dim).map(j => Times(names.precond(i, j), names.right(j))).reduceLeft(Plus),
          names.precondC(i)))
      }.reduceRight(And))

    val timestep = names.timestep
    val remainder = names.remainder(_)
    val picRem = names.interval(_)
    val tdL = names.lower(_)
    val tdU = names.upper(_)

    def lower_rembounds(t: Term)(td: Int => Term) : List[Formula] = state.zipWithIndex.map{case (v, i) =>
      LessEqual(minF(Number(0), Times(t, td(i))), remainder(v))
    }
    def upper_rembounds(t: Term)(td: Int => Term) : List[Formula] = state.zipWithIndex.map{case (v, i) =>
      LessEqual(remainder(v), maxF(Number(0), Times(t, td(i))))
    }

    def in_domain(t: Term) = And(LessEqual(Number(-1), t), LessEqual(t, Number(1)))

    val right_tm_domain = names.right_vars(dim).map(in_domain).reduceRight(And)

    val lemma : ProvableSig = {
      val vars = DifferentialHelper.getPrimedVariables(ode)
      val state = vars.filterNot(_ == time)

      val tm0 = templateTmCompose(names, dim)
      val picard_iteration = PicardIteration(tm0, names.right_vars(dim), order)

      val picard_remainder_vars: List[Term] = (0 until dim) map (picRem(_)) toList

      val picard_poly_rem = (picard_iteration, picard_remainder_vars).zipped.map(
        (poly, rem) => normaliseStripZero(Plus(poly, rem))) // TODO: here another option might be to just subtract picard_poly_state from the overall result

      val (_, picard_iterate_remainder) = PicardOperation(tm0, names.right_vars(2), picard_poly_rem, order, picard_remainder_vars)
      val (picard_iterate_rem_exact, picard_iterate_rem_ivl) =
        picard_iterate_remainder.map(pir => split_poly(pir, (_ => true), picard_remainder_vars)).unzip

      val odeTac = new DifferentialTactics.ODESpecific(ode)

      def tm_enclosure(x: Variable, p: Term, l: Term, u: Term) = {
        val r = remainder(x)
        Exists(List(r), And(Equal(r, Minus(x, p)), And(LessEqual(l, r), LessEqual(r, u))))
      }

      val post = (state, picard_iteration).zipped.toList.zipWithIndex.map { case ((x, p), i) =>
        tm_enclosure(x, p, Times(time, tdL(i)), Times(time, tdU(i)))
      }

      val box = Box(ODESystem(ode, And(LessEqual(Number(0), time), LessEqual(time, timestep))), post.reduceRight(And))

      val instLeq = "ANON" by { (pos: Position, seq: Sequent) =>
        seq.sub(pos) match {
          case Some(Exists(vs, And(Equal(v: Variable, _), _))) if vs.length == 1 =>
            ProofRuleTactics.boundRenaming(vs.head, remainder(v))(pos) & existsL(pos)
          case _ => TactixLibrary.fail
        }
      }
      val right_vars = names.right_vars(dim)
      val bounded_vars = right_vars ++ state.map(remainder(_)) // variables for which we assume interval bounds somewhen

      /* this tries to keep even powers to exploit r:[-1,1]->r^2:[0,1] */
      val horner_order = (0 until dim).flatMap(i => List(tdL(i), tdU(i))).toList ++ (time :: bounded_vars.map(Power(_, Number(2))) ++ bounded_vars)

      val numberic_condition =
        FormulaTools.quantify(time :: state.map(remainder(_)),
          Imply(
            And(And(LessEqual(Number(0), time), LessEqual(time, timestep)),
              (lower_rembounds(timestep)(tdL), upper_rembounds(timestep)(tdU)).zipped.map(And).reduceRight(And)),
            (applyODE(ode, state, time)((picard_iteration, state).zipped.map((p, x) => (Plus(p, remainder(x))))), picard_iteration).zipped.toList.zipWithIndex.map {
              case ((fp, p), i) =>
                val dp = normalizingLieDerivative(AtomicODE(DifferentialSymbol(time), Number(1)), p)
                val diff = horner(normalise(Minus(fp, dp)), horner_order)
                And(Less(tdL(i), diff), Less(diff, tdU(i)))
            }.reduceRight(And)
          ))
      debug("numberic_condition", numberic_condition)
      val prv = proveBy(
        Imply(
          And(And(initial_condition, right_tm_domain),
            numberic_condition),
          box),
        debugTac("start") &
          implyR(1) &
          unfoldExists(1) &
          odeTac.dIClosed(1) &
          Idioms.<(
            // Initial Condition
            SimplifierV3.fullSimpTac() &
              SaturateTactic(andL('L)) & rewriteAnte(true)(1) &
              debugTac("initial QE") &
              QE(),
            // Differential Invariant
            foldAndLessEqExists(1) & implyR(1) & SaturateTactic(andL('L) | instLeq('L)) & rewriteAnte(true)(1) &
              unfoldMinMax(1) &
              coarsenTimesBounds(time) &
              FOQuantifierTactics.allLs(time :: state.map(remainder(_)))(-1) &
              debugTac("fullSimpTac") &
              SimplifierV3.fullSimpTac() & // gets rid of preconditions of numberic_condition
              debugTac("fullSimpTac done") &
              normaliseAt(-1) &
              debugTac("normalised Ante") &
              normaliseAt(1) &
              debugTac("normalised Succ") &
              closeId &
              debugTac("closed")
          )
      )
      prv
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