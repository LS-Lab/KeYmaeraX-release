package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.bellerophon.{StringInputTactic, _}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.btactics.helpers._
import edu.cmu.cs.ls.keymaerax.parser.{InterpretedSymbols, KeYmaeraXPrettierPrinter}
import cc.redberry.rings
import edu.cmu.cs.ls.keymaerax.btactics.Ax.boxTrueAxiom
import edu.cmu.cs.ls.keymaerax.{Logging, core}
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.tools.ext.{QETacticTool, RingsLibrary}
import rings.scaladsl._
import syntax._

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._

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
  def debug(msg: Unit => String) : Unit = logger.debug(msg())
  def debug(name: String, e: Expression) : Unit = debug(_ => "=== " + name + "===\n" + pp.stringify(e))
  def debugTac(message: => String): StringInputTactic =
    new StringInputTactic("debugTac", message::Nil) {
      override def result(provable: ProvableSig): ProvableSig = {
        debug(_ => "===== " + message + " ====\n" + ppSubgoals(provable) + "\n===== " + message + " (end)\n")
        provable
      }
    }

  // Tactics

  val andLstable = new BuiltInLeftTactic("andLstable") {
    override def computeResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
      ProofRuleTactics.requireOneSubgoal(provable, name)
      val subgoal = provable.subgoals(0)
      /** [[pos.checkTop]] like in [[andL]] */
      val antepos = pos.checkTop
      /** matching on [[And]] like in [[AndLeft]] */
      val fml@And(p, q) = subgoal(pos.checkTop)
      val Llast = subgoal.ante.length
      provable(core.Cut(fml), 0).
        apply(Close(antepos, SuccPos(subgoal.succ.length)), 1).
        apply(AndLeft(AntePos(Llast)), 0).
        apply(ExchangeLeftRule(antepos, AntePos(Llast)), 0).
        apply(HideLeft(AntePos(Llast)), 0)
    }
  }
  val existsLstable = new BuiltInLeftTactic("existsLstable") {
    override def computeResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
      ProofRuleTactics.requireOneSubgoal(provable, name)
      val subgoal = provable.subgoals(0)
      /** [[pos.checkTop]] like in [[andL]] */
      val antepos = pos.checkTop
      /** matching on [[Exists]] like in [[AndLeft]] */
      val fml@Exists(_, _) = subgoal(pos.checkTop)
      val Llast = subgoal.ante.length
      proveBy(provable(core.Cut(fml), 0).
        apply(Close(antepos, SuccPos(subgoal.succ.length)), 1),
        existsL(AntePos(Llast))
      ).apply(ExchangeLeftRule(antepos, AntePos(Llast)), 0).
        apply(HideLeft(AntePos(Llast)), 0)
    }
  }

  // Terms

  def constR(name: String) = FuncOf(Function(name, None, Unit, Real), Nothing)
  def minF(a: Term, b: Term) = FuncOf(InterpretedSymbols.minF, Pair(a, b))
  def maxF(a: Term, b: Term) = FuncOf(InterpretedSymbols.maxF, Pair(a, b))

  // Formulas

  def stripForalls(fml: Formula) : Formula = fml match {
    case Forall(_, t) => stripForalls(t)
    case _ => fml
  }

  // Equality

  def rewriteAnte(hide: Boolean) = anon { (pos: Position, seq: Sequent) =>
    seq.ante.zipWithIndex.filter{ case (Equal(_, _), i) => true case _ => false }.foldLeft[BelleExpr](skip){ case (t, (f, i)) =>
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

  private def rewriteFormula(prv: ProvableSig) = anon { (pos: Position, seq: Sequent) =>
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
            poss.foldRight[BelleExpr](fail){ case (subpos, a) => useAt(prv, PosInExpr(0 :: Nil))(pos ++ subpos) | a }
          case _ => throw new TacticInapplicableFailure("rewriteFormula not on Formula.")
        }
      case _ => throw new InputFormatFailure("rewriteFormula expects an Equiv as single conclusion of provable but got:\\n" + prv)
    }
  }

  // Generic Taylor Model functions

  // names
  case class TMNames(precond_prefix: String,
                     right_prefix: String,
                     interval_prefix: String,
                     remainder_suffix: String,
                     timestepN: String,
                     postCoeff_prefix: String
                    ) {
    def remainder(i: Int) : Variable = Variable("Rem" + i)
    def precond(i: Int, j: Int) : FuncOf = constR(precond_prefix + i + j)
    def precondC(i: Int) : FuncOf = constR(precond_prefix + "C" + i)
    def right(i: Int) : FuncOf = constR(right_prefix + i)
    def rightL(i: Int) : FuncOf = constR(right_prefix + "L" + i)
    def rightU(i: Int) : FuncOf = constR(right_prefix + "U" + i)
    def lower(i: Int) : FuncOf = constR(interval_prefix + "L" + i)
    def upper(i: Int) : FuncOf = constR(interval_prefix + "U" + i)
    def lowerC(i: Int) : FuncOf = constR(interval_prefix + "cL" + i)
    def upperC(i: Int) : FuncOf = constR(interval_prefix + "cU" + i)
    def postCoeff(i: Int, exponents: List[Int]) : FuncOf =
      constR(postCoeff_prefix + i + "e" + exponents.map(e => if (e < 9) e.toString else "X" + e).mkString)
    def interval(i: Int) : FuncOf = constR(interval_prefix + i)
    val timestep = constR(timestepN)
    def right_vars(n: Int) : List[FuncOf] = ((0 until n) map right).toList

    def monomials(len: Int, order: Int) : List[List[Int]] = {
      def monomialsAcc(len: Int, xs: List[Int], n: Int, acc: List[List[Int]]): List[List[Int]] = {
        if (len == 0) xs :: acc
        else (0 to n).foldLeft(acc) { case (a, i) => monomialsAcc(len - 1, i :: xs, n - i, a) }
      }
      monomialsAcc(len, Nil, order, Nil)
    }
    def postCoeffs(i: Int, n: Int, order: Int) : List[FuncOf] = monomials(n, order).map(mon => postCoeff(i, mon))

    def all_vars(n: Int, order: Int) : List[Term] = {
      def make(f: Int => Term) = (0 until n) map f
      val preconds: List[Int => Term] = (0 until n).map(i => (j: Int) => precond(i, j)).toList
      val allPostCoeffs: List[FuncOf] = (0 until n).map(i => postCoeffs(i, n+1 /* time */, order)).flatten.toList
      // Scala does not like this?
      // (precondC::right::lower::upper::interval::preconds).flatMap(make)
      (make(precondC)::make(right)::make(lower)::make(upper)::make(lowerC)::make(upperC)::make(interval)::make(remainder)::preconds.map(make)).flatten ++
        allPostCoeffs
    }
  }

  private def templateTmCompose(names: TMNames, dim: Int): Seq[Term] = {
    (0 until dim).map(i => Plus((0 until dim).map(j => Times(names.precond(i, j), names.right(j))).reduceLeft(Plus), names.precondC(i)))
  }

  // Specialized Tactics
  private def foldAndLessEqExists(but: Seq[Variable] = Nil) = anon { (pos: Position, seq: Sequent) =>
    Idioms.mapSubpositions(pos, seq, {
      case (And(LessEqual(_, Minus(v1: Variable, _)), LessEqual(Minus(v2: Variable, _), _)), pos)
        if v1 == v2 && !but.contains(v1)
      =>
        Some(useAt(Ax.foldAndLessEqExistsLemma, PosInExpr(0::Nil))(pos): BelleExpr)
      case _ =>
        None
    }).reduceLeft(_ & _)
  }

  private[btactics] def coarsenTimesBounds(t: Term) = anon { (seq: Sequent) =>
    val leTimesMono = anon { (pos: Position, seq: Sequent) =>
      pos.checkAnte
      seq.sub(pos) match {
        case Some(LessEqual(l, Plus(Times(t, g), c))) =>
          toc("cTB")
          seq.ante.find{ case (LessEqual(Number(n), s)) if n==0 && s==t => true case _ => false } match {
            case None => throw new IllegalArgumentException("could not find matching nonnegativity assumption")
            case Some(nonneg) => {
              toc(" found nonnegative ")
              seq.ante.collectFirst{ case fml @ LessEqual(s, _) if s == t => fml } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml@LessEqual(_, ub)) =>
                  toc(" found upper bound")
                  cutL(LessEqual(l, Plus(FuncOf(InterpretedSymbols.maxF, Pair(Number(0), Times(ub, g))), c)))(pos) &
                    Idioms.<(skip,
                      cohideOnlyR('Rlast) &
                        cutR(And(nonneg, ub_fml))(1) & Idioms.<(
                        andR(1) & Idioms.<(id, id),
                        cohideR(1) &
                          useAt(Ax.leTimesMonoLemma, PosInExpr(Nil))(1) & // TODO: in high-order (>=4), nonlinear ODE, a QE at this point is very slow (8s), but QE on the subgoal in a separate test is fast(<1s)
                          done
                      )
                    )
              }
            }
          }
        case _ => throw new IllegalArgumentException("leTimesMono not on _ <= _ * _")
      }
    }

    val timesLeMono = anon { (pos: Position, seq: Sequent) =>
      pos.checkAnte
      seq.sub(pos) match {
        case Some(LessEqual(Plus(Times(t, g), c), u)) =>
          seq.ante.find{ case (LessEqual(Number(n), s)) if n==0 && s==t => true case _ => false } match {
            case None => throw new IllegalArgumentException("could not find matching nonnegativity assumption")
            case Some(nonneg) =>
              seq.ante.collectFirst{ case fml @ LessEqual(s, _) if s==t => fml } match {
                case None => throw new IllegalArgumentException("could not find matching upper bound assumption")
                case Some(ub_fml @ LessEqual(_, ub)) =>
                  cutL(LessEqual(Plus(FuncOf(InterpretedSymbols.minF, Pair(Number(0), Times(ub, g))), c), u))(pos) &
                    Idioms.<( skip,
                      cohideOnlyR('Rlast) &
                        cutR(And(nonneg, ub_fml))(1) & Idioms.<(
                        andR(1) & Idioms.<(id, id),
                        cohideR(1) & useAt(Ax.timesLeMonoLemma, PosInExpr(Nil))(1) & done
                      )
                    )
              }
          }
        case _ => throw new IllegalArgumentException("leTimesMono not on _ <= _ * _")
      }
    }

    seq.zipAnteWithPositions.map{
      case (LessEqual(Plus(Times(s, _), _), _), pos) if s == t =>
        timesLeMono(pos)
      case (LessEqual(_, Plus(Times(s, _), _)), pos) if s == t =>
        leTimesMono(pos)
      case _ => skip
    }.reduceOption[BelleExpr](_ & _).getOrElse(skip)
  }

  // only the cases that I need here...
  private [btactics] def unfoldMinMax = chaseCustom({
    case Greater(FuncOf(InterpretedSymbols.minF, _), _) => (Ax.minGtNorm.provable, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case GreaterEqual(FuncOf(InterpretedSymbols.minF, _), _) => (Ax.minGeNorm.provable, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case LessEqual(FuncOf(InterpretedSymbols.minF, _), _) => (Ax.minLeNorm.provable, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case LessEqual(_, FuncOf(InterpretedSymbols.maxF, _)) => (Ax.leMaxNorm.provable, PosInExpr(0::Nil), List(PosInExpr(0::Nil), PosInExpr(1::Nil)))::Nil
    case _ => Nil
  })

  private def solveTrivialInequalities : DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    pos.checkTop
    pos.checkSucc
    val ssp = seq.sub(pos)
    seq.sub(pos) match {
      case Some(LessEqual(a, b)) =>
        useAt(Ax.trivialInequality, PosInExpr(1::Nil))(pos) & andR(pos) &
          Idioms.<(QE & done, QE & done) // TODO: this is purely algebraic, optimize for that?
      case Some(And(f, g)) =>
        andR(pos) & Idioms.<(solveTrivialInequalities(1), solveTrivialInequalities(1))
      case _ =>
        throw new IllegalArgumentException("solveTrivialInequalities cannot be applied here: " + ssp)
    }
  }

  // was "refineTrivialStrictInequalities"
  private [btactics] def refineTrivialInequalities : DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    pos.checkTop
    pos.checkSucc
    val ssp = seq.sub(pos)
    seq.sub(pos) match {
      case Some(Imply(And(_, _), And(_, _))) =>
        useAt(Ax.refineConjunction, PosInExpr(1::Nil))(pos) & andR(pos) &
          Idioms.<(refineTrivialInequalities(1), refineTrivialInequalities(1))
      case Some(Imply(Less(_, _), Greater(_, _))) =>
        useAt(Ax.trivialRefineLtGt, PosInExpr(1::Nil))(pos) & Idioms.<(
          QE & done) // TODO: this is purely algebraic, optimize for that?
      case Some(Imply(GreaterEqual(_, _), LessEqual(_, _))) =>
        useAt(Ax.trivialRefineGeLe, PosInExpr(1::Nil))(pos) & Idioms.<(
          QE & done) // TODO: this is purely algebraic, optimize for that?
      case _ =>
        throw new IllegalArgumentException("solveTrivialInequalities cannot be applied here: " + ssp)
    }
  }
  /**
    * A class capturing all lemmas and tactics for Taylor models for the given ode
    * */
  case class TaylorModel(ode: DifferentialProgram, order: Int, names: TMNames = TMNames("a", "r", "i", "Rem", "h", "tm")) {
    protected val time = getTime(ode)
    private val time0 = "t0()".asTerm // TODO: parameterize!
    private val localTime = "s".asVariable // TODO: parameterize!

    // State Variables of Expansion and Actual Evolution
    protected val vars = DifferentialHelper.getPrimedVariables(ode)
    protected val state = vars.filterNot(_ == time)
    protected val dim = state.length
    private val timestep = names.timestep
    private val remainder = names.remainder(_)
    private val tdL = names.lower(_)
    private val tdU = names.upper(_)
    private val cL = names.lowerC(_)
    private val cU = names.upperC(_)
    private val remainders = (0 until dim).map(remainder(_)).toList
    private val right_vars = names.right_vars(dim)
    private val bounded_vars = right_vars ++ (0 until dim).map(remainder(_)) // variables for which we assume interval bounds somewhen


    // Establish connection to the rings-library
    private val ringsLib = new RingsLibrary(time0::localTime::vars++names.all_vars(dim, order))
    private val ringsODE = ringsLib.ODE(localTime, state, names.right_vars(dim),
      DifferentialHelper.atomicOdes(ode).flatMap(aode => if (state.contains (aode.xp.x)) aode.e::Nil else Nil))

    val initial_condition =
      And(Equal(time, time0),
        (state, templateTmCompose(names, dim)).zipped.map { case (v, tm) => Equal(v, tm) }.reduceRight(And))

    private def lower_rembounds(t: Term)(td: Int => Term)(c: Int => Term) : Seq[Formula] = (0 until dim).map(i =>
      LessEqual(Plus(minF(Number(0), Times(t, td(i))), c(i)), remainder(i))
    )
    private def upper_rembounds(t: Term)(td: Int => Term)(c: Int => Term)  : Seq[Formula] = (0 until dim).map(i =>
      LessEqual(remainder(i), Plus(maxF(Number(0), Times(t, td(i))), c(i)))
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

    /** the exact coefficients of the polynomial resulting from Picard iteration */
    private val exactCoefficients: List[Map[List[Int], Term]] = picard_iterationR.map(p => ringsLib.distributive(p, localTime::right_vars)).toList
    /** Just a template polynomial whose coefficients are supposed to be close to [[picard_iterationR]]
      * only uses those coefficients that are actually used
      * */
    def tmMonomial(coeff: Term, exponents: List[Int]) = {
      val monomial = (localTime::right_vars, exponents).zipped.toList.
        filter{case (_, e) => e > 0}.
        map{ case (v, e) => if (e == 1) v else Power(v, Number(e))}
      if (monomial.isEmpty) coeff else Times(coeff, monomial.reduceLeft(Times))
    }

    private val picard_iteration_approx =
      exactCoefficients.zipWithIndex.map { case (c, i) => c.keys.toList.sortBy(_.sum).
        map(k => tmMonomial(names.postCoeff(i, k), k)).reduceLeft(Plus) }
    private val picard_iteration_approxR = picard_iteration_approx.map(ringsLib.toRing(_))

    toc("Picard Iteration")

    toc("Picard Iterate")

    /* this tries to keep even powers to exploit r:[-1,1]->r^2:[0,1] */
    private val horner_order = (0 until dim).flatMap(i => List(tdL(i), tdU(i))).toList ++ (localTime :: bounded_vars.map(Power(_, Number(2))) ++ bounded_vars)
    private val horner_orderR = horner_order.map(ringsLib.toRing)
    toc("horner_order")

    // numeric condition for initial approximation:
    private val initialNumbericCondition = (0 until dim).map{ i =>
      /** time-constant coefficients, i.e., at initial time. this is the same as [[initial_condition]],
        * but perhaps a bit more convenient to use here, because we directly get the exponents. */
      val constantCoeffs = exactCoefficients(i).filterKeys(e => e(0) == 0)
      val diff = ringsLib.toHorner(
        ringsLib.toRing(
          Minus(
            constantCoeffs.map { case (e, c) => tmMonomial(c, e) }.reduceLeft(Plus),
            constantCoeffs.keys.map { e => tmMonomial(names.postCoeff(i, e), e) }.reduceLeft(Plus)
          )),
        horner_orderR
      )
      And(LessEqual(cL(i), diff), LessEqual(diff, cU(i)))
    }.reduceRight(And)

    // f (p + r)
    private val fpr = ringsODE.applyODE(picard_iteration_approxR.zipWithIndex.map{case (p, i) => p + ringsLib.toRing(remainder(i))})
    // p'
    private val pp = picard_iteration_approx.map(ringsLib.lieDerivative{
      case v: Variable if v == localTime => Some(ringsLib.ring(1))
      case _ => None
    })
    // Horner(f (p + r) - p')
    private val hornerFprPp = (fpr, pp).zipped.map{case (a, b) => ringsLib.toHorner(a - b, horner_orderR)}
    private [btactics] val innerNumbericCondition =
      hornerFprPp.zipWithIndex.map { case (diff, i) => And(Less(tdL(i), diff), Less(diff, tdU(i))) }.reduceRight(And)
    val numbericCondition =
      And(
        initialNumbericCondition,
        FormulaTools.quantifyForall(localTime :: remainders,
          Imply(
            And(And(LessEqual(Number(0), localTime), LessEqual(localTime, timestep)),
              (lower_rembounds(timestep)(tdL)(cL), upper_rembounds(timestep)(tdU)(cU)).zipped.map(And).reduceRight(And)),
            innerNumbericCondition
          ))
      )
    toc("numbericCondition")


    private def tmEnclosureEx(x: Variable, i: Int, p: Term, l: Term, u: Term) = {
      val r = remainder(i)
      Exists(List(r), And(Equal(r, Minus(x, p)), And(LessEqual(l, r), LessEqual(r, u))))
    }

    private def tmEnclosure(x: Variable, i: Int, p: Term, l: Term, u: Term) = {
      val r = remainder(i)
      Exists(Seq(r), And(Equal(x, Plus(p, r)), And(LessEqual(l, r), LessEqual(r, u))))
    }
    private val post = {
      (state, picard_iteration_approx).zipped.toList.zipWithIndex.map { case ((x, p), i) =>
        tmEnclosure(x, i, p, postIvlL(i), postIvlU(i))
      }
    }

    private def postIvlL(i: Int) = {
      Plus(Times(localTime, tdL(i)), cL(i))
    }

    private def postIvlU(i: Int) = {
      Plus(Times(localTime, tdU(i)), cU(i))
    }

    toc("post")
    private val postUnfolded = SubstitutionHelper.replaceFree(
      (And(LessEqual(Number(0), localTime), LessEqual(localTime, timestep))::(state, picard_iteration_approx).zipped.toList.zipWithIndex.map { case ((x, p), i) =>
        val r = Minus(x, p)
        And(LessEqual(postIvlL(i), r), LessEqual(r, postIvlU(i)))
      }).reduceRight(And))(localTime, Minus(time, time0))
    toc("postUnfolded")

    private def boxODETimeStep(post: Formula) =
      Box(ODESystem(ode, And(LessEqual(time0, time), LessEqual(time, Plus(time0, timestep)))), post)

    val boxTMEnclosure = boxODETimeStep(
      (Exists(Seq(localTime),
        (And(Equal(time, Plus(time0, localTime)),
          And(LessEqual(Number(0), localTime), LessEqual(localTime, timestep)))
          :: post).reduceRight(And)))
    )

    val postEq = proveBy(Equiv(boxTMEnclosure.child, postUnfolded),
      equivR(1) &
        Idioms.<(
          existsLstable(-1) & andLstable(-1) & andLstable(-1) &
            useAt(Ax.eqAddIff, PosInExpr(0 :: Nil))(-1) & eqL2R(-1)(-2) & eqL2R(-1)(-3) &
            andR(1) & Idioms.<(close(-3, 1), skip) & hideL(-3) & hideL(-1) &
          andLstable('Llast) * (dim-1) &
          (1 to dim).map { i =>
            val p = -i
            val l = -(dim + i)
            existsLstable(p) & andLstable(p) &
              useAt(Ax.eqAddIff, PosInExpr(0 :: Nil))(p) & eqL2R(p)(l)
            : BelleExpr}.reduceLeft(_ & _) &
            hideL(-1) * dim &
            (andR(1) & Idioms.<(id, skip))*(dim - 1) & id,
          existsR(Minus(time, time0))(1) &
            andLstable(-1) &
            andR(1) & Idioms.<(andR(1) & Idioms.<(
                cohideR(1) & byUS(Ax.plusDiffRefl),
                id
              ), hideL(-1)) &
            andLstable('Llast) * (dim - 1) &
            (andR(1) & Idioms.<(
              useAt(Ax.unfoldExistsLemma)(1) & id, skip)) * (dim - 1) &
            useAt(Ax.unfoldExistsLemma)(1) & id
        )
    )

    private val instLeq = anon { (pos: Position, seq: Sequent) =>
      seq.sub(pos) match {
        case Some(Exists(vs, And(Equal(v: Variable, _), _))) if vs.length == 1 =>
          ProofRuleTactics.boundRename(vs.head, remainder(state.indexOf(v)))(pos) & existsL(pos)
        case _ => throw new TacticInapplicableFailure("instLeq not on expected shape.")
      }
    }

    private val domain_rewrite = proveBy(Equiv(And(LessEqual(time0, time), LessEqual(time, Plus(time0, timestep))),
      And(LessEqual(Number(0), Minus(time, time0)), LessEqual(Minus(time, time0), timestep))), QE & done)

    val numericAssumption =
      And(And(
      // t=0, x = A*r + A_c
      initial_condition,
      // r : [rL, rU]
      right_tm_domain),
      // condition for valid TM conclusion
      numbericCondition)

    val lemma: ProvableSig = proveBy(
      Imply(
        numericAssumption,
        boxTMEnclosure),
      debugTac("start") &
        implyR(1) &
        debugTac("pre push") &
        useAt(postEq, PosInExpr(0::Nil))(1, 1::Nil) &
        debugTac("post push") &
        tocTac("pre dIClosed") &
        useAt(domain_rewrite, PosInExpr(0::Nil))(1, 0::1::Nil) &
        debugTac("pre dIClosed") &
        boxAnd(1) & andR(1) & Idioms.<(cohideR(1) & byUS(Ax.DWbase), skip) &
        odeTac.dIClosed(1) &
        Idioms.<(
          // Initial Condition
          tocTac("dIClosed") &
            debugTac("Initial Condition") &
            andL(-1) &
            // obtain initial numberic condition
            andL(-2) &
            hideL(-3) &
            debugTac("obtained initial numberic condition") &
            ringsLib.normalizeLessEquals(QE)(-2) &
            SaturateTactic(andL('L)) &
            rewriteAnte(true)(1) &
            ringsLib.normalizeLessEquals(QE)(1) &
            debugTac("Initial Condition numeric trivialities") &
            prop &
            tocTac("Initial Condition done?") &
            debugTac("Initial Condition done?") &
            done,
          // Differential Invariant
          tocTac("Differential Invariant") &
            debugTac("Differential Invariant") &
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
            debugTac("coarsenTimesBounds") &
            FOQuantifierTactics.allLs(Minus(time, time0):: remainders)('L) &
            implyL('L) &
            Idioms.<(
              cohideOnlyR(2) & prop & done,
              cohideOnlyL(Find.FindLMatch("P_() & Q_()".asFormula)) &
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
          And(And(And(
            numericAssumption
            ,
            // nonnegative time step
            LessEqual(Number(0), timestep)),
            // \forall t x ( x = TM(x,t) -> P(t, x))
            FormulaTools.quantifyForall(localTime :: state,
              Imply(
                And(And(LessEqual(Number(0), localTime), LessEqual(localTime, timestep)),
                  post.reduceRight(And))
                ,
                SubstitutionHelper.replaceFree(odeTac.P_pat)(time, Plus(time, localTime)))
            )),
            // \forall t x Rem ( (t=t0+h() & x = TM(x,h,Rem)) -> [x'=f(x)]P(t,x) )
            FormulaTools.quantifyForall(time::state,
              Imply(
                And(Equal(time, Plus(time0, timestep)), SubstitutionHelper.replaceFree(post.reduceRight(And))(localTime, timestep)),
                Box(ODESystem(ode, True), odeTac.P(vars))
              )
            )
          ),
          Box(ODESystem(ode, True), odeTac.P_pat)
        ),
        implyR(1) &
        // Cut and prove lower bound for time
        dC(LessEqual(time0, time))(1) & Idioms.<(useAt(Ax.trueAnd)(1, 0::1::Nil), dI('diffInd)(1) &
          Idioms.<(
            useAt(Ax.lessEqual, PosInExpr(0::Nil))(1) & orR(1) & hideR(1) & useAt(Ax.equalSym, PosInExpr(1::0::Nil))(1) & prop & done,
            chase(1) & ToolTactics.hideNonFOL & QE & done)) &
        // apply time step axiom (and shuffle around ODEs)
          useAt(Ax.commaCommute)(1) * vars.indexOf(time) &
            useAt(Ax.timeStep, PosInExpr(1 :: Nil),
            (substo: Option[TactixLibrary.Subst]) =>
              substo.getOrElse(RenUSubst(Nil))++ RenUSubst((timestep, Plus(time0, timestep)) :: Nil))(1) &
          useAt(Ax.commaCommute)(1, 1::Nil) * (vars.length - vars.indexOf(time)) &
          useAt(Ax.commaCommute)(1, 1::1::1::1::Nil) * (vars.length - vars.indexOf(time)) &
          andR(1) &
          Idioms.<(
            // time step is nonnegative
            (andL(-1) & hideL(-2))*2 & andL(-1) & (andL(-1) & hideL(-3)) & SaturateTactic(andL(-2) & hideL(-3)) & QE & done,
            boxAnd(1) & andR(1) &
              Idioms.<(
                // safety throughout first step
                andL(-1) & hideL(-2) & andL(-1) & andL(-1) & hideL(-3) & cutR(boxTMEnclosure)(1) /* TODO: does a dC here yield better structure and less overhead? */ &
                Idioms.<(
                  useAt(lemma, PosInExpr(1::Nil))(1) & id,
                  andL(-2) & hideL(-3) &
                    SaturateTactic(andL(-2) & hideL(-3)) /* extract t=t0() */ &
                    eqL2R(-2)(-1) & hideL(-2) &
                    implyR(1) & dC(boxTMEnclosure.child)(1) &
                  Idioms.<(
                    // make implication via dW
                    hideL(-2) & dWPlus(1) & andL(-2) &
                      // obtain existential witnesses
                      existsL(-3) /* local time */ &
                      // instantiate them
                      allL(localTime)(-1) &
                        FOQuantifierTactics.allLs(state)(-1) &
                      andLstable(-3) & andLstable(-3) & eqL2R(-3)(1) & implyL(-1) &
                      Idioms.<(
                        hideR(1) & andR(1) &
                        Idioms.<(
                          hideL(-3) & QE & done,
                          id
                        ),
                        id),
                    id
                  )
                ),
                // safety for next step
                andL(-1) & andL(-1) & hideL(-3) & andL(-2) & hideL(-3) &
                  dC(boxTMEnclosure.child)(1) &
                  Idioms.<(
                    hideL(-2) &
                    dWPlus(1) &
                    implyR(1) & andL(-2) &
                      existsL(-4) /* time */ &
                      allL(time)(-1) & FOQuantifierTactics.allLs(state)(-1) &
                      DifferentialTactics.diffRefine(True)(1) &
                      Idioms.<(
                        implyL(-1) &
                        Idioms.<(
                          hideR(1) &
                          cutR(Equal(localTime, timestep))(1) &
                          Idioms.<(
                            andL(-3) & hideL(-4) & hideL(-2) & QE & done,
                            implyR(1) & eqL2R(-4)(-3) &
                            prop & done
                          ),
                          id
                        ),
                        cohideR(1) & useAt(boxTrueAxiom)(1) & done),
                    useAt(lemma, PosInExpr(1::Nil))(1) & id)
              )
          )
      )
    }

    protected def getBoundees(fml: Formula): List[Term] = fml match {
      case And(And(Less(_, t1), Less(t2, _)), ivls) if t1 == t2 =>
        t1::getBoundees(ivls)
      case And(Less(_, t1), Less(t2, _)) if t1 == t2 =>
        t1::Nil
      case _ => throw new TacticInapplicableFailure("getBoundees called on non-And")
    }

    private def instantiationForBound(prec: Int, bounds: IntervalArithmeticV2.DecimalBounds, fml: Formula) : ((Term, BigDecimal), (Term, BigDecimal)) = fml match {
      case And(LessEqual(l, t1), LessEqual(t2, u)) if t1 == t2 => {
        val ivl = IntervalArithmeticV2.eval_ivl(prec)(bounds)(t1)
        ((l, ivl._1),(u, ivl._2))
      }
      case _ => throw new TacticInapplicableFailure("instantiationForBound called on non-Bound")
    }
    private def instantiationForBounds(prec: Int, bounds: IntervalArithmeticV2.DecimalBounds, fml: Formula): List[((Term, BigDecimal), (Term, BigDecimal))] = fml match {
      case And(fml1 @ And(LessEqual(_, t1), LessEqual(t2, _)), ivls) if t1 == t2 =>
        instantiationForBound(prec, bounds, fml1) :: instantiationForBounds(prec, bounds, ivls)
      case And(LessEqual(_, t1), LessEqual(t2, _)) if t1 == t2 =>
        instantiationForBound(prec, bounds, fml)::Nil
      case _ => throw new TacticInapplicableFailure("instantiationForBounds called on non-And")
    }

    private def numericPicard(prec: Integer, boundees: IndexedSeq[Term], timebound: Term, right_bounds: List[Formula],
                              constant_errors: IndexedSeq[(BigDecimal, BigDecimal)])
                     (ivls: IndexedSeq[(BigDecimal, BigDecimal)]) : IndexedSeq[(BigDecimal, BigDecimal)] =
    {
      val lowers = lower_rembounds(timebound){i => Number(ivls(i)._1)}{i=>Number(constant_errors(i)._1)}
      val uppers = upper_rembounds(timebound){i => Number(ivls(i)._2)}{i=>Number(constant_errors(i)._2)}
      // TODO: compute bounds except lowers/uppers earlier?!
      val bounds = IntervalArithmeticV2.collect_bounds(prec, LessEqual(Number(0), localTime) :: LessEqual(localTime, timebound) :: right_bounds ++ lowers ++ uppers)
      boundees.map(IntervalArithmeticV2.eval_ivl(prec)(bounds))
    }

    def numericPicardIteration(prec: Integer, boundees: IndexedSeq[Term], timebound: Term, right_bounds: List[Formula],
                               remainder_estimation: IndexedSeq[(BigDecimal, BigDecimal)],
                               constant_errors: IndexedSeq[(BigDecimal, BigDecimal)])
    :
    Option[IndexedSeq[(BigDecimal, BigDecimal)]] =
    {
      var remainders = remainder_estimation
      var cremainders = None : Option[IndexedSeq[(BigDecimal, BigDecimal)]]
      var subset = false
      for (k <- 0 until 40) {
        val remainders0 = remainders
        val remainders1 = numericPicard(prec, boundees, timebound, right_bounds, constant_errors)(remainders0)
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

    def instantiateLemma(prec: Integer, t0: Term, timebound: Term,
                         precond: (Integer, Integer) => Term,
                         precondC: Integer => Term,
                         lowers: Integer => Term,
                         uppers: Integer => Term,
                         remainder_estimation : Integer => (BigDecimal, BigDecimal)
                        ) = {
      val subst0 = USubst(
        Seq(SubstitutionPair(time0, t0),SubstitutionPair(names.timestep, timebound))++
          (0 until dim).flatMap(i =>
            Seq(SubstitutionPair(names.precondC(i), precondC(i)),
              SubstitutionPair(names.rightL(i), lowers(i)),
              SubstitutionPair(names.rightU(i), uppers(i))
            ) ++
            (0 until dim).map(j => SubstitutionPair(names.precond(i, j), precond(i, j)))))
      val lemma1 = lemma(subst0)
      require(lemma1.conclusion.succ.length == 1)
      val (boundees, initApprox, concrete_right_bound) = lemma1.conclusion.succ(0) match {
        case Imply(And(And(_, crb), And(initApprox, fml : Forall)), _) => stripForalls(fml) match {
          case Imply(bound_fml, conclusion) => (getBoundees(conclusion), initApprox, FormulaTools.conjuncts(crb))
          case _ => throw new RuntimeException("Taylor model lemma not of expected shape (inner)")
        }
        case _ => throw new RuntimeException("Taylor model lemma not of expected shape")
      }
      val right_bounds = IntervalArithmeticV2.collect_bounds(prec, concrete_right_bound)

      // Approximate values for coefficients
      def midpoint(ivl: (BigDecimal, BigDecimal)) : BigDecimal = (ivl._1 + ivl._2)/2
      val approxCoeffs = exactCoefficients.map(_.mapValues(t => midpoint(IntervalArithmeticV2.eval_ivl(prec)(IntervalArithmeticV2.DecimalBounds())(subst0(t)))))
      val approxCoeffSubst = USubst(approxCoeffs.zipWithIndex.flatMap{ case (coeffs, i) =>
        coeffs.map{case (e, t) => SubstitutionPair(names.postCoeff(i, e), Number(t)) }
      })
      val initApproxInstantiations = instantiationForBounds(prec, right_bounds, approxCoeffSubst(initApprox))
      val initApproxSubst = USubst(initApproxInstantiations.flatMap{case ((t, x), (u, y)) => SubstitutionPair(t, Number(x))::SubstitutionPair(u, Number(y))::Nil})
      val constant_errors = initApproxInstantiations.map{case ((a, b), (c, d)) => (b, d)}
      val subst_remainders = numericPicardIteration(
        prec - 1, // TODO: sometimes the same precision yields unprovable (for IA) goals of the form number<number... perhaps something rounds differently?,
        boundees.map(approxCoeffSubst(_)).toIndexedSeq, timebound, concrete_right_bound, (0 until dim).map(remainder_estimation(_)).toIndexedSeq, constant_errors.toIndexedSeq) match {
        case None => throw new RuntimeException("Picard Iteration did not converge")
        case Some(remainders) =>
          USubst(remainders.zipWithIndex.map{case ((l, _), i) => SubstitutionPair(names.lower(i), IntervalArithmeticV2.mathematicaFriendly(l))} ++
            remainders.zipWithIndex.map{case ((_, u), i) => SubstitutionPair(names.upper(i), IntervalArithmeticV2.mathematicaFriendly(u))})
      }
      subst0 ++ subst_remainders ++ approxCoeffSubst ++ initApproxSubst
    }

    def cutTM(prec: Integer, antepos: AntePosition,
              qeTool: QETacticTool,
              remainder_estimation : IndexedSeq[(BigDecimal, BigDecimal)] = (0 until dim).map(_ => (BigDecimal(-0.001),BigDecimal(0.001))))
    : DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
      pos.checkSucc
      pos.checkTop
      seq.sub(pos) match {
        case Some(Box(ODESystem(ode1, And(LessEqual(t0, time1), LessEqual(time2, Plus(t00, timebound)))), goal))
          // TODO: more flexible domain, lookup ode?
          if ode1 == ode && time1 == time && time2 == time && t0 == t00 =>
        {
          require(seq.sub(antepos).isDefined)
          val concrete_initial_condition = seq.sub(antepos).get
          val um = UnificationMatch(And(initial_condition, right_tm_domain), concrete_initial_condition)
          val lemma2 = lemma(instantiateLemma(prec, t0, timebound,
            (i, j) => um(names.precond(i, j)),
            i => um(names.precondC(i)),
            i => um(names.rightL(i)),
            i => um(names.rightU(i)),
            i => remainder_estimation(i)
          ))
          require(lemma2.conclusion.succ.length == 1)
          val cut_fml = lemma2.conclusion.succ(0) match {
            case Imply(_, Box(_, cut_fml)) => cut_fml
            case _ => throw new RuntimeException("Instantiated Taylor model lemma not of expected shape")
          }
          debugTac("Starting to do something") &
            DC(cut_fml)(pos) &
            Idioms.<(skip,
              useAt(lemma2, PosInExpr(1 :: Nil))(1) &
                debugTac("Used Lemma") &
                andR(1) & Idioms.<(id,
                andR(1) & Idioms.<(
                  debugTac("Initial Numberic condition") &
                    SaturateTactic(andL('L)) &
                    IntervalArithmeticV2.intervalArithmeticBool(prec, qeTool)(1) &
                    done,
                  SaturateTactic(allR(1)) &
                    SaturateTactic(implyR(1)) &
                    SaturateTactic(andL('L)) &
                    debugTac("Numberic condition") &
                    IntervalArithmeticV2.intervalArithmeticBool(prec, qeTool)(1) &
                    done
                    )
                )
              )
        }
        case _ => throw new TacticInapplicableFailure("cutTM not on suitable Box(ODE)")
      }
    }
  }

}